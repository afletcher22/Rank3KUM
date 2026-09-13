#!/usr/bin/env python3
"""Deterministically postprocess the Rank3KUM declaration dependency inventory.

This is a graph-analysis tool, not a semantic proof classifier. The extractor records project
ownership by defining module and separates dependencies from declaration types, values, and
ConstantInfo metadata. This script validates the inventory, computes reachability/statistics, and
emits reproducibility metadata plus conservative generated-origin hints.
"""

from __future__ import annotations

import csv
import hashlib
import json
import re
import subprocess
from collections import Counter, defaultdict, deque
from pathlib import Path

ROOT_DECL = "Rank3KUM.rankThreeKUM"
IMMUTABLE_PARENT = "abced491e10f618400e1c9739d2d9503477da76f"
RAW = Path("artifacts/compression/declarations.raw.tsv")
OUT = Path("artifacts/compression")
DEP_FIELDS = (
    "type_project_deps",
    "value_project_deps",
    "metadata_project_deps",
    "direct_project_deps",
    "type_external_deps",
    "value_external_deps",
    "metadata_external_deps",
    "direct_external_deps",
)


def run_text(*cmd: str) -> str:
    return subprocess.check_output(cmd, text=True).strip()


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def split_field(value: str) -> list[str]:
    return sorted({x for x in value.split(";") if x})


def read_records() -> dict[str, dict]:
    records: dict[str, dict] = {}
    with RAW.open(newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        for row in reader:
            name = row["declaration"]
            if name in records:
                raise SystemExit(f"duplicate declaration in extracted inventory: {name}")
            rec = {
                "name": name,
                "kind": row["kind"],
                "module": row["module"],
                "internal": row["internal"] == "true",
            }
            for field in DEP_FIELDS:
                rec[field] = split_field(row[field])
            records[name] = rec
    return records


def validate_project_edges(records: dict[str, dict]) -> None:
    missing: dict[str, list[str]] = defaultdict(list)
    for name, rec in records.items():
        union = sorted(
            set(rec["type_project_deps"])
            | set(rec["value_project_deps"])
            | set(rec["metadata_project_deps"])
        )
        if union != rec["direct_project_deps"]:
            raise SystemExit(
                f"project dependency union mismatch for {name}: "
                f"recorded={rec['direct_project_deps']} recomputed={union}"
            )
        for dep in rec["direct_project_deps"]:
            if dep not in records:
                missing[dep].append(name)
    if missing:
        details = "\n".join(
            f"  {dep} referenced by {', '.join(sorted(users))}"
            for dep, users in sorted(missing.items())
        )
        raise SystemExit("project-owned dependencies missing from extracted inventory:\n" + details)


def reachable(records: dict[str, dict], root: str) -> set[str]:
    if root not in records:
        raise SystemExit(f"root declaration not found in extracted environment: {root}")
    seen: set[str] = set()
    stack = [root]
    while stack:
        node = stack.pop()
        if node in seen:
            continue
        seen.add(node)
        stack.extend(records[node]["direct_project_deps"])
    return seen


def bfs_depth(records: dict[str, dict], active: set[str], root: str) -> dict[str, int]:
    depth = {root: 0}
    queue = deque([root])
    while queue:
        node = queue.popleft()
        for dep in records[node]["direct_project_deps"]:
            if dep not in active or dep in depth:
                continue
            depth[dep] = depth[node] + 1
            queue.append(dep)
    if set(depth) != active:
        raise SystemExit("BFS did not reach every declaration in active closure")
    return depth


def strongly_connected_components(graph: dict[str, list[str]]) -> list[list[str]]:
    index = 0
    indices: dict[str, int] = {}
    lowlink: dict[str, int] = {}
    stack: list[str] = []
    on_stack: set[str] = set()
    result: list[list[str]] = []

    def visit(v: str) -> None:
        nonlocal index
        indices[v] = index
        lowlink[v] = index
        index += 1
        stack.append(v)
        on_stack.add(v)
        for w in graph[v]:
            if w not in indices:
                visit(w)
                lowlink[v] = min(lowlink[v], lowlink[w])
            elif w in on_stack:
                lowlink[v] = min(lowlink[v], indices[w])
        if lowlink[v] == indices[v]:
            component: list[str] = []
            while True:
                w = stack.pop()
                on_stack.remove(w)
                component.append(w)
                if w == v:
                    break
            result.append(sorted(component))

    for node in sorted(graph):
        if node not in indices:
            visit(node)
    return sorted(result, key=lambda xs: (-len(xs), xs))


def condensation_longest_path_edges(
    graph: dict[str, list[str]], sccs: list[list[str]], root: str
) -> int:
    component_of: dict[str, int] = {}
    for idx, component in enumerate(sccs):
        for node in component:
            component_of[node] = idx
    dag: dict[int, set[int]] = {idx: set() for idx in range(len(sccs))}
    for node, deps in graph.items():
        src = component_of[node]
        for dep in deps:
            dst = component_of[dep]
            if src != dst:
                dag[src].add(dst)

    memo: dict[int, int] = {}

    def longest(component: int) -> int:
        if component in memo:
            return memo[component]
        memo[component] = max((1 + longest(dst) for dst in dag[component]), default=0)
        return memo[component]

    return longest(component_of[root])


def maximal_linear_chains(
    graph: dict[str, list[str]], reverse: dict[str, list[str]], root: str
) -> list[list[str]]:
    """Find graph chains whose interior nodes have active fan-in = fan-out = 1."""
    linear = {
        node
        for node in graph
        if node != root and len(graph[node]) == 1 and len(reverse[node]) == 1
    }
    chains: list[list[str]] = []
    consumed: set[str] = set()
    for node in sorted(linear):
        if node in consumed:
            continue
        start = node
        seen_up: set[str] = set()
        while start not in seen_up:
            seen_up.add(start)
            parents = reverse[start]
            if len(parents) != 1 or parents[0] not in linear:
                break
            start = parents[0]
        chain = [start]
        consumed.add(start)
        cur = start
        seen_down = {start}
        while cur in linear and len(graph[cur]) == 1:
            nxt = graph[cur][0]
            if nxt not in linear or nxt in seen_down:
                break
            chain.append(nxt)
            consumed.add(nxt)
            seen_down.add(nxt)
            cur = nxt
        if len(chain) >= 2:
            chains.append(chain)
    return sorted(chains, key=lambda xs: (-len(xs), xs))


def source_imports() -> list[dict[str, str]]:
    import_re = re.compile(r"^\s*(?:public\s+)?import\s+([^\s]+)")
    edges: list[dict[str, str]] = []
    paths = [Path("Rank3KUM.lean"), *sorted(Path("Rank3KUM").rglob("*.lean"))]
    for path in paths:
        if not path.exists():
            continue
        module = ".".join(path.with_suffix("").parts)
        for line in path.read_text(encoding="utf-8").splitlines():
            match = import_re.match(line)
            if match:
                edges.append({"module": module, "imports": match.group(1)})
    return sorted(edges, key=lambda x: (x["module"], x["imports"]))


HELPER_SUFFIX = re.compile(r"^(.*)\.(match|eq|proof)_\d+$")


def generated_origin_hint(name: str, records: dict[str, dict]) -> tuple[str, str]:
    """Conservative naming/provenance hint, explicitly not an authorship classification."""
    rec = records[name]
    match = HELPER_SUFFIX.match(name)
    if match and match.group(1) in records:
        return match.group(1), f"named-{match.group(2)}-helper"

    if rec["kind"] in {"constructor", "recursor"}:
        inductives = [
            dep
            for dep in rec["metadata_project_deps"]
            if dep in records and records[dep]["kind"] == "inductive"
        ]
        if len(inductives) == 1:
            return inductives[0], rec["kind"]

    if rec["kind"] == "definition" and "." in name:
        parent = name.rsplit(".", 1)[0]
        if parent in records and records[parent]["kind"] == "inductive":
            return parent, "possible-structure-projection"

    if rec["internal"]:
        return name, "internal-unattributed"
    return name, "standalone-noninternal"


def reproducibility_metadata() -> dict:
    manifest_path = Path("lake-manifest.json")
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    packages = []
    for package in manifest.get("packages", []):
        packages.append(
            {
                "name": package.get("name"),
                "type": package.get("type"),
                "url": package.get("url"),
                "inputRev": package.get("inputRev"),
                "rev": package.get("rev"),
            }
        )
    packages.sort(key=lambda p: (p.get("name") or ""))
    return {
        "source_commit": run_text("git", "rev-parse", "HEAD"),
        "immutable_palomar_parent": IMMUTABLE_PARENT,
        "lean_toolchain": Path("lean-toolchain").read_text(encoding="utf-8").strip(),
        "lean_version": run_text("lean", "--version"),
        "lake_manifest_sha256": sha256_file(manifest_path),
        "resolved_packages": packages,
        "extractor_sha256": sha256_file(Path("tools/DependencyMap.lean")),
        "postprocessor_sha256": sha256_file(Path("tools/analyze_dependency_map.py")),
        "challenge_sha256": sha256_file(Path("Challenge.lean")),
        "solution_sha256": sha256_file(Path("Solution.lean")),
    }


def edge_set(records: dict[str, dict], active: set[str], field: str) -> set[tuple[str, str]]:
    return {
        (name, dep)
        for name in active
        for dep in records[name][field]
        if dep in active
    }


def main() -> None:
    records = read_records()
    validate_project_edges(records)
    active = reachable(records, ROOT_DECL)
    inactive = set(records) - active
    depth = bfs_depth(records, active, ROOT_DECL)

    graph = {
        node: sorted(dep for dep in records[node]["direct_project_deps"] if dep in active)
        for node in sorted(active)
    }
    reverse: dict[str, list[str]] = {node: [] for node in active}
    for node, deps in graph.items():
        for dep in deps:
            reverse[dep].append(node)
    for node in reverse:
        reverse[node].sort()

    sccs = strongly_connected_components(graph)
    nontrivial_sccs = [component for component in sccs if len(component) > 1]
    shortest_max = max(depth.values(), default=0)
    longest_condensation = condensation_longest_path_edges(graph, sccs, ROOT_DECL)
    chains = maximal_linear_chains(graph, reverse, ROOT_DECL)

    type_edges = edge_set(records, active, "type_project_deps")
    value_edges = edge_set(records, active, "value_project_deps")
    metadata_edges = edge_set(records, active, "metadata_project_deps")
    union_edges = edge_set(records, active, "direct_project_deps")

    active_modules = Counter(records[node]["module"] for node in active)
    inactive_modules = Counter(records[node]["module"] for node in inactive)
    kind_counts = Counter(records[node]["kind"] for node in active)
    internal_counts = Counter("internal" if records[node]["internal"] else "non_internal" for node in active)

    external_uses: Counter[str] = Counter()
    for node in active:
        external_uses.update(records[node]["direct_external_deps"])

    module_edges: set[tuple[str, str]] = set()
    for node, deps in graph.items():
        src = records[node]["module"]
        for dep in deps:
            dst = records[dep]["module"]
            if src != dst:
                module_edges.add((src, dst))

    imports = source_imports()
    active_module_names = set(active_modules)

    origin_rows = []
    origin_category_counts: Counter[str] = Counter()
    active_origin_groups: defaultdict[str, list[str]] = defaultdict(list)
    for name in sorted(records):
        owner, category = generated_origin_hint(name, records)
        if name in active:
            origin_category_counts[category] += 1
            active_origin_groups[owner].append(name)
        origin_rows.append(
            {
                "name": name,
                "active": name in active,
                "origin_hint": owner,
                "origin_hint_category": category,
            }
        )

    declaration_rows = []
    for name in sorted(records):
        rec = records[name]
        is_active = name in active
        owner, category = generated_origin_hint(name, records)
        declaration_rows.append(
            {
                **rec,
                "active": is_active,
                "shortest_root_distance": depth.get(name),
                "active_fan_in": len(reverse.get(name, [])) if is_active else 0,
                "active_fan_out": len(graph.get(name, [])) if is_active else 0,
                "single_incoming_edge_in_active_closure": is_active
                and name != ROOT_DECL
                and len(reverse[name]) == 1,
                "linear_chain_node": is_active
                and name != ROOT_DECL
                and len(reverse[name]) == 1
                and len(graph[name]) == 1,
                "origin_hint": owner,
                "origin_hint_category": category,
            }
        )

    payload = {
        "schema_version": 2,
        "root_declaration": ROOT_DECL,
        "method": {
            "project_ownership": "defining module is Rank3KUM or begins Rank3KUM.",
            "dependency_union": "constant occurrences in declaration type, opaque-inclusive value, or ConstantInfo inductive/constructor/recursor metadata",
            "type_value_metadata_separated": True,
            "semantic_interpretation": False,
            "internal_flag_meaning": "Lean Name.isInternal only; not an authorship/generated classification",
            "origin_hints": "conservative naming/metadata heuristic; not a compression score or authorship claim",
        },
        "reproducibility": reproducibility_metadata(),
        "summary": {
            "project_declarations_loaded": len(records),
            "active_declarations": len(active),
            "inactive_declarations": len(inactive),
            "active_union_edges": len(union_edges),
            "active_type_edges": len(type_edges),
            "active_value_edges": len(value_edges),
            "active_metadata_edges": len(metadata_edges),
            "active_modules": len(active_modules),
            "maximum_shortest_root_distance": shortest_max,
            "longest_scc_condensation_path_edges": longest_condensation,
            "nontrivial_scc_count": len(nontrivial_sccs),
            "linear_chain_count": len(chains),
            "active_kind_counts": dict(sorted(kind_counts.items())),
            "active_internal_flag_counts": dict(sorted(internal_counts.items())),
            "active_origin_hint_groups": len(active_origin_groups),
            "active_origin_hint_category_counts": dict(sorted(origin_category_counts.items())),
        },
        "declarations": declaration_rows,
        "active_declarations": sorted(active),
        "inactive_declarations": sorted(inactive),
        "definitions_in_root_closure": sorted(
            node for node in active if records[node]["kind"] in {"definition", "opaque"}
        ),
        "nontrivial_strongly_connected_components": nontrivial_sccs,
        "linear_one_incoming_edge_chains": chains,
        "active_origin_groups": [
            {"origin_hint": owner, "members": sorted(members)}
            for owner, members in sorted(active_origin_groups.items())
        ],
        "active_modules": [
            {
                "module": module,
                "active_declarations": active_modules[module],
                "inactive_declarations_loaded": inactive_modules[module],
            }
            for module in sorted(active_modules)
        ],
        "active_module_dependency_edges": [
            {"module": src, "depends_on": dst} for src, dst in sorted(module_edges)
        ],
        "source_import_edges": imports,
        "active_source_import_edges": [
            edge for edge in imports if edge["module"] in active_module_names
        ],
        "external_boundary_dependencies": [
            {"declaration": name, "active_direct_uses": external_uses[name]}
            for name in sorted(external_uses)
        ],
    }

    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "proof-map.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )

    csv_fields = [
        "name",
        "kind",
        "module",
        "internal",
        "active",
        "shortest_root_distance",
        "active_fan_in",
        "active_fan_out",
        "single_incoming_edge_in_active_closure",
        "linear_chain_node",
        "origin_hint",
        "origin_hint_category",
        *DEP_FIELDS,
    ]
    with (OUT / "proof-map.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=csv_fields)
        writer.writeheader()
        for row in declaration_rows:
            out = {key: row[key] for key in csv_fields}
            for field in DEP_FIELDS:
                out[field] = ";".join(row[field])
            writer.writerow(out)

    with (OUT / "source-aggregation-hints.csv").open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle,
            fieldnames=["name", "active", "origin_hint", "origin_hint_category"],
        )
        writer.writeheader()
        writer.writerows(origin_rows)

    summary_lines = [
        "# Mechanical proof-map summary (schema v2)",
        "",
        f"Root declaration: `{ROOT_DECL}`",
        "",
        "This report contains mechanical graph facts only. Project ownership is determined by defining-module provenance.",
        "The `internal` flag is Lean `Name.isInternal`; it is not an authorship classifier.",
        "Generated-origin hints are conservative aggregation aids, not a proof-complexity score.",
        "",
        "| Metric | Value |",
        "|---|---:|",
        f"| Project declarations loaded | {len(records)} |",
        f"| Active declarations in root closure | {len(active)} |",
        f"| Loaded declarations outside root closure | {len(inactive)} |",
        f"| Active union dependency edges | {len(union_edges)} |",
        f"| Active type edges | {len(type_edges)} |",
        f"| Active value edges | {len(value_edges)} |",
        f"| Active metadata edges | {len(metadata_edges)} |",
        f"| Active modules | {len(active_modules)} |",
        f"| Maximum shortest root distance | {shortest_max} |",
        f"| Longest SCC-condensation path | {longest_condensation} edges |",
        f"| Nontrivial SCCs | {len(nontrivial_sccs)} |",
        f"| Linear one-incoming-edge chains | {len(chains)} |",
        f"| Non-internal active names | {internal_counts['non_internal']} |",
        f"| Internal active names | {internal_counts['internal']} |",
        f"| Active origin-hint groups | {len(active_origin_groups)} |",
        "",
        "## Reproducibility",
        "",
        f"- Source commit: `{payload['reproducibility']['source_commit']}`",
        f"- Immutable Palomar parent: `{IMMUTABLE_PARENT}`",
        f"- Lean toolchain: `{payload['reproducibility']['lean_toolchain']}`",
        f"- Manifest SHA-256: `{payload['reproducibility']['lake_manifest_sha256']}`",
        f"- Extractor SHA-256: `{payload['reproducibility']['extractor_sha256']}`",
        f"- Postprocessor SHA-256: `{payload['reproducibility']['postprocessor_sha256']}`",
        "",
        "## Interpretation cautions",
        "",
        "- Active means reachable through the union of type, value, and declaration-metadata project dependencies.",
        "- Type/value/metadata edge counts overlap; their sum need not equal the union edge count.",
        "- Metadata edges include inductive-to-constructor and constructor/recursor packaging links; SCCs can therefore reflect datatype packaging rather than circular mathematical reasoning.",
        "- Maximum shortest root distance is not longest proof depth. The reported longest path is on the SCC-condensation DAG.",
        "- A single incoming edge is a graph property, not a count of source occurrences or mathematical uses.",
        "- Definitions in the root closure are not necessarily exclusive to this theorem.",
        "- Source-aggregation hints collapse only recognizable generated naming/metadata patterns and are intentionally incomplete.",
        "",
    ]

    if nontrivial_sccs:
        summary_lines += ["## Nontrivial SCCs", ""]
        for component in nontrivial_sccs:
            summary_lines.append("- " + ", ".join(f"`{x}`" for x in component))
        summary_lines.append("")

    (OUT / "proof-map-summary.md").write_text("\n".join(summary_lines), encoding="utf-8")

    with (OUT / "proof-map-active.dot").open("w", encoding="utf-8") as handle:
        handle.write("digraph Rank3KUM {\n")
        handle.write('  rankdir="LR";\n')
        for node in sorted(active):
            label = node.replace('"', '\\"')
            handle.write(f'  "{label}";\n')
        for node in sorted(graph):
            for dep in graph[node]:
                handle.write(f'  "{node}" -> "{dep}";\n')
        handle.write("}\n")


if __name__ == "__main__":
    main()
