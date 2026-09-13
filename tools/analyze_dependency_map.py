#!/usr/bin/env python3
"""Deterministically postprocess the kernel-level Rank3KUM dependency inventory.

This script intentionally performs graph analysis only. It does not assign mathematical meaning to
clusters or decide whether a declaration is redundant.
"""

from __future__ import annotations

import csv
import json
import re
from collections import Counter, defaultdict, deque
from pathlib import Path

ROOT_DECL = "Rank3KUM.rankThreeKUM"
RAW = Path("artifacts/compression/declarations.raw.tsv")
OUT = Path("artifacts/compression")


def read_records() -> dict[str, dict]:
    records: dict[str, dict] = {}
    with RAW.open(newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        for row in reader:
            name = row["declaration"]
            project_deps = sorted({x for x in row["direct_project_deps"].split(";") if x})
            external_deps = sorted({x for x in row["direct_external_deps"].split(";") if x})
            records[name] = {
                "name": name,
                "kind": row["kind"],
                "module": row["module"],
                "internal": row["internal"] == "true",
                "direct_project_deps": project_deps,
                "direct_external_deps": external_deps,
            }
    return records


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
        stack.extend(dep for dep in records[node]["direct_project_deps"] if dep in records)
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


def maximal_linear_chains(
    graph: dict[str, list[str]], reverse: dict[str, list[str]], root: str
) -> list[list[str]]:
    """Find deterministic chains whose interior nodes have fan-in = fan-out = 1."""
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
        while True:
            parents = reverse[start]
            if len(parents) != 1 or parents[0] not in linear:
                break
            start = parents[0]
        chain = [start]
        consumed.add(start)
        cur = start
        while cur in linear and len(graph[cur]) == 1:
            nxt = graph[cur][0]
            if nxt not in linear:
                break
            if nxt in consumed:
                break
            chain.append(nxt)
            consumed.add(nxt)
            cur = nxt
        if len(chain) >= 2:
            chains.append(chain)
    return sorted(chains, key=lambda xs: (-len(xs), xs))


def main() -> None:
    records = read_records()
    active = reachable(records, ROOT_DECL)
    inactive = set(records) - active
    depth = bfs_depth(records, active, ROOT_DECL)

    graph: dict[str, list[str]] = {
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
    chains = maximal_linear_chains(graph, reverse, ROOT_DECL)

    active_modules = Counter(records[node]["module"] for node in active)
    inactive_modules = Counter(records[node]["module"] for node in inactive)
    kind_counts = Counter(records[node]["kind"] for node in active)

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

    declaration_rows = []
    for name in sorted(records):
        rec = records[name]
        is_active = name in active
        declaration_rows.append(
            {
                **rec,
                "active": is_active,
                "root_depth": depth.get(name),
                "active_fan_in": len(reverse.get(name, [])) if is_active else 0,
                "active_fan_out": len(graph.get(name, [])) if is_active else 0,
                "single_use_in_active_closure": is_active and name != ROOT_DECL and len(reverse[name]) == 1,
                "linear_chain_node": is_active
                and name != ROOT_DECL
                and len(reverse[name]) == 1
                and len(graph[name]) == 1,
            }
        )

    payload = {
        "schema_version": 1,
        "root_declaration": ROOT_DECL,
        "method": {
            "dependency_edge": "constant occurs in declaration type or value, with opaque theorem values included",
            "project_filter": "declaration name starts with Rank3KUM.",
            "semantic_interpretation": False,
        },
        "summary": {
            "project_declarations_loaded": len(records),
            "active_declarations": len(active),
            "inactive_declarations": len(inactive),
            "active_declaration_edges": sum(len(v) for v in graph.values()),
            "active_modules": len(active_modules),
            "maximum_root_depth": max(depth.values(), default=0),
            "nontrivial_scc_count": len(nontrivial_sccs),
            "linear_chain_count": len(chains),
            "active_kind_counts": dict(sorted(kind_counts.items())),
        },
        "declarations": declaration_rows,
        "active_declarations": sorted(active),
        "inactive_declarations": sorted(inactive),
        "theorem_specific_definitions": sorted(
            node for node in active if records[node]["kind"] in {"definition", "opaque"}
        ),
        "nontrivial_strongly_connected_components": nontrivial_sccs,
        "linear_one_use_chains": chains,
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

    with (OUT / "proof-map.csv").open("w", newline="", encoding="utf-8") as handle:
        fields = [
            "name",
            "kind",
            "module",
            "internal",
            "active",
            "root_depth",
            "active_fan_in",
            "active_fan_out",
            "single_use_in_active_closure",
            "linear_chain_node",
            "direct_project_deps",
            "direct_external_deps",
        ]
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for row in declaration_rows:
            out = {key: row[key] for key in fields}
            out["direct_project_deps"] = ";".join(row["direct_project_deps"])
            out["direct_external_deps"] = ";".join(row["direct_external_deps"])
            writer.writerow(out)

    summary_lines = [
        "# Mechanical proof-map summary",
        "",
        f"Root declaration: `{ROOT_DECL}`",
        "",
        "This report is generated from elaborated declaration dependencies and contains no semantic labels.",
        "",
        "| Metric | Value |",
        "|---|---:|",
        f"| Loaded `Rank3KUM.*` declarations | {len(records)} |",
        f"| Active declarations in root closure | {len(active)} |",
        f"| Loaded declarations outside root closure | {len(inactive)} |",
        f"| Active project-local edges | {sum(len(v) for v in graph.values())} |",
        f"| Active modules | {len(active_modules)} |",
        f"| Maximum root depth | {max(depth.values(), default=0)} |",
        f"| Nontrivial SCCs | {len(nontrivial_sccs)} |",
        f"| Linear one-use chains | {len(chains)} |",
        "",
        "## Active declaration kinds",
        "",
        "| Kind | Count |",
        "|---|---:|",
        *[f"| {kind} | {kind_counts[kind]} |" for kind in sorted(kind_counts)],
        "",
        "## Active modules",
        "",
        "| Module | Active declarations | Loaded but inactive declarations |",
        "|---|---:|---:|",
        *[
            f"| `{module}` | {active_modules[module]} | {inactive_modules[module]} |"
            for module in sorted(active_modules)
        ],
        "",
        "## Largest linear one-use chains",
        "",
    ]
    if chains:
        for chain in chains[:20]:
            summary_lines.append(f"- {len(chain)} declarations: " + " -> ".join(f"`{x}`" for x in chain))
    else:
        summary_lines.append("No chains of length at least two were detected by the mechanical criterion.")

    summary_lines += [
        "",
        "## Notes on interpretation",
        "",
        "- `active` means reachable from the root through project-local constant dependencies.",
        "- `inactive` means loaded into the `Rank3KUM` environment but outside that closure; it does not mean redundant.",
        "- fan-in/fan-out and one-use-chain flags are graph facts, not importance judgments.",
        "- tactic-level case splits are not represented by kernel constant dependencies and are not inferred here.",
        "",
    ]
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
