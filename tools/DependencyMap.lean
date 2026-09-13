import Rank3KUM
import Lean.Util.FoldConsts

/-!
# Mechanical Rank3KUM dependency extractor

This file intentionally performs no mathematical interpretation. It reads the elaborated Lean
environment and emits one row per imported `Rank3KUM.*` declaration, recording declaration kind,
module provenance, and constants used directly by the declaration's type and (when present) value.
A Python postprocessor computes the theorem-specific transitive closure and graph statistics.
-/

open Lean Elab Command

namespace Rank3KUM.DependencyMap

def isProjectName (n : Name) : Bool :=
  n.toString.startsWith "Rank3KUM."

def constantKind : ConstantInfo → String
  | .axiomInfo _  => "axiom"
  | .defnInfo _   => "definition"
  | .thmInfo _    => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _   => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _   => "constructor"
  | .recInfo _    => "recursor"

def usedConstants (info : ConstantInfo) : Array Name :=
  let fromType := info.type.getUsedConstants
  match info.value? (allowOpaque := true) with
  | some value => fromType ++ value.getUsedConstants
  | none => fromType

def moduleNameFor (env : Environment) (decl : Name) : String :=
  match env.getModuleIdxFor? decl with
  | some idx =>
      match env.allImportedModuleNames[idx.toNat]? with
      | some moduleName => moduleName.toString
      | none => "<unknown-module>"
  | none => "<current-module>"

def boolString (b : Bool) : String :=
  if b then "true" else "false"

run_cmd do
  let env ← getEnv
  let declarations :=
    env.constants.toList
      |>.map Prod.fst
      |>.filter isProjectName

  let mut lines : Array String :=
    #["declaration\tkind\tmodule\tinternal\tdirect_project_deps\tdirect_external_deps"]

  for decl in declarations do
    match env.find? decl with
    | none => pure ()
    | some info =>
        let deps := usedConstants info
        let projectDeps :=
          deps.toList
            |>.filter isProjectName
            |>.map (fun n => n.toString)
            |>.eraseDups
        let externalDeps :=
          deps.toList
            |>.filter (fun n => !isProjectName n)
            |>.map (fun n => n.toString)
            |>.eraseDups
        let row := String.intercalate "\t" [
          decl.toString,
          constantKind info,
          moduleNameFor env decl,
          boolString decl.isInternal,
          String.intercalate ";" projectDeps,
          String.intercalate ";" externalDeps
        ]
        lines := lines.push row

  liftIO <| IO.FS.createDirAll "artifacts/compression"
  liftIO <| IO.FS.writeFile
    "artifacts/compression/declarations.raw.tsv"
    (String.intercalate "\n" lines.toList ++ "\n")

end Rank3KUM.DependencyMap
