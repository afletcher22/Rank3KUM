import Rank3KUM
import Lean.Util.FoldConsts

/-!
# Mechanical Rank3KUM dependency extractor

This file performs no mathematical interpretation. Project ownership is determined by defining-module
provenance, not by declaration namespace. Type, value, and declaration-metadata dependencies are
recorded separately; their union is used for reachability.
-/

open Lean Elab Command

namespace Rank3KUM.DependencyMap

private def projectModulePrefix := "Rank3KUM"

def constantKind : ConstantInfo → String
  | .axiomInfo _  => "axiom"
  | .defnInfo _   => "definition"
  | .thmInfo _    => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _   => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _   => "constructor"
  | .recInfo _    => "recursor"

def moduleNameFor? (env : Environment) (decl : Name) : Option Name :=
  match env.getModuleIdxFor? decl with
  | some idx => env.allImportedModuleNames[idx.toNat]?
  | none => none

def moduleStringFor (env : Environment) (decl : Name) : String :=
  match moduleNameFor? env decl with
  | some moduleName => moduleName.toString
  | none => "<current-or-unknown-module>"

def isProjectModule (moduleName : Name) : Bool :=
  let s := moduleName.toString
  s == projectModulePrefix || s.startsWith (projectModulePrefix ++ ".")

def isProjectOwned (env : Environment) (decl : Name) : Bool :=
  match moduleNameFor? env decl with
  | some moduleName => isProjectModule moduleName
  | none => false

def typeConstants (info : ConstantInfo) : List Name :=
  info.type.getUsedConstants.toList

def valueConstants (info : ConstantInfo) : List Name :=
  match info.value? (allowOpaque := true) with
  | some value => value.getUsedConstants.toList
  | none => []

/-- Dependencies represented in ConstantInfo metadata rather than in an Expr value. -/
def metadataConstants : ConstantInfo → List Name
  | .inductInfo val => val.ctors
  | .ctorInfo val => [val.name]
  | .recInfo val => val.all
  | _ => []

def dedupNames (xs : List Name) : List Name :=
  xs.eraseDups

def namesString (xs : List Name) : String :=
  String.intercalate ";" (xs.map Name.toString)

def boolString (b : Bool) : String :=
  if b then "true" else "false"

def splitProject (env : Environment) (deps : List Name) : List Name × List Name :=
  let deps := dedupNames deps
  (deps.filter (isProjectOwned env ·), deps.filter (fun n => !(isProjectOwned env n)))

run_cmd do
  let env ← getEnv
  let declarations :=
    env.constants.toList
      |>.map Prod.fst
      |>.filter (isProjectOwned env ·)

  let mut lines : Array String := #[
    "declaration\tkind\tmodule\tinternal\ttype_project_deps\tvalue_project_deps\tmetadata_project_deps\tdirect_project_deps\ttype_external_deps\tvalue_external_deps\tmetadata_external_deps\tdirect_external_deps"
  ]

  for decl in declarations do
    match env.find? decl with
    | none => throwError m!"project declaration disappeared from environment: {decl}"
    | some info =>
        let typeDeps := typeConstants info
        let valueDeps := valueConstants info
        let metadataDeps := metadataConstants info
        let allDeps := dedupNames (typeDeps ++ valueDeps ++ metadataDeps)
        let (typeProject, typeExternal) := splitProject env typeDeps
        let (valueProject, valueExternal) := splitProject env valueDeps
        let (metadataProject, metadataExternal) := splitProject env metadataDeps
        let (allProject, allExternal) := splitProject env allDeps
        let row := String.intercalate "\t" [
          decl.toString,
          constantKind info,
          moduleStringFor env decl,
          boolString decl.isInternal,
          namesString typeProject,
          namesString valueProject,
          namesString metadataProject,
          namesString allProject,
          namesString typeExternal,
          namesString valueExternal,
          namesString metadataExternal,
          namesString allExternal
        ]
        lines := lines.push row

  liftIO <| IO.FS.createDirAll "artifacts/compression"
  liftIO <| IO.FS.writeFile
    "artifacts/compression/declarations.raw.tsv"
    (String.intercalate "\n" lines.toList ++ "\n")

end Rank3KUM.DependencyMap
