/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import Lean

/-!
# Declaration index

Dumps one JSON object per declaration of a built Lean library, so questions like "which
definitions are stubbed with `sorry`" are answered by the elaborator instead of by a regex over
source text.

Regexes get this wrong in both directions, and did: one attributed a following declaration's
`sorry` to the preceding `def`, another mis-parsed multi-line signatures. The environment knows
the declaration kind, the elaborated type and the axiom closure exactly.

Run it against whichever project owns the modules, since it needs that project's `LEAN_PATH`:

    lake env lean --run decl_index.lean <LibraryRoot> [<modulesFile>] > index.jsonl

`<LibraryRoot>` is the library's root module name (`Mathlib`, `TauCetiRoadmap`, `ForTauCeti`);
every declaration in a module under that prefix is indexed and nothing else.

`<modulesFile>` holds one module name per line, and all of them are imported. Pass it: a root
module is not required to import its own library. `TauCetiRoadmap.lean` imports 23 modules and
omits `HilbertSpaceOperatorTheory` entirely, because the lakefile globs the library in rather
than aggregating it — so importing only the root silently indexes nothing for that roadmap.
Reporting zero for an unimported module is worse than a wrong regex, and this is the guard.

Fields: `name`, `module`, `kind`, `isProp` (the declaration is itself a proof), `propValued`
(it *returns* `Prop` after its arguments — a predicate), `sorried` (its axiom closure contains
`sorryAx`) and `axioms`.
-/

open Lean Meta

namespace DeclIndex

def kindOf : ConstantInfo → String
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .axiomInfo _ => "axiom"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .recInfo _ => "rec"

def esc (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    acc ++ (match c with
      | '"' => "\\\"" | '\\' => "\\\\" | '\n' => "\\n" | '\t' => "\\t" | c => c.toString)

/-- Drop ASCII whitespace.  Written out rather than using `String.trim`, whose name has moved
between toolchains; module names contain no spaces, so removing all of them is equivalent. -/
def stripWs (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    if c == ' ' || c == '\t' || c == '\r' then acc else acc.push c

/-- Does this declaration return `Prop` once its arguments are consumed? -/
def propValued (type : Expr) : MetaM Bool :=
  forallTelescopeReducing type fun _ body => do
    let body ← whnfR body
    return body.isProp || (body.isSort && body.sortLevel!.isZero)

def emit (root : Name) : MetaM Unit := do
  let env ← getEnv
  for h : i in [0 : env.header.moduleNames.size] do
    let modName := env.header.moduleNames[i]
    -- only the library under test; its dependencies are not our business
    unless root.isPrefixOf modName do continue
    for n in env.header.moduleData[i]!.constNames do
      if n.isInternal then continue
      let some ci := env.find? n | continue
      -- one pathological declaration must not abort the whole index
      let ax ← try collectAxioms n catch _ => pure #[]
      let isP ← try isProp ci.type catch _ => pure false
      let pv ← try propValued ci.type catch _ => pure false
      -- source position, so a caller can jump straight to the declaration
      let line ← try
          match ← findDeclarationRanges? n with
          | some r => pure r.range.pos.line
          | none => pure 0
        catch _ => pure 0
      -- constants named by the type and the value: what this declaration would drag along
      let used := (ci.type.getUsedConstants ++ (ci.value?.map Expr.getUsedConstants).getD #[])
      let deps := used.toList.filter (fun d => !d.isInternal && d != n) |>.eraseDups
      let axStr := String.intercalate "," (ax.toList.map fun a => "\"" ++ esc a.toString ++ "\"")
      let depStr := String.intercalate "," (deps.map fun d => "\"" ++ esc d.toString ++ "\"")
      IO.println <| "{"
        ++ "\"name\":\"" ++ esc n.toString ++ "\","
        ++ "\"module\":\"" ++ esc modName.toString ++ "\","
        ++ "\"kind\":\"" ++ kindOf ci ++ "\","
        ++ "\"isProp\":" ++ (if isP then "true" else "false") ++ ","
        ++ "\"propValued\":" ++ (if pv then "true" else "false") ++ ","
        ++ "\"sorried\":" ++ (if ax.contains ``sorryAx then "true" else "false") ++ ","
        ++ "\"line\":" ++ toString line ++ ","
        ++ "\"axioms\":[" ++ axStr ++ "],"
        ++ "\"deps\":[" ++ depStr ++ "]"
        ++ "}"

end DeclIndex

unsafe def main (args : List String) : IO Unit := do
  let root := (args.head?.getD "Mathlib").toName
  initSearchPath (← findSysroot)
  let mods ← match args.drop 1 |>.head? with
    | none => pure #[root]
    | some f => do
        let txt ← IO.FS.readFile (System.FilePath.mk f)
        pure <| txt.splitOn "\n" |>.map DeclIndex.stripWs
          |>.filter (fun s => !s.isEmpty) |>.map String.toName |>.toArray
  let env ← importModules (mods.map fun m => { module := m }) {} (trustLevel := 1024)
  -- unbounded: `whnf` on a few Mathlib-heavy types exceeds the default budget
  let ctx : Core.Context :=
    { fileName := "<decl-index>", fileMap := default, maxHeartbeats := 0 }
  let st : Core.State := { env := env }
  discard <| ((DeclIndex.emit root).run' {} {} |>.toIO ctx st)
