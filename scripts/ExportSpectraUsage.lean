/-
Exact Spectra-dependency census for the DKPS production build.

For every declaration whose *defining module* is a DKPS production module,
report the `Spectra.*` constants appearing in its type or value, as JSONL:

  {"consumer": "...", "consumerModule": "...", "spectra": ["...", ...]}

This is the measurement half of the Spectra -> Tau Ceti port ledger
(`dev/tauceti/spectra-to-tauceti-port-ledger.md`).  It reads the *compiled*
environment rather than import lines or textual name matches, so the reported
surface is exactly what the kernel sees: a textual scan cannot distinguish
`Spectra.Operator.SymmetricOperator.DomainConditions.A` from a local binder
named `A`, and an import-line count cannot tell a load-bearing import from a
transitively-inherited one.

`DavisKahan.Experimental` is excluded: it sits outside `defaultTargets`, so it
is not part of the surface that has to be repointed before Spectra can leave
the normal build.

Run (after a successful `lake build`):

  lake env lean --run scripts/ExportSpectraUsage.lean > build/spectra_direct_uses.jsonl
  python3 scripts/spectra_port_surface.py build/spectra_direct_uses.jsonl

The Python half aggregates this JSONL against `vendor/Spectra` and the pinned
`external/TauCeti` checkout and rewrites `dev/tauceti/spectra-port-surface.json`.
-/
import Lean
import Lean.Util.FoldConsts

import DavisKahan.All
import ForTauCeti
import ForMathlib
import Acharyya2024
import Acharyya2025
import DkpsQuench2026
import Helm2025

open Lean

/-- Module roots that make up the DKPS production build. -/
def projectModuleRoots : List String :=
  ["DavisKahan", "ForTauCeti", "ForMathlib", "Acharyya2024", "Acharyya2025",
   "DkpsQuench2026", "Helm2025", "FinishTanTwoTheta"]

/-- `DavisKahan.Experimental` is outside `defaultTargets`; keep it out of the census. -/
def isProductionModule (m : String) : Bool :=
  if m.startsWith "DavisKahan.Experimental" then false
  else projectModuleRoots.any (fun r => m == r || m.startsWith (r ++ "."))

def isSpectra (n : Name) : Bool :=
  let s := n.toString
  s == "Spectra" || s.startsWith "Spectra."

def esc (s : String) : String :=
  s.foldl (fun acc c =>
    if c == '"' then acc ++ "\\\"" else if c == '\\' then acc ++ "\\\\" else acc.push c) ""

unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules
    (#[`DavisKahan.All, `ForTauCeti, `ForMathlib, `Acharyya2024, `Acharyya2025,
       `DkpsQuench2026, `Helm2025].map (fun m => { module := m })) {} 0
  let mods := env.header.moduleNames
  let modIdx := env.const2ModIdx
  let mut emitted := 0
  for (name, info) in env.constants.toList do
    if name.isInternal then continue
    let modName :=
      match modIdx[name]? with
      | some (i : ModuleIdx) =>
        match mods[i.toNat]? with
        | some m => m.toString
        | none => ""
      | none => ""
    if !isProductionModule modName then continue
    let mut used : NameSet := {}
    used := info.type.foldConsts used (fun c s => if isSpectra c then s.insert c else s)
    match info.value? with
    | some v => used := v.foldConsts used (fun c s => if isSpectra c then s.insert c else s)
    | none => pure ()
    if used.isEmpty then continue
    emitted := emitted + 1
    let names := used.toList.map (fun n => "\"" ++ esc n.toString ++ "\"")
    IO.println <|
      "{\"consumer\": \"" ++ esc name.toString ++ "\", \"consumerModule\": \"" ++
      esc modName ++ "\", \"spectra\": [" ++ String.intercalate ", " names ++ "]}"
  IO.eprintln s!"emitted {emitted} consumer declarations"
