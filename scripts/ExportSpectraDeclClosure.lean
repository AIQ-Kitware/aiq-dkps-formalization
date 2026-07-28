/-
Transitive *declaration-level* closure of a Spectra endpoint.

  lake env lean --run scripts/ExportSpectraDeclClosure.lean <fully.qualified.name> ...

Prints the number of Spectra constants the given declarations transitively
depend on, grouped by defining module.  Used to size the remaining port in
`dev/tauceti/spectra-removal-plan.md`.

**Attribute by defining module, never by name prefix.**  Private declarations
are mangled to `_private.<module>.…`, so a `name.startsWith "Spectra."` filter
silently drops them and under-reports the closure — it reported 77 constants for
`spectralPVM` where the true figure is 99.  This is the same class of mistake as
believing the word `namespace` inside a docstring (see
`scripts/spectra_port_surface.py`).
-/
import Lean
import Lean.Util.FoldConsts
import Spectra.SpectralTheory.ResolventForm
import Spectra.SpectralTheory.Measure.PVM
open Lean

unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Spectra.SpectralTheory.ResolventForm },
                            { module := `Spectra.SpectralTheory.Measure.PVM }] {} 0
  let mods := env.header.moduleNames
  let modIdx := env.const2ModIdx
  -- attribute by DEFINING MODULE, not by name prefix: private declarations are
  -- mangled to `_private.…` and a prefix filter silently drops them.
  let modOf (n : Name) : String :=
    match modIdx[n]? with
    | some (i : ModuleIdx) => match mods[i.toNat]? with | some m => m.toString | none => ""
    | none => ""
  let isSpectraMod (m : String) : Bool := m == "Spectra" || m.startsWith "Spectra."
  let seeds : List Name := args.map (fun s => s.toName)
  let mut seen : NameSet := {}
  let mut stack : List Name := seeds
  while !stack.isEmpty do
    let n := stack.head!; stack := stack.tail!
    if seen.contains n then continue
    if !(isSpectraMod (modOf n)) then continue
    seen := seen.insert n
    match env.find? n with
    | none => pure ()
    | some info =>
      let mut used : NameSet := {}
      used := info.type.foldConsts used (fun c s => s.insert c)
      match info.value? with
      | some v => used := v.foldConsts used (fun c s => s.insert c)
      | none => pure ()
      stack := used.toList ++ stack
  let mut cnt : Std.HashMap String Nat := {}
  let mut tot := 0
  for n in seen.toList do
    tot := tot + 1
    let m := modOf n
    cnt := cnt.insert m ((cnt.getD m 0) + 1)
  IO.println s!"TOTAL {tot} Spectra constants over {cnt.size} modules"
  for (m, k) in cnt.toList do IO.println s!"{k}\t{m}"
