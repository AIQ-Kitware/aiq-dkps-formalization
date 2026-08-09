import DavisKahan.All

example : True := trivial

-- List every declaration whose type mentions one of the two `IsAcute`s.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let printed : Name := `TauCeti.IsAcute
  let gap : Name := `TauCeti.DavisKahan.IsUniformlyAcute
  let mut pOnly : Array Name := #[]
  let mut gOnly : Array Name := #[]
  let mut both : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    let t := ci.type
    let hasP := t.find? (fun e => e.isConstOf printed) |>.isSome
    let hasG := t.find? (fun e => e.isConstOf gap) |>.isSome
    if hasP && hasG then both := both.push n
    else if hasP then pOnly := pOnly.push n
    else if hasG then gOnly := gOnly.push n
  logInfo s!"PRINTED-only ({pOnly.size}):\n{String.intercalate "\n" (pOnly.qsort (·.toString < ·.toString) |>.toList.map toString)}"
  logInfo s!"GAP-only ({gOnly.size}):\n{String.intercalate "\n" (gOnly.qsort (·.toString < ·.toString) |>.toList.map toString)}"
  logInfo s!"BOTH ({both.size}):\n{String.intercalate "\n" (both.qsort (·.toString < ·.toString) |>.toList.map toString)}"

example : True := trivial
