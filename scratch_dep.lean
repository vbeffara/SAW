import RequestProject.SAWUmlaufSignedArea

open Lean in
run_cmd do
  let env ← Lean.getEnv
  let isProj : Name → Bool := fun n => match env.getModuleFor? n with
    | some m => (`RequestProject).isPrefixOf m
    | none => false
  -- forward DFS from the target, restricted to project declarations
  let mut deps : Std.HashMap Name (Array Name) := {}
  let mut stack := [`hex_signed_turn_eq_six_sign_shoelace]
  while !stack.isEmpty do
    let n := stack.head!; stack := stack.tail!
    if deps.contains n then continue
    let ds : Array Name :=
      match env.find? n with
      | some ci => match ci.value? with
        | some v => v.getUsedConstants.filter (fun d => isProj d || d == ``sorryAx)
        | none => #[]
      | none => #[]
    deps := deps.insert n ds
    for d in ds do
      if !deps.contains d && d != ``sorryAx then stack := d :: stack
  let mut out : Array String := #[]
  for (n, ds) in deps.toList do
    if ds.any (fun d => d == ``sorryAx) then
      let m := (env.getModuleFor? n).getD Name.anonymous
      out := out.push s!"{m} :: {n}"
  Lean.logInfo m!"live sorries: {out.qsort (· < ·)}"
