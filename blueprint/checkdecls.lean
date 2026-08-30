import QuadraticIterates

/-!
# Blueprint declaration check

Checks that every Lean declaration referenced by a `\lean{...}` command in the blueprint really
exists. `blueprint/lean_decls` is written by plasTeX, so run `leanblueprint web` first; then, from
the root of the repository,

```
lake env lean blueprint/checkdecls.lean
```

which reports the missing names, if any, and fails.

This replaces `leanblueprint checkdecls`, which cannot be used here: the upstream `checkdecls`
executable imports the roots of *all* libraries of the workspace at once, and the comparator
harness (`comparator/Challenge.lean`) deliberately re-declares names that the library itself
declares, so the two cannot share an environment.
-/

open Lean Elab Command in
run_cmd do
  let path : System.FilePath := "blueprint" / "lean_decls"
  unless ← path.pathExists do
    throwError "{path} not found (run `leanblueprint web` first, from the repository root)"
  let env ← getEnv
  let mut missing : Array String := #[]
  for line in ← IO.FS.lines path do
    let name : String := line.trimAscii.toString
    unless name.isEmpty || env.contains name.toName do
      missing := missing.push name
  unless missing.isEmpty do
    throwError "declarations referenced by the blueprint but missing from the \
      environment:{indentD (m!"\n".joinSep (missing.toList.map .ofFormat))}"
  logInfo m!"all blueprint declarations exist"
