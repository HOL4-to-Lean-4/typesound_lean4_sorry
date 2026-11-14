# Checks

Run on 14 Nov 2026, Windows 10, Lean 4.28.0, from the repository root.

## Build

`lake build` with an empty `.lake/build` (Mathlib and Batteries sources only in
`.lake/packages`): passes, 28 jobs, 58 s on this machine.

Warnings: 269 `declaration uses 'sorry'` (one per canonical theorem) and 7 deprecation
warnings (`String.data` in `Mlstring.lean`, `String.mk` in `SemanticPrimitives.lean`),
which `typesound_lean4` has too. No other warnings, no errors.

## Content

```sh
lake env lean tools/DefSorry.lean   # writes defsorry.tsv: declarations that mention sorryAx
lake env lean tools/Types.lean      # writes types.tsv: every theorem and its type
# in ../typesound_lean4 (the proved repository):
#   lake env lean ../typesound_lean4_sorry/tools/Types.lean
python tools/check.py ../typesound_lean4
```

Output:

```
theorem declarations: 278 = 269 canonical + 9 termination lemmas (fix_clock_clock_le, lex_le_lt, lex_lt, do_log_exp, do_if_exp, list_sizeOf_append, list_sizeOf_reverse, pat_sizeOf_pos, list_sizeOf_pos)
canonical theorems with the de795c9f6 statement and proof exactly sorry: 269 of 269
sorry/admit tokens in LeanTypeSound/*.lean (comments excluded): 269
kernel declarations mentioning sorryAx: 269 (all canonical theorems: True, distinct names 269)
definition blocks differing from typesound_lean4: 0; only here: 0
definitions of typesound_lean4 not here (proof helpers): EvaluateProps.lean:timeout_res, EvaluateProps.lean:monoGoal?, EvaluateProps.lean:isStatePairTy, EvaluateProps.lean:hasClockOf, EvaluateProps.lean:stateProjs, EvaluateProps.lean:congFun, EvaluateProps.lean:congFunCont, EvaluateProps.lean:applyCong, EvaluateProps.lean:prodFstDiscr?, EvaluateProps.lean:analyseBody, EvaluateProps.lean:discrOf, Misc.lean:Sptree.entries, Tactics.lean:splitHypsPred, TypeSound.lean:decs_sound_concl, TypeSound.lean:decs_sound_motive, TypeSoundCore.lean:op_res_ok, TypeSoundCore.lean:OpOK, TypeSoundExp.lean:exp_res_ok, TypeSoundExp.lean:match_res_ok, TypeSoundExp.lean:EvalSound, TypeSoundExp.lean:MatchSound
files of typesound_lean4 left out: Tactics.lean, TypeSoundCore.lean, TypeSoundExp.lean
kernel types equal to typesound_lean4 (hygiene and matcher names normalised): 269 of 269
axiom/native_decide/implemented_by/extern: 0
problems: 0
```

What each line checks:

- **Theorems.** The only theorem declarations are the 269 canonical theorems of
  `de795c9f6` (names in `tools/baseline_theorems.json`, equal to the paper's `canon.tsv`)
  and the nine lemmas that the termination proof of the evaluator uses.
- **Statements and proofs.** Each canonical theorem's text (comments removed, whitespace
  ignored) is the `de795c9f6` statement, then `:=`, then `sorry` or `by sorry` and nothing
  else. The 269 are in the same files as in `de795c9f6`.
- **No other `sorry`.** The sources hold exactly 269 `sorry` tokens, and in the kernel the
  only declarations whose type or value mentions `sorryAx` are the 269 canonical theorems.
  So no definition, instance or termination proof is admitted.
- **Definitions.** Every definition block (def, opaque, inductive, structure, abbrev,
  instance) is textually identical to the block of that name in `typesound_lean4`
  (`store_type_extension` is in `TypeSound.lean` here, as in `de795c9f6`, and in
  `TypeSoundCore.lean` there, with the same text). The definitions of `typesound_lean4`
  that are not here are proof helpers (tactic code, proof invariants such as `EvalSound`,
  `timeout_res`, `Sptree.entries`).
- **Kernel types.** Each canonical theorem has the same elaborated type here and in
  `typesound_lean4`, after replacing hygienic name suffixes (they contain the module name,
  `TypeSound` here and `TypeSoundCore` there) and the names of auxiliary `match` functions
  (Lean reuses an equal matcher under the first declaration's name). This shows that the
  statements here are the ones `typesound_lean4` proves.
- **Trust.** No `axiom`, `native_decide`, `implemented_by` or `@[extern]` in the sources.

## Provability

`typesound_lean4` commit `8f71000` (same definitions, 269 theorems proved) passes its
own audit: all 269 proved with these statements, using only `propext`,
`Classical.choice` and `Quot.sound`, with no `sorryAx` anywhere.
