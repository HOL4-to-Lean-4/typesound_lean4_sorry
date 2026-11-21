# CakeML type soundness in Lean 4: benchmark version (all proofs `sorry`)

> **Branch `claude/fable52-autoprove`.** This branch is not the benchmark input. It holds the output of a
> clean-room run on 21 Nov 2026 in which Claude Fable 5.2 proved all 269 theorems starting from
> commit `165e03b`. See [`fable52_run/RESULTS.md`](fable52_run/RESULTS.md). The text below describes the
> benchmark input on `main`.

Benchmark input for automatic provers. It holds the corrected Lean 4 translation
of the CakeML type soundness closure with the 269 canonical theorems stated and
every proof left as `sorry`. A prover's task is to replace the 269 `sorry`s.

Each goal is provable: the companion repository `typesound_lean4` (commit `8f71000`;
its definitions have not changed since `858e8641af324b4fe8f4164a2c63e090b47d5cf8`) has
the same definitions and proves all 269 theorems with these statements, using only
`propext`, `Classical.choice` and `Quot.sound`.

## What is here

- `LeanTypeSound/`: the 20 translated theories and `HOL4Prelude.lean`, in the file layout
  of the frozen translation `de795c9f6` (all 269 theorems in their original files and order).
- Theorem statements: textually identical to `de795c9f6`.
- Definitions, datatypes, instances and the prelude: identical to `typesound_lean4`
  `8f71000`. Compared with `de795c9f6` this means:
  - sparse trees ported from HOL4's `sptreeScript.sml` (a tree cannot hold a key twice);
  - `CARD` = length of a duplicate-free enumeration (HOL4's `CARD` on finite sets);
  - recursive definitions whose termination `de795c9f6` admitted with `sorry` now come
    with termination proofs (9 rewritten with `List.attach` or a size guard, 9 with only
    new termination annotations); `typesound_lean4` proves that the rewritten ones satisfy
    the original equations;
  - 34 inductive types also derive `ReflBEq` and `LawfulBEq`.
- No definition contains `sorry`.
- Nine lemmas stay with proofs because the termination proof of `evaluate`,
  `evaluate_match` and `evaluate_decs` uses them: `fix_clock_clock_le`, `lex_le_lt`,
  `lex_lt`, `do_log_exp`, `do_if_exp`, `list_sizeOf_append`, `list_sizeOf_reverse`,
  `pat_sizeOf_pos`, `list_sizeOf_pos` (all in `Evaluate.lean`, about clocks and `sizeOf`).
- Left out: every other lemma of `typesound_lean4` (its helper theorems, the sparse-tree
  lemmas, its tactic code, `TypeSoundCore.lean`, `TypeSoundExp.lean`, `Tactics.lean`) and
  its audit files, so that provers get no hints.
- `hol4-ultramin/`: the 20 HOL4 scripts that were translated, with CakeML's `LICENSE`.
- `tools/`: the script that built the definitions from `typesound_lean4`
  (`transplant_defs.py`) and the checks (`check.py`). They are not Lean build targets.

`CHECKS.md` has the check results.

## Build

Lean 4.28.0 (`lean-toolchain`); the lakefile requires Mathlib `v4.28.0` (the sources
import only Batteries).

```sh
lake build     # expect only "declaration uses 'sorry'" warnings, one per canonical theorem
```

## Known differences from HOL4 that remain (not fixed)

- **Word shifts.** `word_lsl`, `word_lsr`, `word_asr` on `word8`/`word64` take the shift
  amount modulo the width (Lean `UInt` shifts), where HOL4 shifts by the full amount;
  `word_asr` by 0 is also wrong.
- **`fp64_mul_add`** rounds twice; IEEE fused multiply-add rounds once.
- **Rounding modes** are ignored by the floating-point operations.
- **Finite maps** are functions `α → Option β`, so a `Finmap` need not have a finite domain.
- **`CARD` on infinite sets** is 0; HOL4 leaves it unspecified.

The 269 theorems hold for these definitions as written.

## Provenance

| What | Commit |
|---|---|
| Frozen translation (statements, file layout) | `de795c9f6d6515d6c99bdcbb0f8d32e31ee10af6` (Lee-Juntong/cakeml, `lean-translate`) |
| Definitions, prelude, termination lemmas, project files | `typesound_lean4` `8f71000` (definitions unchanged since `858e864`) |
| HOL4 sources | `hol4-ultramin/` from Lee-Juntong/cakeml `904068958d` (last changed at `eb9fbe3a5`) |

The first commit imports `de795c9f6` unchanged (with the Lean 4.28.0 project files of
`typesound_lean4`); the second applies `tools/transplant_defs.py`.
