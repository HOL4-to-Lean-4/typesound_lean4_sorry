# Proving task (clean-room benchmark)

You are an automatic prover under test. Your workspace is a Lean 4.28.0 project that holds a
Lean 4 translation of the CakeML type-soundness development (translated from HOL4). All
definitions are complete. Each theorem is stated and its proof is `sorry`. Every statement is
known to be provable with the definitions as written, using only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

Your job: replace `sorry` with real proofs for the theorems in the files you own (listed in
your assignment), as many as you can. The run measures how many theorems you prove without
help, so work until every owned theorem is proved or you have made several serious, different
attempts at each one that remains.

## Hard rules

1. Clean room. Work only from the files inside your workspace directory and
   `/home/claude/work/benchtools/`, plus your own knowledge of Lean. You may read the Lean core
   and Batteries sources under `.lake/packages/` and the toolchain directory to look up library
   lemmas. Do not read any other path on this machine (in particular nothing under
   `/home/claude/work/typesound_lean4_sorry`, `/home/claude/candle-hol4-lean4-study`,
   `/mnt/`, or the other `ws*` directories). Do not use the web, web search, GitHub, git history,
   MCP tools, browser tools, or tools that reach the user's computer. Do not look for existing
   proofs of these theorems anywhere (no HOL4 proof scripts, no other Lean proofs). The `/- HOL4: ... -/`
   comments in the Lean files show the original HOL4 statements only; those are fine to read.
2. Do not spawn subagents or delegate. You do all the proving yourself.
3. Never change an existing theorem statement, definition, datatype, instance, `open`, option,
   or the order of existing declarations. The only edit allowed to an existing declaration is
   replacing the `sorry` after its `:=` with a proof. A changed statement counts as a failure.
4. You may add new helper lemmas and helper definitions (new names) inside the files you own,
   placed before the theorem that needs them. You may also create new helper files
   `LeanTypeSound/<YourLetter>Aux*.lean` (for example `LeanTypeSound/BAux1.lean`) and import them
   from the files you own. Do not edit files you do not own, `lakefile.lean`, `lean-toolchain` or
   `LeanTypeSound.lean`.
5. Imports: Lean core (`Init`, `Std`, `Lean`) and `Batteries` only. Do not import Mathlib, Aesop or
   other packages (they are not built).
6. No `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `sorry`-hiding tricks, or
   options that skip kernel checking. A proved theorem must depend only on `propext`,
   `Classical.choice`, `Quot.sound`.
7. Theorems in files you do not own are `sorry` in your copy, and another prover is working on
   them in parallel. You may use those theorems as stated (they will be proved separately), as
   long as their file is imported (directly or transitively) by yours. Inside your own files, a
   proof may only use theorems declared earlier, as Lean requires. You may not add imports that
   create a cycle.
8. If you become convinced that a statement is false as written, do not edit it. Leave its
   `sorry`, and report it with a concrete counterexample or the precise reason.
9. Keep every file you own compiling at all times when you move on to another theorem. If a
   proof attempt does not work, restore `sorry` for that theorem before leaving it (snapshots of
   your workspace are taken automatically).

## Environment

- Put Lean on PATH first: `export PATH=$HOME/.elan/bin:$PATH`.
- Build one module: `lake build LeanTypeSound.Misc` (run from the workspace root). Whole
  project: `lake build`.
- Fast iteration: write a scratch file in `scratch/` inside your workspace that imports the
  modules you need and states a copy of the goal, then run `lake env lean scratch/T.lean`.
  Imported modules must have been built (`lake build <module>`) for this to work. Large files
  recompile slowly, so develop proofs in scratch files and paste them in when they check.
- The machine has 4 cores and 15 GB RAM shared with three other provers. Run one Lean process
  at a time, use command timeouts, and avoid tactics that blow up memory.
- Lean 4.28.0 core tactics such as `simp`, `omega`, `grind`, `decide`, `induction ... with`,
  `cases`, `rcases`, `obtain`, `fun_induction`, `split`, `simp_all`, `exact?` are available.
  Mathlib tactics (`aesop`, `linarith`, `tauto`, `ring`, ...) are not.
- Check your work: `python3 /home/claude/work/benchtools/verify.py <workspace>` builds the
  project and reports, among other things, "own proof has no sorry", "statement text changed",
  "kernel type changed" and "baseline definitions changed in kernel". The last three must stay
  empty. (Its "PROVED" count needs all dependencies proved too, so it undercounts while other
  files are still `sorry`.)

## Logging (required)

Keep `PROGRESS.tsv` in your workspace root, tab-separated: UTC time (`date -u +%FT%TZ`),
theorem name, status (`proved` / `failed` / `suspect-false`), short note (for failures: what
you tried and why it failed). Append a line when a theorem is proved and compiled in its real
file, and when you give up on one.

## Final report

When you stop, reply with a summary only: number proved out of the number you own; the
list of theorems still `sorry` with one line each on what blocked you; any statement you
believe false; helper lemmas or files added; the last `verify.py` output lines for the three
"changed" checks; the notable failure patterns you met; and a confirmation that you followed
the clean-room rules (say so plainly if you broke any).
