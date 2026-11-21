# Clean-room test: Claude Fable 5.2 on the CakeML type-soundness closure

Run on 21 Nov 2026 (UTC). Result: **269 of 269 theorems proved**, checked on the merged build.

## Setup

- Input: this repository at commit `165e03b` (269 canonical theorems, every proof `sorry`).
  Lean 4.28.0, Lean core and Batteries only (Mathlib was not built).
- Prover: four Claude Fable 5.2 subagents (`claude-fable-5-2`, high effort), started together in a
  cloud container with 4 cores and 15 GB RAM. Each worked in its own copy of the repository and
  owned a set of files. A prover could use the theorems of files it did not own as stated (they
  were `sorry` in its copy). No human or other model took part in the proofs. No prover was
  resumed or given a second instruction: each ran once from the brief in `BRIEF.md`.
- Clean room: `hol4-ultramin/` (the HOL4 scripts), `README.md`, `CHECKS.md` and `tools/` were
  left out of the provers' copies. The brief forbids the proved repository `typesound_lean4`, HOL4
  proof scripts, other Lean proofs, web, git history and the user's computer. After the run, every
  tool call in the four transcripts was scanned (`audit_transcript.py`): no call refers to a path
  outside the prover's own workspace and the benchmark tools, and no web or git call occurs.
  Prover D reported that one `ps` listing showed another prover's command line with the theorem
  name `do_app_cases`; it opened no file there.
- The model's training data (cutoff June 2026) can include the public CakeML HOL4 sources. The
  proved Lean repository was published in November 2026.

## Result

| Prover | Files | Theorems | Proved | Duration | Tool calls |
|---|---|---|---|---|---|
| A | Misc, Mlstring, NamespaceProps, Evaluate, EvaluateProps, SemanticPrimitivesProps | 108 | 108 | 47 min | 111 |
| B | TypeSysProps | 92 | 92 | 30 min | 67 |
| C | Weakening | 25 | 25 | 5 min | 26 |
| D | TypeSound | 44 | 44 | 62 min | 146 |
| Total | | 269 | 269 | 62 min wall time, 144 min summed | 350 |

Start 03:01:26 UTC, last prover finished 04:03:44 UTC.

Remaining `sorry` tokens over time (`sorry_tokens_over_time.tsv`):

| UTC | A | B | C | D | Total |
|---|---|---|---|---|---|
| 03:00 | 108 | 92 | 25 | 44 | 269 |
| 03:10 | 38 | 38 | 0 | 44 | 120 |
| 03:20 | 38 | 23 | 0 | 44 | 105 |
| 03:30 | 22 | 0 | 0 | 6 | 28 |
| 03:40 | 2 | 0 | 0 | 5 | 7 |
| 03:50 | 0 | 0 | 0 | 4 | 4 |
| 04:02 | 0 | 0 | 0 | 0 | 0 |

(Prover D developed its proofs in helper files first, so its count drops late.)

## Token usage (summed from the API usage fields of the four transcripts, `token_usage.json`)

| Prover | API responses | Output | Cache write | Cache read | Uncached input |
|---|---|---|---|---|---|
| A | 106 | 204,816 | 502,605 | 20,931,743 | 212 |
| B | 63 | 173,652 | 379,107 | 15,586,368 | 126 |
| C | 23 | 31,669 | 187,500 | 3,104,454 | 46 |
| D | 142 | 298,375 | 981,872 | 30,969,520 | 284 |
| Total | 334 | 708,512 | 2,051,084 | 70,592,085 | 668 |

The orchestrating session's own tokens (setup, merge, verification) are not included.

## Verification (`verify.py`, `Audit.lean`, report in `verify_report_final.txt`)

On the merged files, after deleting the project's build directory:

- `lake build` succeeds; the log has no `sorry` warning (`verify_build_final.log`).
- All 269 canonical theorems: source statement text equal to `tools/baseline_theorems.json`,
  kernel type equal to the all-sorry baseline, in their original files, axioms within
  `propext`, `Classical.choice`, `Quot.sound` (transitively, so no `sorryAx`).
- Every baseline constant that is not a theorem (2,353 definitions, constructors, recursors, ...)
  has the same kernel type and value hash as in the baseline.
- No `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe`; no `sorry` or `admit` token
  in any file. A text diff of each baseline file shows that the only removed lines are the
  lines that held `sorry`.
- Two `set_option maxHeartbeats ... in` lines were added on helper theorems (`sp_do_app_cases_aux`,
  `ep_do_app_facts`).

## What the provers added

- 9,550 lines: 18,577 lines in `LeanTypeSound/` against 9,027 in the baseline.
- New helper files: `BAux1`, `BAux2` (induction principles for the nested and mutual types, 561
  lines), `DAux1` to `DAux4` (4,374 lines: canonical forms and store lemmas, per-operator lemmas for
  `op_type_sound`, per-construct lemmas and strong induction on clock and size for
  `exp_type_sound`, per-declaration lemmas for `decs_type_sound`). `TypeSound.lean` fills each
  theorem with `DAux.<name>'` and adds four imports.
- Helper lemmas inside the owned files (prefixes `misc_`, `mlstring_`, `ns_`, `sp_`, `ev_`, `ep_`,
  `icm_`, `B_`, and unprefixed ones in `Weakening.lean`).
- Three files had been rewritten with LF line endings by the provers; they were converted back to
  CRLF before the final verification.

## Failures and friction

No theorem was left unproved, none was reported as false, and no statement was changed.
`PROGRESS_ws*.tsv` hold 269 `proved` lines and no `failed` line. Patterns the provers reported:

- `induction` does not work on the mutual relations `type_p`, `type_e`, `type_d`; the provers
  wrote combined induction principles from the recursors or used mutual structural recursion.
- `cases ... with` and `rename_i` name slots on indexed families differ from the constructor
  declaration, which cost retries.
- The same `match` elaborated in two declarations gives different matcher constants, so goals
  that look equal need `rfl` or `split` in place of rewriting.
- `set_option maxHeartbeats` at tactic level does not lift the limit for `do_app_cases`; it has
  to be at command level on a helper theorem.
- `rw` with an iff picked the wrong occurrence (`tveLookup_inc_none`); `simp_all` rewrote
  `fix_clock` goals before the intended lemma fired.
- One helper (`DAux.extend_dec_env_assoc`) had the short name of a canonical theorem and tripped
  the statement check; prover D renamed it.
- `List.perm_ext_iff_of_nodup` was not available without a new import; prover A proved a
  replacement.

## Check against the HOL4 sources (done after the run, by the orchestrating session)

Question: do the friction items mean a theorem was changed or the translation is wrong? Answer:
no theorem was changed, and the friction items are properties of Lean 4, with one observation
about the translation (item 5).

1. **Statements.** All 269 keep the baseline source text and kernel type (see Verification). The
   top-level statements `semantics_type_sound` and `exp_type_sound` were also read side by side
   with `hol4-ultramin/typeSoundScript.sml` and match clause for clause.
2. **Induction on `type_p`, `type_e`, `type_d`.** These are mutual inductive relations in HOL4 too
   (`type_p`/`type_ps`, `type_e`/`type_es`/`type_funs`, `type_d`/`type_ds`). HOL4's `Inductive`
   generates one combined principle per group (`type_p_ind`, `type_e_ind`, `type_d_ind`), and the
   HOL4 scripts use them 14 times. Lean 4's `induction` tactic does not accept mutual inductive
   types, so the provers stated the same combined principles (`BAux.type_p_ind` and so on) and
   proved them from Lean's generated recursors (`type_p.rec`, `type_ps.rec`). They are theorems
   checked by the kernel, so they cannot add an assumption.
3. **`cases ... with` name slots, `rfl` in place of `rw` for `match` terms.** Both concern how
   Lean names constructor arguments and compiles `match` into auxiliary functions. Neither
   touches a statement or a definition.
4. **`maxHeartbeats` for `do_app_cases`.** In HOL4 this theorem is computed (`SIMP_CONV` over
   `do_app_def`), so the script has no statement text. The Lean statement is the written-out
   case expansion: 297 lines, one `↔` with 64 disjuncts. Proving it means case analysis over all
   of `do_app`, which exceeds Lean's default step budget. Because it is an `↔` proved from the
   Lean `do_app`, it characterises the Lean `do_app` exactly; it can differ from HOL4's computed
   theorem only where the Lean `do_app` differs from HOL4's (README, known differences).
5. **Proof-size comparison** (`compare_hol.py`): 268 of 269 theorems match a HOL4 theorem by name
   (`type_v_exn` is a `val` in HOL4). HOL4 proofs total 3,925 lines. Theorems with a long HOL4
   proof and a short Lean proof all go through helper lemmas, except one:
   `check_dup_ctors_thm` is `rfl` in Lean, 11 lines in HOL4. HOL4 defines `check_dup_ctors` with
   `FOLDR (λ(n,ts) x2. if T then n::x2 else x2) [] condefs`; the Lean definition already says
   `condefs.map fun (n, _) => n`. The two are equal, so the translation is correct, but it
   simplified the definition and the theorem became trivial.
6. **`evaluate_length`** ends in `→ True` for `evaluate_decs`. HOL4 has `⇒ T` there too.
7. **Helper definitions.** The provers added 17 definitions (`ste`, `bindR`, `op_res`, `res1`,
   `R1`, `envOK`, `M1`, `M3`, `dres`, `DR`, `DS`, `misc_keys`, six `icm_app*`), four tactic macros,
   one `attribute [local simp]` line and two `maxHeartbeats` lines. All have new names and state
   proof invariants. No canonical statement mentions them (kernel types equal the baseline).
   `DAux.ste` repeats `store_type_extension` word for word, because that definition lives in
   `TypeSound.lean`, which the helper files cannot import.
8. **Induction scheme of the main theorems.** HOL4 proves `exp_type_sound` with `evaluate_ind`
   and `decs_type_sound` with `evaluate_decs_ind`. The Lean proofs use strong induction on the
   clock and `sizeOf` (the termination measure of `evaluate`) and mutual recursion over
   `type_d`/`type_ds`. `is_clock_io_mono_evaluate` uses `evaluate.mutual_induct`, Lean's
   counterpart of `full_evaluate_ind`.

Not covered by this check: a fresh statement-by-statement comparison of all 269 Lean statements
and of the definitions with HOL4. That is the translation validation done before this run.

## Files here

`BRIEF.md` (the brief every prover got), `verify.py`, `Audit.lean`, `base_thms.tsv`, `base_defs.tsv`
(baseline audit), `audit_transcript.py`, `monitor.sh`, `PROGRESS_ws*.tsv` (per-theorem log written
by each prover), `agent_usage.tsv` (harness figures; its token column is not a cumulative count),
`token_usage.json`, `sorry_tokens_over_time.tsv`, `verify_report_final.txt`, `compare_hol.py`.
