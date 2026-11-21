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

## Files here

`BRIEF.md` (the brief every prover got), `verify.py`, `Audit.lean`, `base_thms.tsv`, `base_defs.tsv`
(baseline audit), `audit_transcript.py`, `monitor.sh`, `PROGRESS_ws*.tsv` (per-theorem log written
by each prover), `agent_usage.tsv` (harness figures; its token column is not a cumulative count),
`token_usage.json`, `sorry_tokens_over_time.tsv`, `verify_report_final.txt`.
