/-
  Translation of evaluatePropsScript.sml
  Properties of the operational semantics.
-/
import LeanTypeSound.HOL4Prelude
import LeanTypeSound.Ast
import LeanTypeSound.Evaluate
import LeanTypeSound.Namespace
import LeanTypeSound.NamespaceProps
import LeanTypeSound.SemanticPrimitives
import LeanTypeSound.SemanticPrimitivesProps

open HOL4

-- ============================================================
-- Definitions
-- ============================================================

/- HOL4:
Definition call_FFI_rel_def:
  call_FFI_rel s1 s2 <=> ?n conf bytes t. call_FFI s1 n conf bytes = FFI_return s2 t
End
-/
def call_FFI_rel {ffi : Type} (s1 s2 : ffi_state ffi) : Prop :=
  ∃ n conf bytes t, call_FFI s1 n conf bytes = .FFI_return s2 t

/- HOL4:
Definition dest_IO_event_def[simp]:
  dest_IO_event (IO_event s c b) = (s,c,b)
End
-/
def dest_IO_event : io_event → ffiname × List word8 × List (word8 × word8)
  | .IO_event s c b => (s, c, b)

/- HOL4:
Definition io_events_mono_def:
  io_events_mono s1 s2 ⇔
    s1.io_events ≼ s2.io_events ∧
    (s2.io_events = s1.io_events ⇒ s2 = s1)
End
-/
def io_events_mono {ffi : Type} (s1 s2 : ffi_state ffi) : Prop :=
  s1.io_events.isPrefixOf s2.io_events ∧
  (s2.io_events = s1.io_events → s2 = s1)

/- HOL4:
Definition is_clock_io_mono_def:
  is_clock_io_mono f s = (case f s of (s', r) =>
        io_events_mono s.ffi s'.ffi
        /\ s'.clock <= s.clock
        /\ s.next_type_stamp <= s'.next_type_stamp
        /\ s.next_exn_stamp <= s'.next_exn_stamp
        /\ LENGTH s.refs <= LENGTH s'.refs
        /\ (!clk. case f (s with clock := clk) of (s'', r') =>
            (~ (r' = Rerr (Rabort Rtimeout_error))
                ==> ~ (r = Rerr (Rabort Rtimeout_error))
                ==> r' = r
                    /\ s'' = (s' with clock := clk - (s.clock - s'.clock)))
            /\ (~ (r = Rerr (Rabort Rtimeout_error))
                ==> (clk >= s.clock - s'.clock
                    <=> ~ (r' = Rerr (Rabort Rtimeout_error))))
            /\ (~ (r' = Rerr (Rabort Rtimeout_error))
                ==> clk <= s.clock
                ==> ~ (r = Rerr (Rabort Rtimeout_error)))
            /\ (clk <= s.clock ==> io_events_mono s''.ffi s'.ffi)
        ))
End
-/
def is_clock_io_mono {ffi α β : Type} (f : cml_state ffi → cml_state ffi × result α β)
    (s : cml_state ffi) : Prop :=
  let (s', r) := f s
  io_events_mono s.ffi s'.ffi ∧
  s'.clock ≤ s.clock ∧
  s.next_type_stamp ≤ s'.next_type_stamp ∧
  s.next_exn_stamp ≤ s'.next_exn_stamp ∧
  s.refs.length ≤ s'.refs.length ∧
  ∀ (clk : Nat),
    let (s'', r') := f ({ s with clock := clk })
    (¬ (r' = .Rerr (.Rabort .Rtimeout_error)) →
      ¬ (r = .Rerr (.Rabort .Rtimeout_error)) →
      r' = r ∧ s'' = { s' with clock := clk - (s.clock - s'.clock) }) ∧
    (¬ (r = .Rerr (.Rabort .Rtimeout_error)) →
      (clk ≥ s.clock - s'.clock ↔ ¬ (r' = .Rerr (.Rabort .Rtimeout_error)))) ∧
    (¬ (r' = .Rerr (.Rabort .Rtimeout_error)) →
      clk ≤ s.clock → ¬ (r = .Rerr (.Rabort .Rtimeout_error))) ∧
    (clk ≤ s.clock → io_events_mono s''.ffi s'.ffi)

/- HOL4:
Definition adj_clock_def:
  adj_clock inc dec s = (s with clock := ((s.clock + inc) - dec))
End
-/
def adj_clock {ffi : Type} (inc dec_ : Nat) (s : cml_state ffi) : cml_state ffi :=
  { s with clock := s.clock + inc - dec_ }

-- ============================================================
-- Theorem stubs
-- ============================================================

theorem ep_icm_def {ffi α β : Type} (f : cml_state ffi → cml_state ffi × result α β)
    (s : cml_state ffi) :
    is_clock_io_mono f s ↔
    (io_events_mono s.ffi (f s).1.ffi ∧
     (f s).1.clock ≤ s.clock ∧
     s.next_type_stamp ≤ (f s).1.next_type_stamp ∧
     s.next_exn_stamp ≤ (f s).1.next_exn_stamp ∧
     s.refs.length ≤ (f s).1.refs.length ∧
     ∀ (clk : Nat),
      (¬ ((f { s with clock := clk }).2 = .Rerr (.Rabort .Rtimeout_error)) →
        ¬ ((f s).2 = .Rerr (.Rabort .Rtimeout_error)) →
        (f { s with clock := clk }).2 = (f s).2 ∧
        (f { s with clock := clk }).1 = { (f s).1 with clock := clk - (s.clock - (f s).1.clock) }) ∧
      (¬ ((f s).2 = .Rerr (.Rabort .Rtimeout_error)) →
        (clk ≥ s.clock - (f s).1.clock ↔ ¬ ((f { s with clock := clk }).2 = .Rerr (.Rabort .Rtimeout_error)))) ∧
      (¬ ((f { s with clock := clk }).2 = .Rerr (.Rabort .Rtimeout_error)) →
        clk ≤ s.clock → ¬ ((f s).2 = .Rerr (.Rabort .Rtimeout_error))) ∧
      (clk ≤ s.clock → io_events_mono (f { s with clock := clk }).1.ffi (f s).1.ffi)) := Iff.rfl

theorem ep_prefix_iff {ffi : Type} (s1 s2 : ffi_state ffi) :
    io_events_mono s1 s2 ↔ (s1.io_events <+: s2.io_events ∧ (s2.io_events = s1.io_events → s2 = s1)) := by
  unfold io_events_mono
  rw [List.isPrefixOf_iff_prefix]

/- HOL4: Theorem io_events_mono_trans
   io_events_mono ffi1 ffi2 ∧ io_events_mono ffi2 ffi3 ⇒
   io_events_mono ffi1 ffi3
-/
theorem io_events_mono_trans {ffi : Type}
    {ffi1 ffi2 ffi3 : ffi_state ffi} :
    io_events_mono ffi1 ffi2 ∧ io_events_mono ffi2 ffi3 →
    io_events_mono ffi1 ffi3 := by
  simp only [ep_prefix_iff]
  rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  refine ⟨h1.trans h3, fun h => ?_⟩
  have e21 : ffi2.io_events = ffi1.io_events := by
    obtain ⟨t1, ht1⟩ := h1
    obtain ⟨t2, ht2⟩ := h3
    rw [h, ← ht1, List.append_assoc] at ht2
    have := congrArg List.length ht2
    simp at this
    have ht1' : t1 = [] := by cases t1 <;> simp_all
    rw [← ht1, ht1']; simp
  have e2 := h2 e21
  subst e2
  exact h4 h
theorem ep_io_events_mono_refl {ffi : Type}
    (s : ffi_state ffi) :
    io_events_mono s s := by
  rw [ep_prefix_iff]; exact ⟨List.prefix_refl _, fun _ => rfl⟩

theorem ep_call_FFI_mono {ffi : Type} {s1 s2 : ffi_state ffi} (h : call_FFI_rel s1 s2) :
    io_events_mono s1 s2 := by
  obtain ⟨n, conf, bytes, t, h⟩ := h
  unfold call_FFI at h
  split at h
  · split at h
    · split at h
      · injection h with h1 h2
        subst h1
        rw [ep_prefix_iff]
        refine ⟨List.prefix_append _ _, fun h => ?_⟩
        have := congrArg List.length h
        simp at this
      · cases h
    · cases h
  · injection h with h1 h2
    subst h1
    exact ep_io_events_mono_refl _

/- HOL4: Theorem call_FFI_rel_io_events_mono
   ∀s1 s2. RTC call_FFI_rel s1 s2 ⇒ io_events_mono s1 s2
-/
theorem call_FFI_rel_io_events_mono {ffi : Type}
    {s1 s2 : ffi_state ffi} :
    RTC call_FFI_rel s1 s2 → io_events_mono s1 s2 := by
  intro h
  induction h with
  | refl x => exact ep_io_events_mono_refl x
  | step x y z hxy _ ih => exact io_events_mono_trans ⟨ep_call_FFI_mono hxy, ih⟩
/- HOL4: Theorem io_events_mono_refl[simp]
   io_events_mono ffi ffi
-/
theorem io_events_mono_refl {ffi : Type}
    (s : ffi_state ffi) :
    io_events_mono s s := ep_io_events_mono_refl s
theorem ep_store_assign_length {α : Type} {n : Nat} {x : store_v α} {s s' : List (store_v α)}
    (h : store_assign n x s = some s') : s'.length = s.length := by
  unfold store_assign at h
  split at h
  · injection h with h; subst h; simp [LUPDATE]
  · cases h

theorem ep_store_alloc_length {α : Type} {x : store_v α} {s s' : List (store_v α)} {n : Nat}
    (h : store_alloc x s = (s', n)) : s'.length = s.length + 1 := by
  unfold store_alloc at h
  injection h with h1 h2; subst h1; simp

theorem ep_thunk_op {ffi : Type} {s : store v} {t : ffi_state ffi} {th_op : thunk_op} {vs : List v}
    {s' : store v} {t' : ffi_state ffi} {res : result v v}
    (h : thunk_op_fun (s, t) th_op vs = some ((s', t'), res)) :
    t' = t ∧ s.length ≤ s'.length := by
  unfold thunk_op_fun at h
  split at h
  · simp only [store_alloc, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, -⟩ := h
    simp
  · split at h
    · rename_i heq
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, -⟩ := h
      exact ⟨rfl, Nat.le_of_eq (ep_store_assign_length heq).symm⟩
    · cases h
  · cases h

set_option maxHeartbeats 1000000 in

theorem ep_do_app_facts {ffi : Type}
    {r : store v} {s : ffi_state ffi} {op : op} {vs : List v}
    {r' : store v} {s' : ffi_state ffi} {res : result v v} :
    do_app (r, s) op vs = some ((r', s'), res) →
    (s' = s ∨ call_FFI_rel s s') ∧ r.length ≤ r'.length := by
  intro h
  rw [do_app_cases] at h
  revert h
  simp only [or_imp, forall_exists_index, and_imp]
  repeat' apply And.intro
  all_goals (
    intros
    first
      | (rename_i h1 h2
         have e := ep_thunk_op h2
         exact ⟨Or.inl e.1, e.2⟩)
      | (rename_i h1 h2
         injection h1 with h3 h4
         subst h3 h4
         refine ⟨by first | exact Or.inl rfl | exact Or.inr ⟨_, _, _, _, ‹_›⟩, ?_⟩
         first
           | exact Nat.le_refl _
           | exact Nat.le_of_eq (ep_store_assign_length ‹_›).symm
           | (have := ep_store_alloc_length ‹_›; omega)))

/- HOL4: Theorem do_app_call_FFI_rel
   do_app (r,ffi) op vs = SOME ((r',ffi'),res) ⇒
   call_FFI_rel^* ffi ffi'
-/
theorem do_app_call_FFI_rel {ffi : Type}
    {r : store v} {s : ffi_state ffi} {op : op} {vs : List v}
    {r' : store v} {s' : ffi_state ffi} {res : result v v} :
    do_app (r, s) op vs = some ((r', s'), res) →
    RTC call_FFI_rel s s' := by
  intro h
  rcases (ep_do_app_facts h).1 with rfl | h1
  · exact RTC.refl _
  · exact RTC.step _ _ _ h1 (RTC.refl _)
/- HOL4: Theorem do_app_io_events_mono
   do_app (r,ffi) op vs = SOME ((r',ffi'),res) ⇒ io_events_mono ffi ffi'
-/
theorem do_app_io_events_mono {ffi : Type}
    {r : store v} {s : ffi_state ffi} {op : op} {vs : List v}
    {r' : store v} {s' : ffi_state ffi} {res : result v v} :
    do_app (r, s) op vs = some ((r', s'), res) →
    io_events_mono s s' := fun h => call_FFI_rel_io_events_mono (do_app_call_FFI_rel h)
/- HOL4: Theorem is_clock_io_mono_cong
   s = t ==>
   (!s. s.eval_state = t.eval_state /\ s.refs = t.refs /\ s.ffi = t.ffi ==>
     f s = g s) ==>
   (is_clock_io_mono f s <=> is_clock_io_mono g t)
-/
theorem is_clock_io_mono_cong {ffi α β : Type}
    {f g : cml_state ffi → cml_state ffi × result α β}
    {s t : cml_state ffi} :
    s = t →
    (∀ s', s'.eval_state_field = t.eval_state_field ∧ s'.refs = t.refs ∧ s'.ffi = t.ffi →
      f s' = g s') →
    (is_clock_io_mono f s ↔ is_clock_io_mono g t) := by
  rintro rfl h
  have h1 : f s = g s := h s ⟨rfl, rfl, rfl⟩
  have h2 : ∀ clk, f { s with clock := clk } = g { s with clock := clk } :=
    fun clk => h _ ⟨rfl, rfl, rfl⟩
  simp only [ep_icm_def, h1, h2]
/- HOL4: Theorem is_clock_io_mono_return
   is_clock_io_mono (\s. (s, Rval r)) s
-/
theorem is_clock_io_mono_return {ffi α β : Type}
    (r : α) (s : cml_state ffi) :
    is_clock_io_mono (fun s => (s, @result.Rval α β r)) s := by
  rw [ep_icm_def]
  simp [io_events_mono_refl]
/- HOL4: Theorem is_clock_io_mono_err
   is_clock_io_mono (\s. (s, Rerr r)) s
-/
theorem is_clock_io_mono_err {ffi α β : Type}
    (r : error_result β) (s : cml_state ffi) :
    is_clock_io_mono (fun s => (s, @result.Rerr α β r)) s := by
  rw [ep_icm_def]
  simp [io_events_mono_refl]
  intro _ h _; exact h
/- HOL4: Theorem pair_CASE_eq_forall
   (case x of (a, b) => P a b) = (!a b. x = (a, b) ==> P a b)
-/
theorem pair_CASE_eq_forall {α β : Type} {P : α → β → Prop} {x : α × β} :
    (match x with | (a, b) => P a b) = (∀ a b, x = (a, b) → P a b) := by
  obtain ⟨a, b⟩ := x
  apply propext
  constructor
  · intro h a' b' e; injection e with e1 e2; subst e1 e2; exact h
  · intro h; exact h a b rfl
/- HOL4: Theorem is_clock_io_mono_bind
   is_clock_io_mono f s /\ (!s' r. f s = (s', r)
        ==> is_clock_io_mono (g r) s')
    /\ (!s'. g (Rerr (Rabort Rtimeout_error)) s'
        = (s', Rerr (Rabort Rtimeout_error)))
    ==> is_clock_io_mono (\s. case f s of (s', r) => g r s') s
-/
theorem is_clock_io_mono_bind {ffi α β γ δ : Type}
    {f : cml_state ffi → cml_state ffi × result α β}
    {g : result α β → cml_state ffi → cml_state ffi × result γ δ}
    {s : cml_state ffi} :
    is_clock_io_mono f s ∧
    (∀ s' r, f s = (s', r) → is_clock_io_mono (g r) s') ∧
    (∀ s', g (.Rerr (.Rabort .Rtimeout_error)) s' =
      (s', .Rerr (.Rabort .Rtimeout_error))) →
    is_clock_io_mono (fun s => match f s with | (s', r) => g r s') s := by
  rintro ⟨hf, hg, ht⟩
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := (ep_icm_def f s).mp hf
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := (ep_icm_def _ _).mp (hg (f s).1 (f s).2 rfl)
  show is_clock_io_mono (fun s => g (f s).2 (f s).1) s
  rw [ep_icm_def]
  refine ⟨io_events_mono_trans ⟨f1, g1⟩, Nat.le_trans g2 f2, Nat.le_trans f3 g3, Nat.le_trans f4 g4,
    Nat.le_trans f5 g5, fun clk => ?_⟩
  obtain ⟨F1, F2, F3, F4⟩ := f6 clk
  simp only
  by_cases hT1 : (f s).2 = .Rerr (.Rabort .Rtimeout_error)
  · have e : g (f s).2 (f s).1 = ((f s).1, .Rerr (.Rabort .Rtimeout_error)) := by rw [hT1]; exact ht _
    refine ⟨fun _ h => absurd (by rw [e]) h, fun h => absurd (by rw [e]) h, fun h3 hc => ?_, fun hc => ?_⟩
    · by_cases hT1c : (f { s with clock := clk }).2 = .Rerr (.Rabort .Rtimeout_error)
      · exact absurd (by rw [hT1c, ht]) h3
      · exact absurd hT1 (F3 hT1c hc)
    · by_cases hT1c : (f { s with clock := clk }).2 = .Rerr (.Rabort .Rtimeout_error)
      · rw [hT1c, ht, e]; exact F4 hc
      · exact absurd hT1 (F3 hT1c hc)
  · by_cases hT1c : (f { s with clock := clk }).2 = .Rerr (.Rabort .Rtimeout_error)
    · have hlt : ¬ (clk ≥ s.clock - (f s).1.clock) := fun h => (F2 hT1).mp h hT1c
      refine ⟨fun h => absurd (by rw [hT1c, ht]) h, fun _ => ?_, fun h => absurd (by rw [hT1c, ht]) h, fun hc => ?_⟩
      · constructor
        · intro h; omega
        · intro h; exact absurd (by rw [hT1c, ht]) h
      · rw [hT1c, ht]; exact io_events_mono_trans ⟨F4 hc, g1⟩
    · obtain ⟨e1, e2⟩ := F1 hT1c hT1
      have hge : clk ≥ s.clock - (f s).1.clock := (F2 hT1).mpr hT1c
      obtain ⟨G1, G2, G3, G4⟩ := g6 (clk - (s.clock - (f s).1.clock))
      rw [e1, e2]
      refine ⟨fun h3 h2 => ?_, fun h2 => ?_, fun h3 hc => ?_, fun hc => ?_⟩
      · obtain ⟨a, b⟩ := G1 h3 h2
        refine ⟨a, ?_⟩
        rw [b]
        have : clk - (s.clock - (f s).1.clock) - ((f s).1.clock - (g (f s).2 (f s).1).1.clock)
            = clk - (s.clock - (g (f s).2 (f s).1).1.clock) := by omega
        rw [this]
      · rw [← G2 h2]; omega
      · exact G3 h3 (by omega)
      · exact G4 (by omega)
/- HOL4: Theorem is_clock_io_mono_check
   (~ (s.clock = 0) ==>
        is_clock_io_mono (\s. f (adj_clock 1 0 s)) (dec_clock s))
    ==> is_clock_io_mono (\s. if s.clock = 0
        then (s, Rerr (Rabort Rtimeout_error)) else f s) s
-/
theorem is_clock_io_mono_check {ffi α β : Type}
    {f : cml_state ffi → cml_state ffi × result α β}
    {s : cml_state ffi} :
    (¬ (s.clock = 0) →
      is_clock_io_mono (fun s => f (adj_clock 1 0 s)) (dec_clock s)) →
    is_clock_io_mono
      (fun s => if s.clock = 0
        then (s, .Rerr (.Rabort .Rtimeout_error))
        else f s) s := by
  intro h
  rw [ep_icm_def]
  by_cases h0 : s.clock = 0
  · simp only [h0, if_true]
    refine ⟨io_events_mono_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, fun clk => ?_⟩
    refine ⟨fun _ h => (by simp at h), fun h => (by simp at h), fun h3 hc => ?_, fun hc => ?_⟩
    · have : clk = 0 := by omega
      subst this; simp at h3
    · have : clk = 0 := by omega
      subst this
      have e : ({ s with clock := 0 } : cml_state ffi) = s := by
        cases s; simp_all
      simp only [if_true, e]; exact io_events_mono_refl _
  · have hh := (ep_icm_def _ _).mp (h h0)
    have e : adj_clock 1 0 (dec_clock s) = s := by
      cases s; simp only [adj_clock, dec_clock] at *; congr 1; omega
    simp only [e] at hh
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hh
    simp only [dec_clock] at g1 g2 g3 g4 g5
    simp only [h0, if_false]
    refine ⟨g1, by omega, g3, g4, g5, fun clk => ?_⟩
    cases clk with
    | zero =>
      simp only [if_true]
      refine ⟨fun h => (by simp at h), fun _ => ?_, fun h => (by simp at h), fun _ => g1⟩
      constructor
      · intro h; omega
      · intro h; exact (by simp at h)
    | succ k =>
      have hk : ¬ (k + 1 = 0) := by omega
      simp only [hk, if_false]
      obtain ⟨G1, G2, G3, G4⟩ := g6 k
      have e2 : adj_clock 1 0 { s with clock := k } = { s with clock := k + 1 } := by
        simp [adj_clock]
      simp only [dec_clock] at G1 G2 G3 G4
      simp only [e2] at G1 G2 G3 G4
      refine ⟨fun h3 h2 => ?_, fun h2 => ?_, fun h3 hc => ?_, fun hc => ?_⟩
      · obtain ⟨a, b⟩ := G1 h3 h2
        refine ⟨a, ?_⟩
        rw [b]
        have : k - (s.clock - 1 - (f s).1.clock) = k + 1 - (s.clock - (f s).1.clock) := by omega
        rw [this]
      · rw [← G2 h2]; omega
      · exact G3 h3 (by omega)
      · exact G4 (by omega)
/- HOL4: Theorem dec_inc_clock
   dec_clock (adj_clock 1 0 s) = s
-/
theorem dec_inc_clock {ffi : Type} (s : cml_state ffi) :
    dec_clock (adj_clock 1 0 s) = s := by
  cases s; simp [dec_clock, adj_clock]
/- HOL4: Theorem do_app_refs_length
   do_app refs_ffi op vs = SOME res ==>
   LENGTH (FST refs_ffi) <= LENGTH (FST (FST res))
-/
theorem do_app_refs_length {ffi : Type}
    {refs_ffi : store v × ffi_state ffi} {op : op} {vs : List v}
    {res : (store v × ffi_state ffi) × result v v} :
    do_app refs_ffi op vs = some res →
    refs_ffi.1.length ≤ res.1.1.length := by
  obtain ⟨r, s⟩ := refs_ffi
  obtain ⟨⟨r', s'⟩, x⟩ := res
  intro h
  exact (ep_do_app_facts h).2
/- HOL4: Theorem is_clock_io_mono_do_app_simple
   ! xs (st:'ffi state).
    is_clock_io_mono (\st'.
     case do_app (st'.refs, st'.ffi) op xs of
       NONE => (st', Rerr (Rabort Rtype_error))
     | SOME ((refs,ffi),r) =>
       (st' with<| refs := refs; ffi := ffi |>, list_result r)) st
-/
theorem is_clock_io_mono_do_app_simple {ffi : Type}
    (xs : List v) (op : op) (st : cml_state ffi) :
    is_clock_io_mono (fun st' =>
      match do_app (st'.refs, st'.ffi) op xs with
      | none => (st', .Rerr (.Rabort .Rtype_error))
      | some ((refs, ffi_), r) =>
        ({ st' with refs := refs, ffi := ffi_ }, list_result r)) st := by
  rw [ep_icm_def]
  simp only
  cases h : do_app (st.refs, st.ffi) op xs with
  | none => simp [io_events_mono_refl]
  | some p =>
    obtain ⟨⟨refs, ffi_⟩, r⟩ := p
    have h1 := do_app_io_events_mono h
    have h2 := (ep_do_app_facts h).2
    simp [io_events_mono_refl, h1, h2]
    intro _ h _; exact h
theorem ep_fix_clock_ev {ffi : Type} (s1 : cml_state ffi) (env : sem_env) (e : List exp) :
    fix_clock s1 (evaluate s1 env e) = evaluate s1 env e := (fix_clock_evaluate s1 env e []).1

theorem ep_fix_clock_decs {ffi : Type} (s1 : cml_state ffi) (env : sem_env) (ds : List dec) :
    fix_clock s1 (evaluate_decs s1 env ds) = evaluate_decs s1 env ds := (fix_clock_evaluate s1 env [] ds).2

theorem icm_const {ffi α β : Type} (c : result α β) (s : cml_state ffi) :
    is_clock_io_mono (fun s => (s, c)) s := by
  cases c with
  | Rval x => exact is_clock_io_mono_return x s
  | Rerr e => exact is_clock_io_mono_err e s

theorem icm_bind' {ffi α β γ δ : Type}
    {f : cml_state ffi → cml_state ffi × result α β}
    (g : result α β → cml_state ffi → cml_state ffi × result γ δ)
    {h : cml_state ffi → cml_state ffi × result γ δ}
    {s : cml_state ffi}
    (hh : ∀ s, h s = g (f s).2 (f s).1)
    (hf : is_clock_io_mono f s)
    (hg : ∀ s' r, f s = (s', r) → is_clock_io_mono (g r) s')
    (ht : ∀ s', g (.Rerr (.Rabort .Rtimeout_error)) s' = (s', .Rerr (.Rabort .Rtimeout_error))) :
    is_clock_io_mono h s := by
  have : h = (fun s => match f s with | (s', r) => g r s') := by
    funext s; rw [hh]
  rw [this]
  exact is_clock_io_mono_bind ⟨hf, hg, ht⟩

theorem icm_cong' {ffi α β : Type}
    {f : cml_state ffi → cml_state ffi × result α β}
    (g : cml_state ffi → cml_state ffi × result α β)
    {t : cml_state ffi}
    (hg : is_clock_io_mono g t)
    (h : ∀ s', s'.eval_state_field = t.eval_state_field → s'.refs = t.refs → s'.ffi = t.ffi →
      f s' = g s') :
    is_clock_io_mono f t :=
  (is_clock_io_mono_cong rfl (fun s' ⟨a, b, c⟩ => h s' a b c)).mpr hg

theorem icm_pure {ffi α β : Type}
    {f : cml_state ffi → cml_state ffi × result α β} {s : cml_state ffi}
    (hc : ∀ clk, f { s with clock := clk } = ({ (f s).1 with clock := clk }, (f s).2))
    (h0 : (f s).1.clock = s.clock)
    (h1 : io_events_mono s.ffi (f s).1.ffi)
    (h2 : s.next_type_stamp ≤ (f s).1.next_type_stamp)
    (h3 : s.next_exn_stamp ≤ (f s).1.next_exn_stamp)
    (h4 : s.refs.length ≤ (f s).1.refs.length) :
    is_clock_io_mono f s := by
  rw [ep_icm_def]
  refine ⟨h1, Nat.le_of_eq h0, h2, h3, h4, fun clk => ?_⟩
  rw [hc clk, h0]
  refine ⟨fun _ _ => by simp, fun h => by simp [h], fun h _ => h, fun _ => io_events_mono_refl _⟩

theorem icm_map {ffi α β γ δ : Type}
    {f : cml_state ffi → cml_state ffi × result α β}
    (c : result α β → result γ δ)
    {h : cml_state ffi → cml_state ffi × result γ δ}
    {s : cml_state ffi}
    (hh : ∀ s, h s = ((f s).1, c (f s).2))
    (hf : is_clock_io_mono f s)
    (ht : c (.Rerr (.Rabort .Rtimeout_error)) = .Rerr (.Rabort .Rtimeout_error)) :
    is_clock_io_mono h s :=
  icm_bind' (fun r s' => (s', c r)) hh hf (fun s' r _ => icm_const _ _) (fun s' => by simp only [ht])

theorem icm_Raise {ffi : Type} (st : cml_state ffi) (env : sem_env) (e : exp)
    (ih : is_clock_io_mono (fun s => evaluate s env [e]) st) :
    is_clock_io_mono (fun s => evaluate s env [.Raise e]) st := by
  refine icm_map (fun r => match r with | .Rval vs => .Rerr (.Rraise vs.head!) | .Rerr e => .Rerr e)
    (fun s => ?_) ih rfl
  rw [evaluate]
  split <;> simp [*]

theorem icm_if_refs {ffi α β : Type} (P : store v → Prop) [DecidablePred P]
    {F G : cml_state ffi → cml_state ffi × result α β} {s : cml_state ffi}
    (h1 : P s.refs → is_clock_io_mono F s) (h2 : ¬ P s.refs → is_clock_io_mono G s) :
    is_clock_io_mono (fun s => if P s.refs then F s else G s) s := by
  by_cases h : P s.refs
  · exact icm_cong' F (h1 h) (fun s' _ hr _ => by simp only [hr, h, if_true])
  · exact icm_cong' G (h2 h) (fun s' _ hr _ => by simp only [hr, h, if_false])

theorem icm_Handle {ffi : Type} (st : cml_state ffi) (env : sem_env) (e : exp) (pes : List (pat × exp))
    (ih : is_clock_io_mono (fun s => evaluate s env [e]) st)
    (ih2 : ∀ st' val_, evaluate st env [e] = (st', .Rerr (.Rraise val_)) →
      can_pmatch_all env.c st'.refs (pes.map Prod.fst) val_ = true →
      is_clock_io_mono (fun s => evaluate_match s env val_ pes val_) st') :
    is_clock_io_mono (fun s => evaluate s env [.Handle e pes]) st := by
  refine icm_bind' (fun r s' => match r with
      | .Rval v' => (s', .Rval v')
      | .Rerr (.Rraise val_) =>
        if can_pmatch_all env.c s'.refs (pes.map Prod.fst) val_ = true then
          evaluate_match s' env val_ pes val_
        else (s', .Rerr (.Rabort .Rtype_error))
      | .Rerr (.Rabort a) => (s', .Rerr (.Rabort a))) (fun s => ?_) ih (fun s' r hr => ?_) (fun s' => rfl)
  · rw [evaluate]
    split <;> rename_i heq <;> rw [ep_fix_clock_ev] at heq <;> simp [heq]
  · cases r with
    | Rval v' => exact icm_const _ _
    | Rerr er =>
      cases er with
      | Rraise val_ =>
        exact icm_if_refs (fun refs => can_pmatch_all env.c refs (pes.map Prod.fst) val_ = true)
          (fun h => ih2 s' val_ hr h) (fun _ => icm_const _ _)
      | Rabort a => exact icm_const _ _

theorem icm_of_eq {ffi α β : Type} {f : cml_state ffi → cml_state ffi × result α β}
    (g : cml_state ffi → cml_state ffi × result α β) {s : cml_state ffi}
    (hg : is_clock_io_mono g s) (h : ∀ s, f s = g s) : is_clock_io_mono f s := by
  have : f = g := funext h
  rw [this]; exact hg

theorem icm_const' {ffi α β : Type} {f : cml_state ffi → cml_state ffi × result α β}
    (c : result α β) {s : cml_state ffi} (h : ∀ s, f s = (s, c)) : is_clock_io_mono f s :=
  icm_of_eq _ (icm_const c s) h

theorem icm_refs_dep {ffi α β X : Type} (D : store v → X)
    (F : X → cml_state ffi → cml_state ffi × result α β) {s : cml_state ffi}
    (h : is_clock_io_mono (F (D s.refs)) s) :
    is_clock_io_mono (fun s => F (D s.refs) s) s :=
  icm_cong' _ h (fun s' _ hr _ => by simp only [hr])

theorem icm_es_dep {ffi α β X : Type} (D : Option eval_state → X)
    (F : X → cml_state ffi → cml_state ffi × result α β) {s : cml_state ffi}
    (h : is_clock_io_mono (F (D s.eval_state_field)) s) :
    is_clock_io_mono (fun s => F (D s.eval_state_field) s) s :=
  icm_cong' _ h (fun s' he _ _ => by simp only [he])

theorem icm_nil {ffi : Type} (st : cml_state ffi) (env : sem_env) :
    is_clock_io_mono (fun s => evaluate s env []) st :=
  icm_const' (.Rval []) (fun s => by rw [evaluate])

theorem icm_Lit {ffi : Type} (st : cml_state ffi) (env : sem_env) (l : lit) :
    is_clock_io_mono (fun s => evaluate s env [.Lit l]) st :=
  icm_const' (.Rval [.Litv l]) (fun s => by rw [evaluate])

theorem icm_Fun {ffi : Type} (st : cml_state ffi) (env : sem_env) (x : varN) (e : exp) :
    is_clock_io_mono (fun s => evaluate s env [.Fun x e]) st :=
  icm_const' (.Rval [.Closure env x e]) (fun s => by rw [evaluate])

theorem icm_Var {ffi : Type} (st : cml_state ffi) (env : sem_env) (n : cml_id modN varN) :
    is_clock_io_mono (fun s => evaluate s env [.Var n]) st :=
  icm_const' (match nsLookup env.v_ n with
      | none => .Rerr (.Rabort .Rtype_error)
      | some v' => .Rval [v']) (fun s => by rw [evaluate]; split <;> simp [*])

theorem icm_Con {ffi : Type} (st : cml_state ffi) (env : sem_env) (cn : Option (cml_id modN conN))
    (es' : List exp)
    (ih : do_con_check env.c cn es'.length = true →
      is_clock_io_mono (fun s => evaluate s env es'.reverse) st) :
    is_clock_io_mono (fun s => evaluate s env [.Con cn es']) st := by
  by_cases hc : do_con_check env.c cn es'.length = true
  · refine icm_map (fun r => match r with
        | .Rval vs => (match build_conv env.c cn vs.reverse with
          | none => .Rerr (.Rabort .Rtype_error)
          | some v' => .Rval [v'])
        | .Rerr e => .Rerr e) (fun s => ?_) (ih hc) rfl
    rw [evaluate]; simp only [hc, if_true]
    (repeat' split) <;> simp_all
  · exact icm_const' (.Rerr (.Rabort .Rtype_error)) (fun s => by rw [evaluate]; simp [hc])

theorem icm_Log {ffi : Type} (st : cml_state ffi) (env : sem_env) (l : lop) (e1 e2 : exp)
    (ih : is_clock_io_mono (fun s => evaluate s env [e1]) st)
    (ih2 : ∀ st' v1 e, evaluate st env [e1] = (st', .Rval v1) →
      do_log l v1.head! e2 = some (.Exp e) → is_clock_io_mono (fun s => evaluate s env [e]) st') :
    is_clock_io_mono (fun s => evaluate s env [.Log l e1 e2]) st := by
  refine icm_bind' (fun r s' => match r with
      | .Rval v1 => (match do_log l v1.head! e2 with
        | none => (s', .Rerr (.Rabort .Rtype_error))
        | some (.Exp e) => evaluate s' env [e]
        | some (.Val v') => (s', .Rval [v']))
      | .Rerr e => (s', .Rerr e)) (fun s => ?_) ih (fun s' r hr => ?_) (fun s' => rfl)
  · rw [evaluate]
    (repeat' split) <;> simp_all [ep_fix_clock_ev]
  · cases r with
    | Rerr e => exact icm_const _ _
    | Rval v1 =>
      simp only
      cases hl : do_log l v1.head! e2 with
      | none => exact icm_const _ _
      | some x =>
        cases x with
        | Exp e => exact ih2 s' v1 e hr hl
        | Val v' => exact icm_const _ _

theorem icm_If {ffi : Type} (st : cml_state ffi) (env : sem_env) (e1 e2 e3 : exp)
    (ih : is_clock_io_mono (fun s => evaluate s env [e1]) st)
    (ih2 : ∀ st' v' e, evaluate st env [e1] = (st', .Rval v') →
      do_if v'.head! e2 e3 = some e → is_clock_io_mono (fun s => evaluate s env [e]) st') :
    is_clock_io_mono (fun s => evaluate s env [.If e1 e2 e3]) st := by
  refine icm_bind' (fun r s' => match r with
      | .Rval v' => (match do_if v'.head! e2 e3 with
        | none => (s', .Rerr (.Rabort .Rtype_error))
        | some e => evaluate s' env [e])
      | .Rerr e => (s', .Rerr e)) (fun s => ?_) ih (fun s' r hr => ?_) (fun s' => rfl)
  · rw [evaluate]
    (repeat' split) <;> simp_all [ep_fix_clock_ev]
  · cases r with
    | Rerr e => exact icm_const _ _
    | Rval v1 =>
      simp only
      cases hl : do_if v1.head! e2 e3 with
      | none => exact icm_const _ _
      | some e => exact ih2 s' v1 e hr hl

theorem icm_Mat {ffi : Type} (st : cml_state ffi) (env : sem_env) (e : exp) (pes : List (pat × exp))
    (ih : is_clock_io_mono (fun s => evaluate s env [e]) st)
    (ih2 : ∀ st' v', evaluate st env [e] = (st', .Rval v') →
      can_pmatch_all env.c st'.refs (pes.map Prod.fst) v'.head! = true →
      is_clock_io_mono (fun s => evaluate_match s env v'.head! pes bind_exn_v) st') :
    is_clock_io_mono (fun s => evaluate s env [.Mat e pes]) st := by
  refine icm_bind' (fun r s' => match r with
      | .Rval v' =>
        if can_pmatch_all env.c s'.refs (pes.map Prod.fst) v'.head! = true then
          evaluate_match s' env v'.head! pes bind_exn_v
        else (s', .Rerr (.Rabort .Rtype_error))
      | .Rerr e => (s', .Rerr e)) (fun s => ?_) ih (fun s' r hr => ?_) (fun s' => rfl)
  · rw [evaluate]
    split <;> rename_i heq <;> rw [ep_fix_clock_ev] at heq <;> simp [heq]
  · cases r with
    | Rerr e => exact icm_const _ _
    | Rval v' =>
      exact icm_if_refs (fun refs => can_pmatch_all env.c refs (pes.map Prod.fst) v'.head! = true)
        (fun h => ih2 s' v' hr h) (fun _ => icm_const _ _)

theorem icm_Let {ffi : Type} (st : cml_state ffi) (env : sem_env) (xo : Option varN) (e1 e2 : exp)
    (ih : is_clock_io_mono (fun s => evaluate s env [e1]) st)
    (ih2 : ∀ st' v', evaluate st env [e1] = (st', .Rval v') →
      is_clock_io_mono (fun s => evaluate s (.mk (nsOptBind xo v'.head! env.v_) env.c) [e2]) st') :
    is_clock_io_mono (fun s => evaluate s env [.Let xo e1 e2]) st := by
  refine icm_bind' (fun r s' => match r with
      | .Rval v' => evaluate s' (.mk (nsOptBind xo v'.head! env.v_) env.c) [e2]
      | .Rerr e => (s', .Rerr e)) (fun s => ?_) ih (fun s' r hr => ?_) (fun s' => rfl)
  · rw [evaluate]
    split <;> rename_i heq <;> rw [ep_fix_clock_ev] at heq <;> simp [heq]
  · cases r with
    | Rerr e => exact icm_const _ _
    | Rval v' => exact ih2 s' v' hr

theorem icm_Letrec {ffi : Type} (st : cml_state ffi) (env : sem_env)
    (funs : List (varN × varN × exp)) (e : exp)
    (ih : ALL_DISTINCT (funs.map fun (x, _, _) => x) = true →
      is_clock_io_mono (fun s => evaluate s (.mk (build_rec_env funs env env.v_) env.c) [e]) st) :
    is_clock_io_mono (fun s => evaluate s env [.Letrec funs e]) st := by
  by_cases hc : ALL_DISTINCT (funs.map fun (x, _, _) => x) = true
  · exact icm_of_eq _ (ih hc) (fun s => by rw [evaluate]; simp only [hc, if_true])
  · exact icm_const' (.Rerr (.Rabort .Rtype_error)) (fun s => by rw [evaluate]; simp only [hc]; rfl)

theorem icm_Tannot {ffi : Type} (st : cml_state ffi) (env : sem_env) (e : exp) (t : ast_t)
    (ih : is_clock_io_mono (fun s => evaluate s env [e]) st) :
    is_clock_io_mono (fun s => evaluate s env [.Tannot e t]) st :=
  icm_of_eq _ ih (fun s => by rw [evaluate])

theorem icm_Lannot {ffi : Type} (st : cml_state ffi) (env : sem_env) (e : exp) (l : locs)
    (ih : is_clock_io_mono (fun s => evaluate s env [e]) st) :
    is_clock_io_mono (fun s => evaluate s env [.Lannot e l]) st :=
  icm_of_eq _ ih (fun s => by rw [evaluate])

theorem icm_cons {ffi : Type} (st : cml_state ffi) (env : sem_env) (e1 e2 : exp) (es' : List exp)
    (ih : is_clock_io_mono (fun s => evaluate s env [e1]) st)
    (ih2 : ∀ st' v1, evaluate st env [e1] = (st', .Rval v1) →
      is_clock_io_mono (fun s => evaluate s env (e2 :: es')) st') :
    is_clock_io_mono (fun s => evaluate s env (e1 :: e2 :: es')) st := by
  refine icm_bind' (fun r s' => match r with
      | .Rval v1 => ((evaluate s' env (e2 :: es')).1,
          match (evaluate s' env (e2 :: es')).2 with
          | .Rval vs => .Rval (v1.head! :: vs)
          | .Rerr e => .Rerr e)
      | .Rerr e => (s', .Rerr e)) (fun s => ?_) ih (fun s' r hr => ?_) (fun s' => rfl)
  · rw [evaluate]
    (repeat' split) <;> simp_all [ep_fix_clock_ev]
  · cases r with
    | Rerr e => exact icm_const _ _
    | Rval v1 =>
      exact icm_map (fun r => match r with
          | .Rval vs => .Rval (v1.head! :: vs)
          | .Rerr e => .Rerr e) (fun s => rfl) (ih2 s' v1 hr) rfl

theorem icm_es_set {ffi α β : Type} (es1 : Option eval_state)
    (H : cml_state ffi → cml_state ffi × result α β) {s : cml_state ffi}
    (h : is_clock_io_mono H { s with eval_state_field := es1 }) :
    is_clock_io_mono (fun s => H { s with eval_state_field := es1 }) s := by
  rw [ep_icm_def] at h ⊢
  exact h

theorem icm_es_upd {ffi α β : Type} (E : Option eval_state → Option eval_state)
    (c : result α β) (s : cml_state ffi) :
    is_clock_io_mono (fun s => ({ s with eval_state_field := E s.eval_state_field }, c)) s :=
  icm_pure (fun _ => rfl) rfl (io_events_mono_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

def icm_appF {ffi : Type} (vs : List v) (s' : cml_state ffi) : cml_state ffi × result (List v) v :=
  match do_opapp vs.reverse with
  | some (env', e) =>
    if s'.clock = 0 then (s', .Rerr (.Rabort .Rtimeout_error))
    else evaluate (dec_clock s') env' [e]
  | none => (s', .Rerr (.Rabort .Rtype_error))

def icm_appT_k {ffi : Type} (vs : List v) (r : result (List v) v) (st2 : cml_state ffi) :
    cml_state ffi × result (List v) v :=
  match r with
  | .Rval vs2 =>
    (match update_thunk vs.reverse st2.refs vs2 with
     | none => (st2, .Rerr (.Rabort .Rtype_error))
     | some refs => ({ st2 with refs := refs }, .Rval vs2))
  | .Rerr e => (st2, .Rerr e)

def icm_appT {ffi : Type} (vs : List v) (d : dest_thunk_ret) (s' : cml_state ffi) :
    cml_state ffi × result (List v) v :=
  match d with
  | .BadRef => (s', .Rerr (.Rabort .Rtype_error))
  | .NotThunk => (s', .Rerr (.Rabort .Rtype_error))
  | .IsThunk .Evaluated val_ => (s', .Rval [val_])
  | .IsThunk .NotEvaluated f =>
    match do_opapp [f, .Conv none []] with
    | some (env', e) =>
      if s'.clock = 0 then (s', .Rerr (.Rabort .Rtimeout_error))
      else icm_appT_k vs (evaluate (dec_clock s') env' [e]).2 (evaluate (dec_clock s') env' [e]).1
    | none => (s', .Rerr (.Rabort .Rtype_error))

def icm_appE_k {ffi : Type} (es0 : Option eval_state) (env1 : sem_env) (r : result sem_env v)
    (st2 : cml_state ffi) : cml_state ffi × result (List v) v :=
  match r with
  | .Rval env2 =>
    (match declare_env st2.eval_state_field (extend_dec_env env2 env1) with
     | some (x, es2) =>
       ({ st2 with eval_state_field := reset_env_generation es0 es2 }, .Rval [x])
     | none => (st2, .Rerr (.Rabort .Rtype_error)))
  | .Rerr (.Rabort a) => (st2, .Rerr (.Rabort a))
  | .Rerr e =>
    ({ st2 with eval_state_field := reset_env_generation es0 st2.eval_state_field }, .Rerr e)

def icm_appE {ffi : Type} (es0 : Option eval_state)
    (r : result (sem_env × List dec) v) (st1 : cml_state ffi) :
    cml_state ffi × result (List v) v :=
  match r with
  | .Rval (env1, decs) =>
    if st1.clock = 0 then (st1, .Rerr (.Rabort .Rtimeout_error))
    else icm_appE_k es0 env1
      (evaluate_decs (dec_clock st1) env1 decs).2
      (evaluate_decs (dec_clock st1) env1 decs).1
  | .Rerr e => (st1, .Rerr e)

def icm_appG {ffi : Type} (o : op) (r : result (List v) v) (s' : cml_state ffi) :
    cml_state ffi × result (List v) v :=
  match r with
  | .Rval vs =>
    (match getOpClass o with
     | .FunApp => icm_appF vs s'
     | .Force => icm_appT vs (dest_thunk vs.reverse s'.refs) s'
     | .EvalOp => icm_appE s'.eval_state_field (do_eval_res vs.reverse s').2 (do_eval_res vs.reverse s').1
     | .Simple =>
       match do_app (s'.refs, s'.ffi) o vs.reverse with
       | none => (s', .Rerr (.Rabort .Rtype_error))
       | some ((refs, ffi_), r) =>
         ({ s' with refs := refs, ffi := ffi_ }, list_result r))
  | .Rerr e => (s', .Rerr e)

theorem icm_do_eval_res_none {ffi : Type} {vs : List v} {s : cml_state ffi}
    (h : do_eval vs s.eval_state_field = none) :
    do_eval_res vs s = (s, .Rerr (.Rabort .Rtype_error)) := by
  simp [do_eval_res, h]

theorem icm_do_eval_res_some {ffi : Type} {vs : List v} {s : cml_state ffi} {env1 decs es1}
    (h : do_eval vs s.eval_state_field = some (env1, decs, es1)) :
    do_eval_res vs s = ({ s with eval_state_field := es1 }, .Rval (env1, decs)) := by
  simp [do_eval_res, h]

theorem icm_App_eq {ffi : Type} (s : cml_state ffi) (env : sem_env) (o : op) (es' : List exp) :
    evaluate s env [.App o es'] =
      icm_appG o (evaluate s env es'.reverse).2 (evaluate s env es'.reverse).1 := by
  rw [evaluate]
  unfold icm_appG icm_appF icm_appT icm_appE icm_appT_k icm_appE_k
  (repeat' split) <;> simp_all [ep_fix_clock_ev, ep_fix_clock_decs, fix_clock_do_eval_res] <;>
    (rename_i h1 h2; exact absurd h2.symm (h1 _))

theorem icm_update_thunk_length {vs : List v} {st : store v} {vs2 : List v} {refs : store v}
    (h : update_thunk vs st vs2 = some refs) : refs.length = st.length := by
  unfold update_thunk at h
  split at h
  · split at h
    · exact ep_store_assign_length h
    · cases h
  · cases h

theorem icm_appT_k_icm {ffi : Type} (vs : List v) (r : result (List v) v) (st2 : cml_state ffi) :
    is_clock_io_mono (icm_appT_k vs r) st2 := by
  cases r with
  | Rerr e => exact icm_const' _ (fun s => rfl)
  | Rval vs2 =>
    refine icm_of_eq _ (icm_refs_dep (fun refs => update_thunk vs.reverse refs vs2)
      (fun u st2 => match u with
        | none => (st2, .Rerr (.Rabort .Rtype_error))
        | some refs => ({ st2 with refs := refs }, .Rval vs2)) ?_) (fun s => rfl)
    dsimp only
    cases hu : update_thunk vs.reverse st2.refs vs2 with
    | none => exact icm_const' _ (fun s => rfl)
    | some refs =>
      exact icm_pure (fun _ => rfl) rfl (io_events_mono_refl _) (Nat.le_refl _) (Nat.le_refl _)
        (Nat.le_of_eq (icm_update_thunk_length hu).symm)

theorem icm_appE_k_icm {ffi : Type} (es0 : Option eval_state) (env1 : sem_env)
    (r : result sem_env v) (st2 : cml_state ffi) :
    is_clock_io_mono (icm_appE_k es0 env1 r) st2 := by
  cases r with
  | Rval env2 =>
    refine icm_of_eq _ (icm_es_dep (fun es => declare_env es (extend_dec_env env2 env1))
      (fun u st2 => match u with
        | some (x, es2) =>
          ({ st2 with eval_state_field := reset_env_generation es0 es2 }, .Rval [x])
        | none => (st2, .Rerr (.Rabort .Rtype_error))) ?_) (fun s => rfl)
    dsimp only
    cases hu : declare_env st2.eval_state_field (extend_dec_env env2 env1) with
    | none => exact icm_const' _ (fun s => rfl)
    | some p =>
      obtain ⟨x, es2⟩ := p
      exact icm_es_upd (fun _ => reset_env_generation es0 es2) (.Rval [x]) _
  | Rerr e =>
    cases e with
    | Rabort a => exact icm_const' _ (fun s => rfl)
    | Rraise x => exact icm_es_upd (fun es => reset_env_generation es0 es) _ _

theorem icm_appF_icm {ffi : Type} (vs : List v) (s' : cml_state ffi)
    (ih : ∀ env' e, do_opapp vs.reverse = some (env', e) → s'.clock ≠ 0 →
      is_clock_io_mono (fun s => evaluate s env' [e]) (dec_clock s')) :
    is_clock_io_mono (icm_appF vs) s' := by
  cases h : do_opapp vs.reverse with
  | none => exact icm_const' (.Rerr (.Rabort .Rtype_error)) (fun s => by simp [icm_appF, h])
  | some p =>
    obtain ⟨env', e⟩ := p
    refine icm_of_eq _ (@is_clock_io_mono_check _ _ _ (fun s => evaluate (dec_clock s) env' [e]) s'
      (fun h0 => ?_)) (fun s => by simp [icm_appF, h])
    simp only [dec_inc_clock]
    exact ih env' e h h0

theorem icm_appT_icm {ffi : Type} (vs : List v) (d : dest_thunk_ret) (s' : cml_state ffi)
    (ih : ∀ f env' e, d = .IsThunk .NotEvaluated f →
      do_opapp [f, .Conv none []] = some (env', e) → s'.clock ≠ 0 →
      is_clock_io_mono (fun s => evaluate s env' [e]) (dec_clock s')) :
    is_clock_io_mono (icm_appT vs d) s' := by
  cases d with
  | BadRef => exact icm_const' _ (fun s => rfl)
  | NotThunk => exact icm_const' _ (fun s => rfl)
  | IsThunk m f =>
    cases m with
    | Evaluated => exact icm_const' _ (fun s => rfl)
    | NotEvaluated =>
      cases h : do_opapp [f, .Conv none []] with
      | none => exact icm_const' (.Rerr (.Rabort .Rtype_error)) (fun s => by simp [icm_appT, h])
      | some p =>
        obtain ⟨env', e⟩ := p
        refine icm_of_eq _ (@is_clock_io_mono_check _ _ _
          (fun s => icm_appT_k vs (evaluate (dec_clock s) env' [e]).2
            (evaluate (dec_clock s) env' [e]).1) s'
          (fun h0 => ?_)) (fun s => by simp [icm_appT, h])
        simp only [dec_inc_clock]
        exact icm_bind' (icm_appT_k vs) (fun s => rfl) (ih f env' e rfl h h0)
          (fun s2 r _ => icm_appT_k_icm vs r s2) (fun s2 => rfl)

theorem icm_appE_icm {ffi : Type} (vs : List v) (s' : cml_state ffi)
    (ih : ∀ st1 env1 decs, do_eval_res vs s' = (st1, .Rval (env1, decs)) → st1.clock ≠ 0 →
      is_clock_io_mono (fun s => evaluate_decs s env1 decs) (dec_clock st1)) :
    is_clock_io_mono (fun s' => icm_appE s'.eval_state_field
      (do_eval_res vs s').2 (do_eval_res vs s').1) s' := by
  cases hd : do_eval vs s'.eval_state_field with
  | none =>
    refine icm_cong' _ (icm_const (.Rerr (.Rabort .Rtype_error)) s') (fun s he _ _ => ?_)
    rw [← he] at hd
    simp [icm_do_eval_res_none hd, icm_appE]
  | some p =>
    obtain ⟨env1, decs, es1⟩ := p
    have hs := icm_do_eval_res_some hd
    refine icm_cong' _ (icm_es_set es1 (fun s1 =>
      if s1.clock = 0 then (s1, .Rerr (.Rabort .Rtimeout_error))
      else (fun s => icm_appE_k s'.eval_state_field env1
        (evaluate_decs (dec_clock s) env1 decs).2
        (evaluate_decs (dec_clock s) env1 decs).1) s1) (is_clock_io_mono_check (fun h0 => ?_)))
      (fun s he _ _ => ?_)
    · simp only [dec_inc_clock]
      exact icm_bind' (icm_appE_k s'.eval_state_field env1) (fun s => rfl) (ih _ env1 decs hs h0)
        (fun s2 r _ => icm_appE_k_icm _ _ r s2) (fun s2 => rfl)
    · rw [← he] at hd
      simp [icm_do_eval_res_some hd, icm_appE, he]

theorem icm_App {ffi : Type} (st : cml_state ffi) (env : sem_env) (o : op) (es' : List exp)
    (ih : is_clock_io_mono (fun s => evaluate s env es'.reverse) st)
    (ihF : ∀ st' vs env' e, evaluate st env es'.reverse = (st', .Rval vs) →
      getOpClass o = .FunApp → do_opapp vs.reverse = some (env', e) → st'.clock ≠ 0 →
      is_clock_io_mono (fun s => evaluate s env' [e]) (dec_clock st'))
    (ihT : ∀ st' vs f env' e, evaluate st env es'.reverse = (st', .Rval vs) →
      getOpClass o = .Force → dest_thunk vs.reverse st'.refs = .IsThunk .NotEvaluated f →
      do_opapp [f, .Conv none []] = some (env', e) → st'.clock ≠ 0 →
      is_clock_io_mono (fun s => evaluate s env' [e]) (dec_clock st'))
    (ihE : ∀ st' vs st1 env1 decs, evaluate st env es'.reverse = (st', .Rval vs) →
      getOpClass o = .EvalOp → do_eval_res vs.reverse st' = (st1, .Rval (env1, decs)) →
      st1.clock ≠ 0 →
      is_clock_io_mono (fun s => evaluate_decs s env1 decs) (dec_clock st1)) :
    is_clock_io_mono (fun s => evaluate s env [.App o es']) st := by
  refine icm_bind' (icm_appG o) (fun s => icm_App_eq s env o es') ih (fun s' r hr => ?_)
    (fun s' => rfl)
  cases r with
  | Rerr e => exact icm_const' _ (fun s => rfl)
  | Rval vs =>
    cases hc : getOpClass o with
    | FunApp =>
      exact icm_of_eq _ (icm_appF_icm vs s' (fun env' e h1 h2 => ihF s' vs env' e hr hc h1 h2))
        (fun s => by simp [icm_appG, hc])
    | Force =>
      exact icm_of_eq _ (icm_refs_dep (fun refs => dest_thunk vs.reverse refs)
        (fun d s => icm_appT vs d s)
        (icm_appT_icm vs _ s' (fun f env' e h1 h2 h3 => ihT s' vs f env' e hr hc h1 h2 h3)))
        (fun s => by simp [icm_appG, hc])
    | EvalOp =>
      exact icm_of_eq _ (icm_appE_icm vs.reverse s'
        (fun st1 env1 decs h1 h2 => ihE s' vs st1 env1 decs hr hc h1 h2))
        (fun s => by simp [icm_appG, hc])
    | Simple =>
      exact icm_of_eq _ (is_clock_io_mono_do_app_simple vs.reverse o s')
        (fun s => by simp only [icm_appG, hc] <;> first | rfl | (split <;> simp_all))

theorem icm_match_nil {ffi : Type} (st : cml_state ffi) (env : sem_env) (val_ err_v : v) :
    is_clock_io_mono (fun s => evaluate_match s env val_ [] err_v) st :=
  icm_const' (.Rerr (.Rraise err_v)) (fun s => by rw [evaluate_match])

theorem icm_match_cons {ffi : Type} (st : cml_state ffi) (env : sem_env) (val_ err_v : v)
    (p : pat) (e : exp) (pes' : List (pat × exp))
    (ih1 : ALL_DISTINCT (pat_bindings p []) = true → pmatch env.c st.refs p val_ [] = .No_match →
      is_clock_io_mono (fun s => evaluate_match s env val_ pes' err_v) st)
    (ih2 : ∀ env_v', ALL_DISTINCT (pat_bindings p []) = true →
      pmatch env.c st.refs p val_ [] = .Match env_v' →
      is_clock_io_mono
        (fun s => evaluate s (.mk (nsAppend (alist_to_ns env_v') env.v_) env.c) [e]) st) :
    is_clock_io_mono (fun s => evaluate_match s env val_ ((p, e) :: pes') err_v) st := by
  by_cases hd : ALL_DISTINCT (pat_bindings p []) = true
  · refine icm_of_eq _ (icm_refs_dep (fun refs => pmatch env.c refs p val_ [])
      (fun m s => match m with
        | .No_match => evaluate_match s env val_ pes' err_v
        | .Match_type_error => (s, .Rerr (.Rabort .Rtype_error))
        | .Match env_v' =>
          evaluate s (.mk (nsAppend (alist_to_ns env_v') env.v_) env.c) [e]) ?_)
      (fun s => by rw [evaluate_match]; simp only [hd, if_true]; first | rfl | (split <;> simp_all))
    dsimp only
    cases hm : pmatch env.c st.refs p val_ [] with
    | No_match => exact ih1 hd hm
    | Match_type_error => exact icm_const' _ (fun s => rfl)
    | Match env_v' => exact ih2 env_v' hd hm
  · exact icm_const' (.Rerr (.Rabort .Rtype_error))
      (fun s => by rw [evaluate_match]; simp only [hd]; rfl)

theorem icm_decs_nil {ffi : Type} (st : cml_state ffi) (env : sem_env) :
    is_clock_io_mono (fun s => evaluate_decs s env []) st :=
  icm_const' (.Rval (.mk nsEmpty nsEmpty)) (fun s => by rw [evaluate_decs])

theorem icm_Dlet {ffi : Type} (st : cml_state ffi) (env : sem_env) (l : locs) (p : pat) (e : exp)
    (ih : ALL_DISTINCT (pat_bindings p []) = true → every_exp (one_con_check env.c) e = true →
      is_clock_io_mono (fun s => evaluate s env [e]) st) :
    is_clock_io_mono (fun s => evaluate_decs s env [.Dlet l p e]) st := by
  by_cases hc : (ALL_DISTINCT (pat_bindings p []) && every_exp (one_con_check env.c) e) = true
  · have hc' := hc
    rw [Bool.and_eq_true] at hc'
    refine icm_bind' (fun r s' => match r with
        | .Rval v' => (s', match pmatch env.c s'.refs p v'.head! [] with
          | .No_match => .Rerr (.Rraise bind_exn_v)
          | .Match_type_error => .Rerr (.Rabort .Rtype_error)
          | .Match new_vals => .Rval (.mk (alist_to_ns new_vals) nsEmpty))
        | .Rerr err => (s', .Rerr err)) (fun s => ?_) (ih hc'.1 hc'.2) (fun s' r hr => ?_)
      (fun s' => rfl)
    · rw [evaluate_decs]; simp only [hc, if_true]
      split <;> rename_i heq <;> simp [heq] <;> rfl
    · cases r with
      | Rerr err => exact icm_const' _ (fun s => rfl)
      | Rval v' =>
        exact icm_of_eq _ (icm_refs_dep (fun refs => pmatch env.c refs p v'.head! [])
          (fun m s' => (s', match m with
            | .No_match => .Rerr (.Rraise bind_exn_v)
            | .Match_type_error => .Rerr (.Rabort .Rtype_error)
            | .Match new_vals => .Rval (.mk (alist_to_ns new_vals) nsEmpty)))
          (icm_const _ _)) (fun s => rfl)
  · exact icm_const' (.Rerr (.Rabort .Rtype_error))
      (fun s => by rw [evaluate_decs]; simp only [hc]; rfl)

theorem icm_Dletrec {ffi : Type} (st : cml_state ffi) (env : sem_env) (l : locs)
    (funs : List (varN × varN × exp)) :
    is_clock_io_mono (fun s => evaluate_decs s env [.Dletrec l funs]) st :=
  icm_const' _ (fun s => by rw [evaluate_decs])

theorem icm_Dtype {ffi : Type} (st : cml_state ffi) (env : sem_env) (l : locs) (tds : type_def) :
    is_clock_io_mono (fun s => evaluate_decs s env [.Dtype l tds]) st := by
  by_cases hc : tds.all check_dup_ctors = true
  · refine icm_of_eq (fun s => ({ s with next_type_stamp := s.next_type_stamp + tds.length },
       .Rval (.mk nsEmpty (build_tdefs s.next_type_stamp tds)))) ?_
       (fun s => by rw [evaluate_decs]; simp only [hc, if_true])
    exact icm_pure (fun _ => rfl) rfl (io_events_mono_refl _) (Nat.le_add_right _ _)
      (Nat.le_refl _) (Nat.le_refl _)
  · exact icm_const' (.Rerr (.Rabort .Rtype_error))
      (fun s => by rw [evaluate_decs]; simp only [hc]; rfl)

theorem icm_Dtabbrev {ffi : Type} (st : cml_state ffi) (env : sem_env) (l : locs)
    (tvs : List tvarN) (tn : typeN) (t : ast_t) :
    is_clock_io_mono (fun s => evaluate_decs s env [.Dtabbrev l tvs tn t]) st :=
  icm_const' (.Rval (.mk nsEmpty nsEmpty)) (fun s => by rw [evaluate_decs])

theorem icm_Denv {ffi : Type} (st : cml_state ffi) (env : sem_env) (n : tvarN) :
    is_clock_io_mono (fun s => evaluate_decs s env [.Denv n]) st := by
  refine icm_of_eq _ (icm_es_dep (fun es => declare_env es env)
    (fun d s => match d with
      | none => (s, .Rerr (.Rabort .Rtype_error))
      | some (x, es') =>
        ({ s with eval_state_field := es' }, .Rval (.mk (nsSing n x) nsEmpty))) ?_)
    (fun s => by rw [evaluate_decs]; first | rfl | (split <;> simp_all))
  dsimp only
  cases hd : declare_env st.eval_state_field env with
  | none => exact icm_const' _ (fun s => rfl)
  | some q =>
    obtain ⟨x, es'⟩ := q
    exact icm_es_upd (fun _ => es') (.Rval (sem_env.mk (nsSing n x) nsEmpty)) _

theorem icm_Dexn {ffi : Type} (st : cml_state ffi) (env : sem_env) (l : locs) (cn : conN)
    (ts : List ast_t) :
    is_clock_io_mono (fun s => evaluate_decs s env [.Dexn l cn ts]) st := by
  refine icm_of_eq (fun s => ({ s with next_exn_stamp := s.next_exn_stamp + 1 },
     .Rval (.mk nsEmpty (nsSing cn (ts.length, .ExnStamp s.next_exn_stamp))))) ?_
     (fun s => by rw [evaluate_decs])
  exact icm_pure (fun _ => rfl) rfl (io_events_mono_refl _) (Nat.le_refl _)
    (Nat.le_add_right _ _) (Nat.le_refl _)

theorem icm_Dmod {ffi : Type} (st : cml_state ffi) (env : sem_env) (mn : modN) (ds' : List dec)
    (ih : is_clock_io_mono (fun s => evaluate_decs s env ds') st) :
    is_clock_io_mono (fun s => evaluate_decs s env [.Dmod mn ds']) st := by
  refine icm_map (fun (r : result sem_env v) => ((match r with
      | .Rval env' => .Rval (.mk (nsLift mn env'.v_) (nsLift mn env'.c))
      | .Rerr err => .Rerr err) : result sem_env v)) (fun s => ?_) ih rfl
  rw [evaluate_decs]
  first | rfl | (rcases evaluate_decs s env ds' with ⟨a, r⟩; cases r <;> rfl)

theorem icm_Dlocal {ffi : Type} (st : cml_state ffi) (env : sem_env) (lds ds' : List dec)
    (ih : is_clock_io_mono (fun s => evaluate_decs s env lds) st)
    (ih2 : ∀ st1 env1, evaluate_decs st env lds = (st1, .Rval env1) →
      is_clock_io_mono (fun s => evaluate_decs s (extend_dec_env env1 env) ds') st1) :
    is_clock_io_mono (fun s => evaluate_decs s env [.Dlocal lds ds']) st := by
  refine icm_bind' (fun r s' => match r with
      | .Rval env1 => evaluate_decs s' (extend_dec_env env1 env) ds'
      | .Rerr e => (s', .Rerr e)) (fun s => ?_) ih (fun s' r hr => ?_) (fun s' => rfl)
  · rw [evaluate_decs]
    split <;> rename_i heq <;> rw [ep_fix_clock_decs] at heq <;> simp [heq]
  · cases r with
    | Rerr e => exact icm_const _ _
    | Rval env1 => exact ih2 s' env1 hr

theorem icm_decs_cons {ffi : Type} (st : cml_state ffi) (env : sem_env) (d1 d2 : dec)
    (ds' : List dec)
    (ih : is_clock_io_mono (fun s => evaluate_decs s env [d1]) st)
    (ih2 : ∀ st1 env1, evaluate_decs st env [d1] = (st1, .Rval env1) →
      is_clock_io_mono (fun s => evaluate_decs s (extend_dec_env env1 env) (d2 :: ds')) st1) :
    is_clock_io_mono (fun s => evaluate_decs s env (d1 :: d2 :: ds')) st := by
  refine icm_bind' (fun r s' => match r with
      | .Rval env1 => ((evaluate_decs s' (extend_dec_env env1 env) (d2 :: ds')).1,
          combine_dec_result env1 (evaluate_decs s' (extend_dec_env env1 env) (d2 :: ds')).2)
      | .Rerr e => (s', .Rerr e)) (fun s => ?_) ih (fun s' r hr => ?_) (fun s' => rfl)
  · rw [evaluate_decs]
    split <;> rename_i heq <;> rw [ep_fix_clock_decs] at heq <;> simp [heq]
  · cases r with
    | Rerr e => exact icm_const _ _
    | Rval env1 =>
      exact icm_map (combine_dec_result env1) (fun s => rfl) (ih2 s' env1 hr) rfl

theorem icm_main {ffi : Type} :
    (∀ (s : cml_state ffi) (env : sem_env) (es : List exp),
      is_clock_io_mono (fun s => evaluate s env es) s) ∧
    (∀ (s : cml_state ffi) (env : sem_env) (ds : List dec),
      is_clock_io_mono (fun s => evaluate_decs s env ds) s) ∧
    (∀ (s : cml_state ffi) (env : sem_env) (val_ : v) (pes : List (pat × exp)) (err_v : v),
      is_clock_io_mono (fun s => evaluate_match s env val_ pes err_v) s) := by
  apply evaluate.mutual_induct
    (motive1 := fun st env es => is_clock_io_mono (fun s => evaluate s env es) st)
    (motive2 := fun st env ds => is_clock_io_mono (fun s => evaluate_decs s env ds) st)
    (motive3 := fun st env val_ pes err_v =>
      is_clock_io_mono (fun s => evaluate_match s env val_ pes err_v) st)
  all_goals intros
  all_goals (try simp only [ep_fix_clock_ev, ep_fix_clock_decs, fix_clock_do_eval_res,
    ev_attach_fst] at *)
  all_goals first
    | exact icm_nil _ _
    | exact icm_Lit _ _ _
    | exact icm_Fun _ _ _ _
    | exact icm_Var _ _ _
    | exact icm_match_nil _ _ _ _
    | exact icm_decs_nil _ _
    | exact icm_Dletrec _ _ _ _
    | exact icm_Dtype _ _ _ _
    | exact icm_Dtabbrev _ _ _ _ _ _
    | exact icm_Denv _ _ _
    | exact icm_Dexn _ _ _ _ _
    | (apply icm_Raise; assumption)
    | (apply icm_Tannot; assumption)
    | (apply icm_Lannot; assumption)
    | (apply icm_Dmod; assumption)
    | skip
  all_goals first
    | (apply icm_Handle <;> intros <;> simp_all)
    | (apply icm_Con <;> intros <;> simp_all)
    | (apply icm_App <;> intros <;> simp_all)
    | (apply icm_Log <;> intros <;> simp_all)
    | (apply icm_If <;> intros <;> simp_all)
    | (apply icm_Mat <;> intros <;> simp_all)
    | (apply icm_Let <;> intros <;> simp_all)
    | (apply icm_Letrec <;> intros <;> simp_all)
    | (apply icm_cons <;> intros <;> simp_all)
    | (apply icm_match_cons <;> intros <;> simp_all)
    | (apply icm_Dlet <;> intros <;> simp_all)
    | (apply icm_Dlocal <;> intros <;> simp_all)
    | (apply icm_decs_cons <;> intros <;> simp_all)
    | skip

/- HOL4: Theorem is_clock_io_mono_evaluate
   (!(s : 'ffi state) env es. is_clock_io_mono (\s. evaluate s env es) s) /\
   (!(s : 'ffi state) env v pes err_v.
        is_clock_io_mono (\s. evaluate_match s env v pes err_v) s) /\
   (!(s : 'ffi state) env ds.
        is_clock_io_mono (\s. evaluate_decs s env ds) s)
-/
theorem is_clock_io_mono_evaluate {ffi : Type} :
    (∀ (s : cml_state ffi) (env : sem_env) (es : List exp),
      is_clock_io_mono (fun s => evaluate s env es) s) ∧
    (∀ (s : cml_state ffi) (env : sem_env) (val_ : v) (pes : List (pat × exp)) (err_v : v),
      is_clock_io_mono (fun s => evaluate_match s env val_ pes err_v) s) ∧
    (∀ (s : cml_state ffi) (env : sem_env) (ds : List dec),
      is_clock_io_mono (fun s => evaluate_decs s env ds) s) := ⟨icm_main.1, icm_main.2.2, icm_main.2.1⟩
/- HOL4: Theorem is_clock_io_mono_evaluate_decs
   !s e p. is_clock_io_mono (\s. evaluate_decs s e p) s
-/
theorem is_clock_io_mono_evaluate_decs {ffi : Type}
    (s : cml_state ffi) (e : sem_env) (p : List dec) :
    is_clock_io_mono (fun s => evaluate_decs s e p) s := is_clock_io_mono_evaluate.2.2 s e p
/- HOL4: Theorem is_clock_io_mono_extra
   (!s. is_clock_io_mono f s)
    ==> f s = (s', r) /\ ~ (r = Rerr (Rabort Rtimeout_error))
    ==> f (s with clock := s.clock + extra)
        = (s' with clock := s'.clock + extra, r)
-/
theorem is_clock_io_mono_extra {ffi α β : Type}
    {f : cml_state ffi → cml_state ffi × result α β}
    {s s' : cml_state ffi} {r : result α β} {extra : Nat} :
    (∀ s, is_clock_io_mono f s) →
    f s = (s', r) ∧ ¬ (r = .Rerr (.Rabort .Rtimeout_error)) →
    f ({ s with clock := s.clock + extra }) =
      ({ s' with clock := s'.clock + extra }, r) := by
  rintro h ⟨hfs, hr⟩
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := (ep_icm_def f s).mp (h s)
  obtain ⟨F1, F2, F3, F4⟩ := f6 (s.clock + extra)
  rw [hfs] at F1 F2 F3 F4 f2
  simp only at F1 F2 F3 F4 f2
  have hr' := (F2 hr).mp (by omega)
  obtain ⟨a, b⟩ := F1 hr' hr
  have : s.clock + extra - (s.clock - s'.clock) = s'.clock + extra := by omega
  rw [this] at b
  rw [← a, ← b]
/- HOL4: Theorem list_result_eq_Rval[simp]
   list_result r = Rval r' ⇔ ∃v. r' = [v] ∧ r = Rval v
-/
theorem list_result_eq_Rval {α β : Type}
    {r : result α β} {r' : List α} :
    list_result r = .Rval r' ↔ ∃ v, r' = [v] ∧ r = .Rval v := by
  cases r with
  | Rval x => simp [list_result, eq_comm]
  | Rerr e => simp [list_result]
theorem ep_length_aux {ffi : Type} :
    (∀ (st : cml_state ffi) (env : sem_env) (es : List exp),
      ∀ s' r, evaluate st env es = (s', .Rval r) → r.length = es.length) ∧
    (∀ (st : cml_state ffi) (env : sem_env) (ds : List dec), True) ∧
    (∀ (st : cml_state ffi) (env : sem_env) (val_ : v) (pes : List (pat × exp)) (err_v : v),
      ∀ s' r, evaluate_match st env val_ pes err_v = (s', .Rval r) → r.length = 1) := by
  apply evaluate.mutual_induct_unfolding
    (motive1 := fun _ _ es res => ∀ s' r, res = (s', .Rval r) → r.length = es.length)
    (motive2 := fun _ _ _ _ => True)
    (motive3 := fun _ _ _ _ _ res => ∀ s' r, res = (s', .Rval r) → r.length = 1)
  all_goals (
    intros
    first
      | trivial
      | (simp_all [ev_attach_fst]; done)
      | (rename_i h; injection h with h1 h2
         first
           | (injection h2 with h2; subst h2; simp_all [ep_fix_clock_ev]; done)
           | (rw [list_result_eq_Rval] at h2; obtain ⟨_, rfl, -⟩ := h2; rfl))
      )

/- HOL4: Theorem evaluate_length
   (∀(s:'ffi state) e p s' r. evaluate s e p = (s',Rval r) ⇒ LENGTH r = LENGTH p) ∧
   (∀(s:'ffi state) e v p er s' r. evaluate_match s e v p er = (s',Rval r) ⇒ LENGTH r = 1) ∧
   (∀(s:'ffi state) e ds s' r. evaluate_decs s e ds = (s',Rval r) ⇒ T)
-/
theorem evaluate_length {ffi : Type} :
    (∀ (s : cml_state ffi) (env : sem_env) (es : List exp) (s' : cml_state ffi) (r : List v),
      evaluate s env es = (s', .Rval r) → r.length = es.length) ∧
    (∀ (s : cml_state ffi) (env : sem_env) (val_ : v) (pes : List (pat × exp)) (err_v : v)
      (s' : cml_state ffi) (r : List v),
      evaluate_match s env val_ pes err_v = (s', .Rval r) → r.length = 1) ∧
    (∀ (s : cml_state ffi) (env : sem_env) (ds : List dec) (s' : cml_state ffi) (r : sem_env),
      evaluate_decs s env ds = (s', .Rval r) → True) := ⟨ep_length_aux.1, ep_length_aux.2.2, fun _ _ _ _ _ _ => trivial⟩
/- HOL4: Theorem is_clock_io_mono_set_clock
   is_clock_io_mono f s
    ==> f s = (s', r) /\ ~ (r = Rerr (Rabort Rtimeout_error))
    ==> ?ck0. f (s with clock := ck0) = (s' with clock := ck1, r)
-/
theorem is_clock_io_mono_set_clock {ffi α β : Type}
    {f : cml_state ffi → cml_state ffi × result α β}
    {s s' : cml_state ffi} {r : result α β} {ck1 : Nat} :
    is_clock_io_mono f s →
    f s = (s', r) ∧ ¬ (r = .Rerr (.Rabort .Rtimeout_error)) →
    ∃ ck0, f ({ s with clock := ck0 }) = ({ s' with clock := ck1 }, r) := by
  rintro h ⟨hfs, hr⟩
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := (ep_icm_def f s).mp h
  obtain ⟨F1, F2, F3, F4⟩ := f6 (ck1 + (s.clock - s'.clock))
  rw [hfs] at F1 F2 F3 F4 f2
  simp only at F1 F2 F3 F4 f2
  have hr' := (F2 hr).mp (by omega)
  obtain ⟨a, b⟩ := F1 hr' hr
  have : ck1 + (s.clock - s'.clock) - (s.clock - s'.clock) = ck1 := by omega
  rw [this] at b
  exact ⟨_, by rw [← a, ← b]⟩
/- HOL4: Theorem is_clock_io_mono_minimal
   is_clock_io_mono f s
    ==> f s = (s', r) /\ s'.clock = 0 /\ r <> Rerr (Rabort Rtimeout_error)
        /\ s.clock > k
    ==> (?s''. f (s with clock := k) = (s'', Rerr (Rabort Rtimeout_error)) /\
               io_events_mono s''.ffi s'.ffi)
-/
theorem is_clock_io_mono_minimal {ffi α β : Type}
    {f : cml_state ffi → cml_state ffi × result α β}
    {s s' : cml_state ffi} {r : result α β} {k : Nat} :
    is_clock_io_mono f s →
    f s = (s', r) ∧ s'.clock = 0 ∧ r ≠ .Rerr (.Rabort .Rtimeout_error) ∧ s.clock > k →
    ∃ s'', f ({ s with clock := k }) = (s'', .Rerr (.Rabort .Rtimeout_error)) ∧
      io_events_mono s''.ffi s'.ffi := by
  rintro h ⟨hfs, hc, hr, hk⟩
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := (ep_icm_def f s).mp h
  obtain ⟨F1, F2, F3, F4⟩ := f6 k
  rw [hfs] at F1 F2 F3 F4 f2
  simp only at F1 F2 F3 F4 f2
  have hT : (f { s with clock := k }).2 = .Rerr (.Rabort .Rtimeout_error) := by
    apply Classical.byContradiction
    intro hn
    have := (F2 hr).mpr hn
    omega
  exact ⟨(f { s with clock := k }).1, by rw [← hT], F4 (by omega)⟩
/- HOL4: Theorem can_pmatch_all_EVERY
   can_pmatch_all envC refs ps v <=>
   EVERY (\p. pmatch envC refs p v [] <> Match_type_error) ps
-/
theorem can_pmatch_all_EVERY
    (envC : env_ctor) (refs : store v) (ps : List pat) (val_ : v) :
    can_pmatch_all envC refs ps val_ = true ↔
    ∀ p, p ∈ ps → pmatch envC refs p val_ [] ≠ .Match_type_error := by
  induction ps with
  | nil => simp [can_pmatch_all]
  | cons p t ih =>
    simp only [can_pmatch_all, List.mem_cons, forall_eq_or_imp]
    cases h : pmatch envC refs p val_ [] <;> simp [ih]
