import LeanTypeSound.DAux1
open HOL4
namespace DAux

theorem Boolv_beq (b b' : Bool) : (Boolv b == Boolv b') = (b == b') := by
  cases b <;> cases b' <;> simp [Boolv, BEq.beq, v_beq, v_list_beq] <;> decide

theorem v_beq_Boolv (x : v) (b : Bool) : (x == Boolv b) = true ↔ x = Boolv b := by
  constructor
  · intro h
    cases b
    · simp only [Boolv, BEq.beq, Bool.false_eq_true, if_false] at h ⊢
      cases x <;> simp [v_beq] at h
      rename_i st vs
      cases vs <;> simp [v_list_beq] at h
      have : st = some (stamp.TypeStamp (mlstring.strlit "False") bool_type_num) := by
        simpa using h
      rw [this]
    · simp only [Boolv, BEq.beq, if_true] at h ⊢
      cases x <;> simp [v_beq] at h
      rename_i st vs
      cases vs <;> simp [v_list_beq] at h
      have : st = some (stamp.TypeStamp (mlstring.strlit "True") bool_type_num) := by
        simpa using h
      rw [this]
  · intro h; subst h; rw [Boolv_beq]; simp

def op_res {ffi : Type} (c : ctMap) (s : tenv_store) (t : sem_t)
    (r : Option ((store v × ffi_state ffi) × result v v)) : Prop :=
  ∃ (s' : tenv_store) (store' : List (store_v v)) (ffi' : ffi_state ffi) (r' : result v v),
    ste s s' ∧ type_s c store' s' ∧ r = some ((store', ffi'), r') ∧
    match r' with
    | .Rval val_ => type_v 0 c s' val_ t
    | .Rerr (.Rraise val_) => type_v 0 c s' val_ Texn
    | .Rerr (.Rabort (.Rffi_error _)) => True
    | .Rerr (.Rabort _) => False

section
variable {ffi : Type} {c : ctMap} {s : tenv_store} {st : List (store_v v)} {f : ffi_state ffi}

theorem op_res_val {t : sem_t} {x : v} (hs : type_s c st s) (hv : type_v 0 c s x t) :
    op_res c s t (some ((st, f), .Rval x)) :=
  ⟨s, st, f, _, ste_refl s, hs, rfl, hv⟩

theorem op_res_val' {t : sem_t} {x : v} {s' : tenv_store} {st' : List (store_v v)}
    (he : ste s s') (hs : type_s c st' s') (hv : type_v 0 c s' x t) :
    op_res (ffi := ffi) c s t (some ((st', f), .Rval x)) :=
  ⟨s', st', f, _, he, hs, rfl, hv⟩

theorem op_res_exn {t : sem_t} {x : v} (hs : type_s c st s) (hv : type_v 0 c s x Texn) :
    op_res c s t (some ((st, f), .Rerr (.Rraise x))) :=
  ⟨s, st, f, _, ste_refl s, hs, rfl, hv⟩

theorem op_res_sub {t : sem_t} (hs : type_s c st s) (he : ctMap_has_exns c) :
    op_res c s t (some ((st, f), .Rerr (.Rraise sub_exn_v))) :=
  op_res_exn hs (type_v_exn' 0 c s he).2.1

theorem op_res_div {t : sem_t} (hs : type_s c st s) (he : ctMap_has_exns c) :
    op_res c s t (some ((st, f), .Rerr (.Rraise div_exn_v))) :=
  op_res_exn hs (type_v_exn' 0 c s he).2.2.2

theorem op_res_chr {t : sem_t} (hs : type_s c st s) (he : ctMap_has_exns c) :
    op_res c s t (some ((st, f), .Rerr (.Rraise chr_exn_v))) :=
  op_res_exn hs (type_v_exn' 0 c s he).1

theorem type_v_unit : type_v 0 c s (.Conv none []) (Ttup []) :=
  .conv_none _ _ _ _ _ rfl (by intro i hi; simp at hi)

theorem lr1 {α β : Type} {R : α → β → Prop} {l : List α} {a : β} (h : LIST_REL R l [a]) :
    ∃ x, l = [x] ∧ R x a := by
  obtain ⟨x, l', rfl, h1, h2⟩ := LIST_REL_cons_right.mp h
  rw [LIST_REL_nil_right] at h2; subst h2
  exact ⟨x, rfl, h1⟩

theorem lr2 {α β : Type} {R : α → β → Prop} {l : List α} {a b : β} (h : LIST_REL R l [a, b]) :
    ∃ x y, l = [x, y] ∧ R x a ∧ R y b := by
  obtain ⟨x, l', rfl, h1, h2⟩ := LIST_REL_cons_right.mp h
  obtain ⟨y, rfl, h3⟩ := lr1 h2
  exact ⟨x, y, rfl, h1, h3⟩

theorem lr3 {α β : Type} {R : α → β → Prop} {l : List α} {a b d : β} (h : LIST_REL R l [a, b, d]) :
    ∃ x y z, l = [x, y, z] ∧ R x a ∧ R y b ∧ R z d := by
  obtain ⟨x, l', rfl, h1, h2⟩ := LIST_REL_cons_right.mp h
  obtain ⟨y, z, rfl, h3, h4⟩ := lr2 h2
  exact ⟨x, y, z, rfl, h1, h3, h4⟩

theorem lr5 {α β : Type} {R : α → β → Prop} {l : List α} {a b d e g : β}
    (h : LIST_REL R l [a, b, d, e, g]) :
    ∃ x y z u w, l = [x, y, z, u, w] ∧ R x a ∧ R y b ∧ R z d ∧ R u e ∧ R w g := by
  obtain ⟨x, l', rfl, h1, h2⟩ := LIST_REL_cons_right.mp h
  obtain ⟨y, l', rfl, h3, h4⟩ := LIST_REL_cons_right.mp h2
  obtain ⟨z, u, w, rfl, h5, h6, h7⟩ := lr3 h4
  exact ⟨x, y, z, u, w, rfl, h1, h3, h5, h6, h7⟩

theorem op_shift8 (hc : ctMap_ok c) (hs : type_s c st s) {sh : shift} {n : Nat} {v1 : v}
    (h1 : type_v 0 c s v1 Tword8) :
    op_res c s Tword8 (do_app (st, f) (.Shift .W8 sh n) [v1]) := by
  obtain ⟨w, rfl⟩ := canon_Tword8 h1 hc
  simp [do_app]
  exact op_res_val hs (.litv_word8 _ _ _ _)

theorem op_shift64 (hc : ctMap_ok c) (hs : type_s c st s) {sh : shift} {n : Nat} {v1 : v}
    (h1 : type_v 0 c s v1 Tword64) :
    op_res c s Tword64 (do_app (st, f) (.Shift .W64 sh n) [v1]) := by
  obtain ⟨w, rfl⟩ := canon_Tword64 h1 hc
  simp [do_app]
  exact op_res_val hs (.litv_word64 _ _ _ _)

theorem op_equality (hc : ctMap_ok c) (hb : ctMap_has_bools c) (hs : type_s c st s) {v1 v2 : v} {t : sem_t}
    (h1 : type_v 0 c s v1 t) (h2 : type_v 0 c s v2 t) :
    op_res c s Tbool (do_app (st, f) .Equality [v1, v2]) := by
  have := eq_same_type_1 hc h1 h2
  simp [do_app]
  cases h : do_eq v1 v2 with
  | Eq_type_error => exact absurd h this
  | Eq_val b => exact op_res_val hs (type_v_Boolv' b hb)


theorem op_res_mk {t : sem_t} {s' : tenv_store} {st' : List (store_v v)} {f' : ffi_state ffi}
    {r' : result v v} (he : ste s s') (hs : type_s c st' s')
    (hr : match r' with
      | .Rval val_ => type_v 0 c s' val_ t
      | .Rerr (.Rraise val_) => type_v 0 c s' val_ Texn
      | .Rerr (.Rabort (.Rffi_error _)) => True
      | .Rerr (.Rabort _) => False) :
    op_res c s t (some ((st', f'), r')) :=
  ⟨s', st', f', r', he, hs, rfl, hr⟩

theorem EL_mem {α : Type} [Inhabited α] {n : Nat} {l : List α} (h : n < l.length) : EL n l ∈ l := by
  simp [EL, h]

theorem op_opassign (hc : ctMap_ok c) (hs : type_s c st s) {v1 v2 : v} {u2 : sem_t}
    (h1 : type_v 0 c s v1 (Tref u2)) (h2 : type_v 0 c s v2 u2) :
    op_res c s (Ttup []) (do_app (st, f) .Opassign [v1, v2]) := by
  obtain ⟨n, rfl, hl⟩ := canon_Tref h1 hc
  obtain ⟨st', ha, hs'⟩ := store_assign_type_sound' c s st (.Refv v2) (.Ref_t u2) n ⟨hs, hl, h2⟩
  simp [do_app, ha]
  exact op_res_val hs' type_v_unit

theorem op_opref (hc : ctMap_ok c) (hs : type_s c st s) {v1 : v} {u1 : sem_t}
    (hf : check_freevars 0 [] u1) (h1 : type_v 0 c s v1 u1) :
    op_res c s (Tref u1) (do_app (st, f) .Opref [v1]) := by
  obtain ⟨st', s', n, he, ha, hs', hl⟩ := store_alloc_type_sound' c s st (.Refv v1) (.Ref_t u1) ⟨hc, hs, h1⟩
  simp [do_app, ha]
  exact op_res_val' he hs' (.loc_ref _ _ _ _ _ hf hl)

theorem op_opderef (hc : ctMap_ok c) (hs : type_s c st s) {v1 : v} {t : sem_t}
    (h1 : type_v 0 c s v1 (Tref t)) :
    op_res c s t (do_app (st, f) .Opderef [v1]) := by
  obtain ⟨n, rfl, hl⟩ := canon_Tref h1 hc
  obtain ⟨v2, hlk, hv2⟩ := type_s_Ref hs hl
  simp [do_app, hlk]
  exact op_res_val hs hv2

theorem op_aw8alloc (hc : ctMap_ok c) (he : ctMap_has_exns c) (hs : type_s c st s) {v1 v2 : v}
    (h1 : type_v 0 c s v1 Tint) (h2 : type_v 0 c s v2 Tword8) :
    op_res c s Tword8array (do_app (st, f) .Aw8alloc [v1, v2]) := by
  obtain ⟨n, rfl⟩ := canon_Tint h1 hc
  obtain ⟨w, rfl⟩ := canon_Tword8 h2 hc
  obtain ⟨st', s', l, hste, ha, hs', hl⟩ := store_alloc_type_sound' c s st
    (.W8array (REPLICATE n.natAbs w)) .W8array_t ⟨hc, hs, trivial⟩
  by_cases hn : n < 0
  · simp [do_app, hn]
    exact op_res_sub hs he
  · simp [do_app, hn, ha]
    exact op_res_val' hste hs' (.loc_w8array _ _ _ _ hl)

theorem op_aw8sub (hc : ctMap_ok c) (he : ctMap_has_exns c) (hs : type_s c st s) {v1 v2 : v}
    (h1 : type_v 0 c s v1 Tword8array) (h2 : type_v 0 c s v2 Tint) :
    op_res c s Tword8 (do_app (st, f) .Aw8sub [v1, v2]) := by
  obtain ⟨l, rfl, hl⟩ := canon_Tword8array h1 hc
  obtain ⟨n, rfl⟩ := canon_Tint h2 hc
  obtain ⟨ws, hlk⟩ := type_s_W8 hs hl
  simp only [do_app, hlk]
  split
  · exact op_res_sub hs he
  · split
    · exact op_res_sub hs he
    · exact op_res_val hs (.litv_word8 _ _ _ _)

theorem op_aw8length (hc : ctMap_ok c) (hs : type_s c st s) {v1 : v}
    (h1 : type_v 0 c s v1 Tword8array) :
    op_res c s Tint (do_app (st, f) .Aw8length [v1]) := by
  obtain ⟨l, rfl, hl⟩ := canon_Tword8array h1 hc
  obtain ⟨ws, hlk⟩ := type_s_W8 hs hl
  simp only [do_app, hlk]
  exact op_res_val hs (.litv_int _ _ _ _)

theorem op_aw8update (hc : ctMap_ok c) (he : ctMap_has_exns c) (hs : type_s c st s) {v1 v2 v3 : v}
    (h1 : type_v 0 c s v1 Tword8array) (h2 : type_v 0 c s v2 Tint) (h3 : type_v 0 c s v3 Tword8) :
    op_res c s (Ttup []) (do_app (st, f) .Aw8update [v1, v2, v3]) := by
  obtain ⟨l, rfl, hl⟩ := canon_Tword8array h1 hc
  obtain ⟨n, rfl⟩ := canon_Tint h2 hc
  obtain ⟨w, rfl⟩ := canon_Tword8 h3 hc
  obtain ⟨ws, hlk⟩ := type_s_W8 hs hl
  simp only [do_app, hlk]
  split
  · exact op_res_sub hs he
  · split
    · exact op_res_sub hs he
    · obtain ⟨st', ha, hs'⟩ := store_assign_type_sound' c s st
        (.W8array (LUPDATE w n.natAbs ws)) .W8array_t l ⟨hs, hl, trivial⟩
      rw [ha]
      exact op_res_val hs' type_v_unit

theorem op_copystrstr (hc : ctMap_ok c) (he : ctMap_has_exns c) (hs : type_s c st s) {v1 v2 v3 : v}
    (h1 : type_v 0 c s v1 Tstring) (h2 : type_v 0 c s v2 Tint) (h3 : type_v 0 c s v3 Tint) :
    op_res c s Tstring (do_app (st, f) .CopyStrStr [v1, v2, v3]) := by
  obtain ⟨str, rfl⟩ := canon_Tstring h1 hc
  obtain ⟨n, rfl⟩ := canon_Tint h2 hc
  obtain ⟨m, rfl⟩ := canon_Tint h3 hc
  simp only [do_app]
  split
  · exact op_res_sub hs he
  · exact op_res_val hs (.litv_str _ _ _ _)

theorem op_copystraw8 (hc : ctMap_ok c) (he : ctMap_has_exns c) (hs : type_s c st s) {v1 v2 v3 v4 v5 : v}
    (h1 : type_v 0 c s v1 Tstring) (h2 : type_v 0 c s v2 Tint) (h3 : type_v 0 c s v3 Tint)
    (h4 : type_v 0 c s v4 Tword8array) (h5 : type_v 0 c s v5 Tint) :
    op_res c s (Ttup []) (do_app (st, f) .CopyStrAw8 [v1, v2, v3, v4, v5]) := by
  obtain ⟨str, rfl⟩ := canon_Tstring h1 hc
  obtain ⟨n, rfl⟩ := canon_Tint h2 hc
  obtain ⟨m, rfl⟩ := canon_Tint h3 hc
  obtain ⟨l, rfl, hl⟩ := canon_Tword8array h4 hc
  obtain ⟨k, rfl⟩ := canon_Tint h5 hc
  obtain ⟨ws, hlk⟩ := type_s_W8 hs hl
  simp only [do_app, hlk]
  split
  · exact op_res_sub hs he
  · rename_i cs _
    obtain ⟨st', ha, hs'⟩ := store_assign_type_sound' c s st
        (.W8array (chars_to_ws cs)) .W8array_t l ⟨hs, hl, trivial⟩
    rw [ha]
    exact op_res_val hs' type_v_unit

theorem op_copyaw8str (hc : ctMap_ok c) (he : ctMap_has_exns c) (hs : type_s c st s) {v1 v2 v3 : v}
    (h1 : type_v 0 c s v1 Tword8array) (h2 : type_v 0 c s v2 Tint) (h3 : type_v 0 c s v3 Tint) :
    op_res c s Tstring (do_app (st, f) .CopyAw8Str [v1, v2, v3]) := by
  obtain ⟨l, rfl, hl⟩ := canon_Tword8array h1 hc
  obtain ⟨n, rfl⟩ := canon_Tint h2 hc
  obtain ⟨m, rfl⟩ := canon_Tint h3 hc
  obtain ⟨ws, hlk⟩ := type_s_W8 hs hl
  simp only [do_app, hlk]
  split
  · exact op_res_sub hs he
  · exact op_res_val hs (.litv_str _ _ _ _)

theorem op_copyaw8aw8 (hc : ctMap_ok c) (he : ctMap_has_exns c) (hs : type_s c st s) {v1 v2 v3 v4 v5 : v}
    (h1 : type_v 0 c s v1 Tword8array) (h2 : type_v 0 c s v2 Tint) (h3 : type_v 0 c s v3 Tint)
    (h4 : type_v 0 c s v4 Tword8array) (h5 : type_v 0 c s v5 Tint) :
    op_res c s (Ttup []) (do_app (st, f) .CopyAw8Aw8 [v1, v2, v3, v4, v5]) := by
  obtain ⟨l1, rfl, hl1⟩ := canon_Tword8array h1 hc
  obtain ⟨n, rfl⟩ := canon_Tint h2 hc
  obtain ⟨m, rfl⟩ := canon_Tint h3 hc
  obtain ⟨l, rfl, hl⟩ := canon_Tword8array h4 hc
  obtain ⟨k, rfl⟩ := canon_Tint h5 hc
  obtain ⟨ws1, hlk1⟩ := type_s_W8 hs hl1
  obtain ⟨ws, hlk⟩ := type_s_W8 hs hl
  simp only [do_app, hlk, hlk1]
  split
  · exact op_res_sub hs he
  · rename_i cs _
    obtain ⟨st', ha, hs'⟩ := store_assign_type_sound' c s st
        (.W8array cs) .W8array_t l ⟨hs, hl, trivial⟩
    rw [ha]
    exact op_res_val hs' type_v_unit


theorem cf_Tapp1 {n : Nat} {u : sem_t} {ti : type_ident} (h : check_freevars n [] (.Tapp [u] ti)) :
    check_freevars n [] u := by
  rw [check_freevars_Tapp] at h
  exact h u (by simp)

theorem op_implode (hc : ctMap_ok c) (hl : ctMap_has_lists c) (hs : type_s c st s) {v1 : v}
    (h1 : type_v 0 c s v1 (Tlist Tchar)) :
    op_res c s Tstring (do_app (st, f) .Implode [v1]) := by
  obtain ⟨vs, _, _, h, _⟩ := has_lists_v_to_list' c 0 s Tchar v1 ⟨hc, hl, h1⟩
  obtain ⟨cs, hcs⟩ := h rfl
  simp only [do_app, hcs]
  exact op_res_val hs (.litv_str _ _ _ _)

theorem op_explode (hc : ctMap_ok c) (hl : ctMap_has_lists c) (hs : type_s c st s) {v1 : v}
    (h1 : type_v 0 c s v1 Tstring) :
    op_res c s (Tlist Tchar) (do_app (st, f) .Explode [v1]) := by
  obtain ⟨str, rfl⟩ := canon_Tstring h1 hc
  simp only [do_app]
  refine op_res_val hs (type_v_list_to_v_all hl (by simp [check_freevars, Tchar]) _ ?_)
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨ch, _, rfl⟩ := hx
  exact .litv_char _ _ _ _

theorem op_strsub (hc : ctMap_ok c) (he : ctMap_has_exns c) (hs : type_s c st s) {v1 v2 : v}
    (h1 : type_v 0 c s v1 Tstring) (h2 : type_v 0 c s v2 Tint) :
    op_res c s Tchar (do_app (st, f) .Strsub [v1, v2]) := by
  obtain ⟨str, rfl⟩ := canon_Tstring h1 hc
  obtain ⟨n, rfl⟩ := canon_Tint h2 hc
  simp only [do_app]
  split
  · exact op_res_sub hs he
  · split
    · exact op_res_sub hs he
    · exact op_res_val hs (.litv_char _ _ _ _)

theorem op_strlen (hc : ctMap_ok c) (hs : type_s c st s) {v1 : v}
    (h1 : type_v 0 c s v1 Tstring) :
    op_res c s Tint (do_app (st, f) .Strlen [v1]) := by
  obtain ⟨str, rfl⟩ := canon_Tstring h1 hc
  simp only [do_app]
  exact op_res_val hs (.litv_int _ _ _ _)

theorem op_strcat (hc : ctMap_ok c) (hl : ctMap_has_lists c) (hs : type_s c st s) {v1 : v}
    (h1 : type_v 0 c s v1 (Tlist Tstring)) :
    op_res c s Tstring (do_app (st, f) .Strcat [v1]) := by
  obtain ⟨vs, hvs, _, _, h⟩ := has_lists_v_to_list' c 0 s Tstring v1 ⟨hc, hl, h1⟩
  obtain ⟨str, hstr⟩ := h rfl
  simp only [do_app, hvs, hstr]
  exact op_res_val hs (.litv_str _ _ _ _)

theorem op_vfromlist (hc : ctMap_ok c) (hl : ctMap_has_lists c) (hs : type_s c st s) {v1 : v}
    {u1 : sem_t} (hf : check_freevars 0 [] u1)
    (h1 : type_v 0 c s v1 (Tlist u1)) :
    op_res c s (Tvector u1) (do_app (st, f) .VfromList [v1]) := by
  obtain ⟨vs, hvs, hall, _, _⟩ := has_lists_v_to_list' c 0 s u1 v1 ⟨hc, hl, h1⟩
  simp only [do_app, hvs]
  exact op_res_val hs (.vectorv _ _ _ _ _ hf hall)

theorem op_vsub (hc : ctMap_ok c) (he : ctMap_has_exns c) (hs : type_s c st s) {v1 v2 : v}
    {t : sem_t} (h1 : type_v 0 c s v1 (Tvector t)) (h2 : type_v 0 c s v2 Tint) :
    op_res c s t (do_app (st, f) .Vsub [v1, v2]) := by
  obtain ⟨vs, rfl, hall⟩ := canon_Tvector h1 hc
  obtain ⟨n, rfl⟩ := canon_Tint h2 hc
  simp only [do_app]
  split
  · exact op_res_sub hs he
  · split
    · exact op_res_sub hs he
    · exact op_res_val hs (hall _ (EL_mem (by omega)))

theorem op_vlength (hc : ctMap_ok c) (hs : type_s c st s) {v1 : v}
    {t : sem_t} (h1 : type_v 0 c s v1 (Tvector t)) :
    op_res c s Tint (do_app (st, f) .Vlength [v1]) := by
  obtain ⟨vs, rfl, hall⟩ := canon_Tvector h1 hc
  simp only [do_app]
  exact op_res_val hs (.litv_int _ _ _ _)

theorem op_aalloc (hc : ctMap_ok c) (he : ctMap_has_exns c) (hs : type_s c st s) {v1 v2 : v}
    {u2 : sem_t} (hf : check_freevars 0 [] u2)
    (h1 : type_v 0 c s v1 Tint) (h2 : type_v 0 c s v2 u2) :
    op_res c s (Tarray u2) (do_app (st, f) .Aalloc [v1, v2]) := by
  obtain ⟨n, rfl⟩ := canon_Tint h1 hc
  obtain ⟨st', s', l, hste, ha, hs', hl⟩ := store_alloc_type_sound' c s st
    (.Varray (REPLICATE n.natAbs v2)) (.Varray_t u2) ⟨hc, hs, by
      intro w hw
      simp only [REPLICATE, List.mem_replicate] at hw
      rw [hw.2]; exact h2⟩
  by_cases hn : n < 0
  · simp [do_app, hn]
    exact op_res_sub hs he
  · simp [do_app, hn, ha]
    exact op_res_val' hste hs' (.loc_varray _ _ _ _ _ hf hl)

theorem op_aallocempty (hc : ctMap_ok c) (hs : type_s c st s) {v1 : v}
    {u2 : sem_t} (hf : check_freevars 0 [] u2)
    (h1 : type_v 0 c s v1 (Ttup [])) :
    op_res c s (Tarray u2) (do_app (st, f) .AallocEmpty [v1]) := by
  obtain ⟨vs, rfl, hvs⟩ := canon_Ttup h1 hc
  rw [LIST_REL_nil_right] at hvs
  subst hvs
  obtain ⟨st', s', l, hste, ha, hs', hl⟩ := store_alloc_type_sound' c s st
    (.Varray []) (.Varray_t u2) ⟨hc, hs, by intro w hw; simp at hw⟩
  simp [do_app, ha]
  exact op_res_val' hste hs' (.loc_varray _ _ _ _ _ hf hl)

theorem op_asub (hc : ctMap_ok c) (he : ctMap_has_exns c) (hs : type_s c st s) {v1 v2 : v}
    {t : sem_t} (h1 : type_v 0 c s v1 (Tarray t)) (h2 : type_v 0 c s v2 Tint) :
    op_res c s t (do_app (st, f) .Asub [v1, v2]) := by
  obtain ⟨l, rfl, hl⟩ := canon_Tarray h1 hc
  obtain ⟨n, rfl⟩ := canon_Tint h2 hc
  obtain ⟨vs, hlk, hall⟩ := type_s_Varray hs hl
  simp only [do_app, hlk]
  split
  · exact op_res_sub hs he
  · split
    · exact op_res_sub hs he
    · exact op_res_val hs (hall _ (EL_mem (by omega)))

theorem op_alength (hc : ctMap_ok c) (hs : type_s c st s) {v1 : v}
    {t : sem_t} (h1 : type_v 0 c s v1 (Tarray t)) :
    op_res c s Tint (do_app (st, f) .Alength [v1]) := by
  obtain ⟨l, rfl, hl⟩ := canon_Tarray h1 hc
  obtain ⟨vs, hlk, hall⟩ := type_s_Varray hs hl
  simp only [do_app, hlk]
  exact op_res_val hs (.litv_int _ _ _ _)

theorem op_aupdate (hc : ctMap_ok c) (he : ctMap_has_exns c) (hs : type_s c st s) {v1 v2 v3 : v}
    {u3 : sem_t}
    (h1 : type_v 0 c s v1 (Tarray u3)) (h2 : type_v 0 c s v2 Tint) (h3 : type_v 0 c s v3 u3) :
    op_res c s (Ttup []) (do_app (st, f) .Aupdate [v1, v2, v3]) := by
  obtain ⟨l, rfl, hl⟩ := canon_Tarray h1 hc
  obtain ⟨n, rfl⟩ := canon_Tint h2 hc
  obtain ⟨vs, hlk, hall⟩ := type_s_Varray hs hl
  simp only [do_app, hlk]
  split
  · exact op_res_sub hs he
  · split
    · exact op_res_sub hs he
    · obtain ⟨st', ha, hs'⟩ := store_assign_type_sound' c s st
        (.Varray (LUPDATE v3 n.natAbs vs)) (.Varray_t u3) l ⟨hs, hl, by
          intro w hw
          simp only [LUPDATE] at hw
          rcases List.mem_or_eq_of_mem_set hw with h | h
          · exact hall _ h
          · rw [h]; exact h3⟩
      rw [ha]
      exact op_res_val hs' type_v_unit

theorem op_configgc (hc : ctMap_ok c) (hs : type_s c st s) {v1 v2 : v}
    (h1 : type_v 0 c s v1 Tint) (h2 : type_v 0 c s v2 Tint) :
    op_res c s (Ttup []) (do_app (st, f) .ConfigGC [v1, v2]) := by
  obtain ⟨n, rfl⟩ := canon_Tint h1 hc
  obtain ⟨m, rfl⟩ := canon_Tint h2 hc
  simp only [do_app]
  exact op_res_val hs type_v_unit

theorem op_ffi (hc : ctMap_ok c) (hs : type_s c st s) {v1 v2 : v} {nm : mlstring}
    (h1 : type_v 0 c s v1 Tstring) (h2 : type_v 0 c s v2 Tword8array) :
    op_res c s (Ttup []) (do_app (st, f) (.FFI nm) [v1, v2]) := by
  obtain ⟨str, rfl⟩ := canon_Tstring h1 hc
  obtain ⟨l, rfl, hl⟩ := canon_Tword8array h2 hc
  obtain ⟨ws, hlk⟩ := type_s_W8 hs hl
  simp only [do_app, hlk]
  split
  · rename_i t' ws' _
    obtain ⟨st', ha, hs'⟩ := store_assign_type_sound' c s st
        (.W8array ws') .W8array_t l ⟨hs, hl, trivial⟩
    rw [ha]
    exact op_res_mk (ste_refl s) hs' type_v_unit
  · exact op_res_mk (ste_refl s) hs trivial

theorem op_listappend (hc : ctMap_ok c) (hl : ctMap_has_lists c) (hs : type_s c st s) {v1 v2 : v}
    {u1 : sem_t} (hf : check_freevars 0 [] u1)
    (h1 : type_v 0 c s v1 (Tlist u1)) (h2 : type_v 0 c s v2 (Tlist u1)) :
    op_res c s (Tlist u1) (do_app (st, f) .ListAppend [v1, v2]) := by
  obtain ⟨xs, hxs, hall1, _, _⟩ := has_lists_v_to_list' c 0 s u1 v1 ⟨hc, hl, h1⟩
  obtain ⟨ys, hys, hall2, _, _⟩ := has_lists_v_to_list' c 0 s u1 v2 ⟨hc, hl, h2⟩
  simp only [do_app, hxs, hys]
  refine op_res_val hs (type_v_list_to_v_all hl hf _ ?_)
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact hall1 _ h
  · exact hall2 _ h


macro "canon1" h:ident hc:ident hb:ident : tactic => `(tactic| first
  | (obtain ⟨_, heq⟩ := canon_Tint $h $hc; subst heq)
  | (obtain ⟨_, heq⟩ := canon_Tchar $h $hc; subst heq)
  | (obtain ⟨_, heq⟩ := canon_Tstring $h $hc; subst heq)
  | (obtain ⟨_, heq⟩ := canon_Tword8 $h $hc; subst heq)
  | (obtain ⟨_, heq⟩ := canon_Tword64 $h $hc; subst heq)
  | (obtain ⟨_, heq⟩ := canon_Tdouble $h $hc; subst heq)
  | (obtain ⟨_, heq⟩ := canon_Tbool $h $hc $hb; subst heq))

macro "op_fin" hs:ident he:ident hb:ident : tactic => `(tactic| first
  | exact op_res_val $hs (.litv_int _ _ _ _)
  | exact op_res_val $hs (.litv_char _ _ _ _)
  | exact op_res_val $hs (.litv_str _ _ _ _)
  | exact op_res_val $hs (.litv_word8 _ _ _ _)
  | exact op_res_val $hs (.litv_word64 _ _ _ _)
  | exact op_res_val $hs (.litv_float64 _ _ _ _)
  | exact op_res_val $hs (type_v_Boolv' _ $hb)
  | exact op_res_div $hs $he
  | exact op_res_chr $hs $he)

theorem check_type_ok (hc : ctMap_ok c) (hb : ctMap_has_bools c) {ty : prim_type} {v1 : v}
    (h1 : type_v 0 c s v1 (t_of ty)) : check_type ty v1 = true := by
  cases ty
  case WordT w => cases w <;> canon1 h1 hc hb <;> simp [check_type]
  all_goals (canon1 h1 hc hb; simp [check_type])
  rename_i b; cases b <;> simp [Boolv_beq]

theorem op_test (hc : ctMap_ok c) (hb : ctMap_has_bools c) (hs : type_s c st s) {v1 v2 : v}
    {tst : test} {ty : prim_type} (hsup : supported_test tst ty = true)
    (h1 : type_v 0 c s v1 (t_of ty)) (h2 : type_v 0 c s v2 (t_of ty)) :
    op_res c s Tbool (do_app (st, f) (.Test tst ty) [v1, v2]) := by
  have : ∃ b, do_test tst ty v1 v2 = .Eq_val b := by
    cases tst with
    | Equal =>
      have k1 := check_type_ok hc hb h1
      have k2 := check_type_ok hc hb h2
      have hne := eq_same_type_1 hc h1 h2
      simp only [do_test, k1, k2, Bool.and_self, if_true]
      split
      · exact ⟨_, rfl⟩
      · cases h : do_eq v1 v2 with
        | Eq_type_error => exact absurd h hne
        | Eq_val b => exact ⟨b, rfl⟩
    | Compare cmp =>
      cases ty
      case WordT w =>
        cases w
        · canon1 h1 hc hb; canon1 h2 hc hb; simp [do_test, dest_Litv]
        · simp [supported_test] at hsup
      all_goals first
        | (simp [supported_test] at hsup; done)
        | (canon1 h1 hc hb; canon1 h2 hc hb; simp [do_test, dest_Litv])
    | AltCompare cmp => simp [supported_test] at hsup
  obtain ⟨b, hb'⟩ := this
  simp only [do_app, hb']
  exact op_res_val hs (type_v_Boolv' b hb)

theorem op_fromto (hc : ctMap_ok c) (hb : ctMap_has_bools c) (he : ctMap_has_exns c)
    (hs : type_s c st s) {v1 : v}
    {ty1 ty2 : prim_type} (hsup : supported_conversion ty1 ty2 = true)
    (h1 : type_v 0 c s v1 (t_of ty1)) :
    op_res c s (t_of ty2) (do_app (st, f) (.FromTo ty1 ty2) [v1]) := by
  have k1 := check_type_ok hc hb h1
  simp only [do_app, k1, if_true]
  cases ty1 <;> cases ty2 <;> (try rename_i w; cases w) <;> (try rename_i w; cases w) <;>
    simp [supported_conversion] at hsup <;>
    simp only [do_conversion] <;>
    first
    | op_fin hs he hb
    | (split <;> op_fin hs he hb)
    | (by_cases hi : (the_Litv_IntLit v1 < 0 || the_Litv_IntLit v1 > 255) = true <;>
        simp only [hi] <;> first | op_fin hs he hb | (simp; op_fin hs he hb) | trace_state)


theorem op_arith1 (hc : ctMap_ok c) (hb : ctMap_has_bools c) (he : ctMap_has_exns c)
    (hs : type_s c st s) {v1 : v} {a : arith} {ty : prim_type}
    (hsup : supported_arith a ty = some 1)
    (h1 : type_v 0 c s v1 (t_of ty)) :
    op_res c s (t_of ty) (do_app (st, f) (.Arith a ty) [v1]) := by
  have k1 := check_type_ok hc hb h1
  simp only [do_app, EVERY, List.all_cons, List.all_nil, k1, Bool.and_self, if_true]
  cases ty <;> (try rename_i w; cases w) <;> cases a <;>
    simp [supported_arith] at hsup <;>
    simp only [do_arith, List.map_cons, List.map_nil] <;>
    op_fin hs he hb

theorem op_arith2 (hc : ctMap_ok c) (hb : ctMap_has_bools c) (he : ctMap_has_exns c)
    (hs : type_s c st s) {v1 v2 : v} {a : arith} {ty : prim_type}
    (hsup : supported_arith a ty = some 2)
    (h1 : type_v 0 c s v1 (t_of ty)) (h2 : type_v 0 c s v2 (t_of ty)) :
    op_res c s (t_of ty) (do_app (st, f) (.Arith a ty) [v1, v2]) := by
  have k1 := check_type_ok hc hb h1
  have k2 := check_type_ok hc hb h2
  simp only [do_app, EVERY, List.all_cons, List.all_nil, k1, k2, Bool.and_self, if_true]
  cases ty <;> (try rename_i w; cases w) <;> cases a <;>
    simp [supported_arith] at hsup <;>
    simp only [do_arith, List.map_cons, List.map_nil] <;>
    first
    | op_fin hs he hb
    | (by_cases hi : (the_Litv_IntLit v2 == 0) = true <;>
        simp only [hi] <;> first | op_fin hs he hb | (simp; op_fin hs he hb) | trace_state)

theorem op_arith3 (hc : ctMap_ok c) (hb : ctMap_has_bools c) (he : ctMap_has_exns c)
    (hs : type_s c st s) {v1 v2 v3 : v} {a : arith} {ty : prim_type}
    (hsup : supported_arith a ty = some 3)
    (h1 : type_v 0 c s v1 (t_of ty)) (h2 : type_v 0 c s v2 (t_of ty)) (h3 : type_v 0 c s v3 (t_of ty)) :
    op_res c s (t_of ty) (do_app (st, f) (.Arith a ty) [v1, v2, v3]) := by
  have k1 := check_type_ok hc hb h1
  have k2 := check_type_ok hc hb h2
  have k3 := check_type_ok hc hb h3
  simp only [do_app, EVERY, List.all_cons, List.all_nil, k1, k2, k3, Bool.and_self, if_true]
  cases ty <;> (try rename_i w; cases w) <;> cases a <;>
    simp [supported_arith] at hsup <;>
    simp only [do_arith, List.map_cons, List.map_nil] <;>
    op_fin hs he hb

theorem op_arith (hc : ctMap_ok c) (hb : ctMap_has_bools c) (he : ctMap_has_exns c)
    (hs : type_s c st s) {a : arith} {ty : prim_type} {ts : List sem_t} {ws : List v}
    (hall : ∀ arg, arg ∈ ts → arg = t_of ty)
    (hsup : supported_arith a ty = some ts.length)
    (hws : LIST_REL (type_v 0 c s) ws ts) :
    op_res c s (t_of ty) (do_app (st, f) (.Arith a ty) ws) := by
  rcases ts with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨u, ts⟩⟩⟩⟩
  · exfalso
    cases ty <;> cases a <;> simp [supported_arith] at hsup
  · obtain ⟨v1, rfl, h1⟩ := lr1 hws
    rw [hall x (by simp)] at h1
    exact op_arith1 hc hb he hs hsup h1
  · obtain ⟨v1, v2, rfl, h1, h2⟩ := lr2 hws
    rw [hall x (by simp)] at h1
    rw [hall y (by simp)] at h2
    exact op_arith2 hc hb he hs hsup h1 h2
  · obtain ⟨v1, v2, v3, rfl, h1, h2, h3⟩ := lr3 hws
    rw [hall x (by simp)] at h1
    rw [hall y (by simp)] at h2
    rw [hall z (by simp)] at h3
    exact op_arith3 hc hb he hs hsup h1 h2 h3
  · exfalso
    cases ty <;> cases a <;> simp [supported_arith] at hsup <;> omega


theorem op_type_sound_ws (hg : good_ctMap c) (hs : type_s c st s) {op_ : op} {ts : List sem_t}
    {t : sem_t} {ws : List v}
    (hne : op_ ≠ .Opapp) (hop : type_op op_ ts t) (hf : check_freevars 0 [] t)
    (hws : LIST_REL (type_v 0 c s) ws ts) : op_res c s t (do_app (st, f) op_ ws) := by
  obtain ⟨hc, hb, he, hl⟩ := hg
  rw [type_op_cases_thm] at hop
  rcases hop with ⟨u1, u2, rfl, _⟩ | ⟨sh, n, u1, rfl, rfl, rfl, rfl⟩ | ⟨sh, n, u1, rfl, rfl, rfl, rfl⟩ |
    ⟨u1, u2, rfl, rfl, rfl, rfl⟩ | ⟨a, ty, rfl, hall, rfl, hsup⟩ |
    ⟨ty1, ty2, u1, rfl, rfl, rfl, rfl, hsup⟩ | ⟨tst, ty, u1, u2, rfl, rfl, rfl, rfl, rfl, hsup⟩ |
    ⟨u1, u2, rfl, rfl, rfl, rfl⟩ | ⟨u1, rfl, rfl, rfl⟩ | ⟨u1, rfl, rfl, rfl⟩ |
    ⟨u1, u2, rfl, rfl, rfl, rfl, rfl⟩ | ⟨u1, u2, rfl, rfl, rfl, rfl, rfl⟩ | ⟨u1, rfl, rfl, rfl, rfl⟩ |
    ⟨u1, u2, u3, rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨u1, u2, u3, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨u1, u2, u3, u4, u5, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨u1, u2, u3, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨u1, u2, u3, u4, u5, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨u1, rfl, rfl, rfl, rfl⟩ | ⟨u1, rfl, rfl, rfl, rfl⟩ | ⟨u1, u2, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨u1, rfl, rfl, rfl, rfl⟩ | ⟨u1, rfl, rfl, rfl, rfl⟩ | ⟨u1, ctor, rfl, rfl, rfl, rfl⟩ |
    ⟨u1, u2, rfl, rfl, rfl, rfl⟩ | ⟨u1, ctor, rfl, rfl, rfl, rfl⟩ | ⟨u1, u2, rfl, rfl, rfl, rfl⟩ |
    ⟨u1, rfl, rfl, rfl, u2, rfl⟩ | ⟨u1, u2, rfl, rfl, rfl, rfl⟩ | ⟨u1, ctor, rfl, rfl, rfl, rfl⟩ |
    ⟨u1, u2, u3, rfl, rfl, rfl, rfl, rfl⟩ | ⟨u1, u2, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨nm, u1, u2, rfl, rfl, rfl, rfl, rfl⟩ | ⟨u1, ctor, u2, rfl, rfl, rfl, rfl, rfl⟩
  · exact absurd rfl hne
  · obtain ⟨v1, rfl, h1⟩ := lr1 hws
    exact op_shift8 hc hs h1
  · obtain ⟨v1, rfl, h1⟩ := lr1 hws
    exact op_shift64 hc hs h1
  · obtain ⟨v1, v2, rfl, h1, h2⟩ := lr2 hws
    exact op_equality hc hb hs h1 h2
  · exact op_arith hc hb he hs hall hsup hws
  · obtain ⟨v1, rfl, h1⟩ := lr1 hws
    exact op_fromto hc hb he hs hsup h1
  · obtain ⟨v1, v2, rfl, h1, h2⟩ := lr2 hws
    exact op_test hc hb hs hsup h1 h2
  · obtain ⟨v1, v2, rfl, h1, h2⟩ := lr2 hws
    exact op_opassign hc hs h1 h2
  · obtain ⟨v1, rfl, h1⟩ := lr1 hws
    exact op_opref hc hs (cf_Tapp1 hf) h1
  · obtain ⟨v1, rfl, h1⟩ := lr1 hws
    exact op_opderef hc hs h1
  · obtain ⟨v1, v2, rfl, h1, h2⟩ := lr2 hws
    exact op_aw8alloc hc he hs h1 h2
  · obtain ⟨v1, v2, rfl, h1, h2⟩ := lr2 hws
    exact op_aw8sub hc he hs h1 h2
  · obtain ⟨v1, rfl, h1⟩ := lr1 hws
    exact op_aw8length hc hs h1
  · obtain ⟨v1, v2, v3, rfl, h1, h2, h3⟩ := lr3 hws
    exact op_aw8update hc he hs h1 h2 h3
  · obtain ⟨v1, v2, v3, rfl, h1, h2, h3⟩ := lr3 hws
    exact op_copystrstr hc he hs h1 h2 h3
  · obtain ⟨v1, v2, v3, v4, v5, rfl, h1, h2, h3, h4, h5⟩ := lr5 hws
    exact op_copystraw8 hc he hs h1 h2 h3 h4 h5
  · obtain ⟨v1, v2, v3, rfl, h1, h2, h3⟩ := lr3 hws
    exact op_copyaw8str hc he hs h1 h2 h3
  · obtain ⟨v1, v2, v3, v4, v5, rfl, h1, h2, h3, h4, h5⟩ := lr5 hws
    exact op_copyaw8aw8 hc he hs h1 h2 h3 h4 h5
  · obtain ⟨v1, rfl, h1⟩ := lr1 hws
    exact op_implode hc hl hs h1
  · obtain ⟨v1, rfl, h1⟩ := lr1 hws
    exact op_explode hc hl hs h1
  · obtain ⟨v1, v2, rfl, h1, h2⟩ := lr2 hws
    exact op_strsub hc he hs h1 h2
  · obtain ⟨v1, rfl, h1⟩ := lr1 hws
    exact op_strlen hc hs h1
  · obtain ⟨v1, rfl, h1⟩ := lr1 hws
    exact op_strcat hc hl hs h1
  · obtain ⟨v1, rfl, h1⟩ := lr1 hws
    exact op_vfromlist hc hl hs (cf_Tapp1 hf) h1
  · obtain ⟨v1, v2, rfl, h1, h2⟩ := lr2 hws
    exact op_vsub hc he hs h1 h2
  · obtain ⟨v1, rfl, h1⟩ := lr1 hws
    exact op_vlength hc hs h1
  · obtain ⟨v1, v2, rfl, h1, h2⟩ := lr2 hws
    exact op_aalloc hc he hs (cf_Tapp1 hf) h1 h2
  · obtain ⟨v1, rfl, h1⟩ := lr1 hws
    exact op_aallocempty hc hs (cf_Tapp1 hf) h1
  · obtain ⟨v1, v2, rfl, h1, h2⟩ := lr2 hws
    exact op_asub hc he hs h1 h2
  · obtain ⟨v1, rfl, h1⟩ := lr1 hws
    exact op_alength hc hs h1
  · obtain ⟨v1, v2, v3, rfl, h1, h2, h3⟩ := lr3 hws
    exact op_aupdate hc he hs h1 h2 h3
  · obtain ⟨v1, v2, rfl, h1, h2⟩ := lr2 hws
    exact op_configgc hc hs h1 h2
  · obtain ⟨v1, v2, rfl, h1, h2⟩ := lr2 hws
    exact op_ffi hc hs h1 h2
  · obtain ⟨v1, v2, rfl, h1, h2⟩ := lr2 hws
    exact op_listappend hc hl hs (cf_Tapp1 hf) h1 h2

end

theorem op_type_sound' :
    ∀ {ffi : Type} (ctMap_ : ctMap) (tenvS : tenv_store) (vs : List v)
      (op_ : op) (ts : List sem_t) (t : sem_t) (store_ : List (store_v v))
      (ffi_ : ffi_state ffi),
      good_ctMap ctMap_ ∧
      op_ ≠ .Opapp ∧
      type_s ctMap_ store_ tenvS ∧
      type_op op_ ts t ∧
      check_freevars 0 [] t ∧
      LIST_REL (type_v 0 ctMap_ tenvS) vs ts.reverse →
      ∃ (tenvS' : tenv_store) (store' : List (store_v v)) (ffi' : ffi_state ffi)
        (r : result v v),
        ste tenvS tenvS' ∧
        type_s ctMap_ store' tenvS' ∧
        do_app (store_, ffi_) op_ vs.reverse = some ((store', ffi'), r) ∧
        match r with
        | .Rval val_ => type_v 0 ctMap_ tenvS' val_ t
        | .Rerr (.Rraise val_) => type_v 0 ctMap_ tenvS' val_ Texn
        | .Rerr (.Rabort (.Rffi_error _)) => True
        | .Rerr (.Rabort _) => False := by
  intro ffi c s vs op_ ts t st f ⟨hg, hne, hs, hop, hf, hvs⟩
  have hws : LIST_REL (type_v 0 c s) vs.reverse ts := by
    have := LIST_REL_reverse hvs
    simpa using this
  exact op_type_sound_ws hg hs hne hop hf hws

end DAux
