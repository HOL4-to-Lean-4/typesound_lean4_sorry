import LeanTypeSound.DAux3
open HOL4
namespace DAux

theorem fcd {ffi : Type} (st : cml_state ffi) (env : sem_env) (ds : List dec) :
    fix_clock st (evaluate_decs st env ds) = evaluate_decs st env ds :=
  (fix_clock_evaluate st env [] ds).2

theorem evd_nil {ffi : Type} (st : cml_state ffi) (env : sem_env) :
    evaluate_decs st env [] = (st, .Rval (.mk nsEmpty nsEmpty)) := by
  rw [evaluate_decs]

theorem evd_dlet {ffi : Type} (st : cml_state ffi) (env : sem_env) (l : locs) (p : pat) (e : exp) :
    evaluate_decs st env [.Dlet l p e] =
    (if ALL_DISTINCT (pat_bindings p []) && every_exp (one_con_check env.c) e then
      match evaluate st env [e] with
      | (st', .Rval v') =>
        (st', match pmatch env.c st'.refs p v'.head! [] with
          | .No_match => .Rerr (.Rraise bind_exn_v)
          | .Match_type_error => .Rerr (.Rabort .Rtype_error)
          | .Match new_vals => .Rval (.mk (alist_to_ns new_vals) nsEmpty))
      | (st', .Rerr err) => (st', .Rerr err)
    else (st, .Rerr (.Rabort .Rtype_error))) := by
  rw [evaluate_decs]; rfl

theorem evd_dletrec {ffi : Type} (st : cml_state ffi) (env : sem_env) (l : locs)
    (funs : List (varN × varN × exp)) :
    evaluate_decs st env [.Dletrec l funs] =
    (st,
     if ALL_DISTINCT (funs.map fun (x, _, _) => x) &&
        funs.all fun (_, _, e) => every_exp (one_con_check env.c) e then
       .Rval (.mk (build_rec_env funs env nsEmpty) nsEmpty)
     else .Rerr (.Rabort .Rtype_error)) := by
  rw [evaluate_decs]

theorem evd_dtype {ffi : Type} (st : cml_state ffi) (env : sem_env) (l : locs) (tds : type_def) :
    evaluate_decs st env [.Dtype l tds] =
    (if tds.all check_dup_ctors then
      ({ st with next_type_stamp := st.next_type_stamp + tds.length },
       .Rval (.mk nsEmpty (build_tdefs st.next_type_stamp tds)))
    else (st, .Rerr (.Rabort .Rtype_error))) := by
  rw [evaluate_decs]

theorem evd_dtabbrev {ffi : Type} (st : cml_state ffi) (env : sem_env) (l : locs)
    (tvs : List tvarN) (tn : typeN) (t : ast_t) :
    evaluate_decs st env [.Dtabbrev l tvs tn t] = (st, .Rval (.mk nsEmpty nsEmpty)) := by
  rw [evaluate_decs]

theorem evd_dexn {ffi : Type} (st : cml_state ffi) (env : sem_env) (l : locs)
    (cn : conN) (ts : List ast_t) :
    evaluate_decs st env [.Dexn l cn ts] =
    ({ st with next_exn_stamp := st.next_exn_stamp + 1 },
     .Rval (.mk nsEmpty (nsSing cn (ts.length, .ExnStamp st.next_exn_stamp)))) := by
  rw [evaluate_decs]

theorem evd_dmod {ffi : Type} (st : cml_state ffi) (env : sem_env) (mn : modN) (ds' : List dec) :
    evaluate_decs st env [.Dmod mn ds'] =
    (match evaluate_decs st env ds' with
    | (st', r) =>
      (st', match r with
        | .Rval env' => .Rval (.mk (nsLift mn env'.v_) (nsLift mn env'.c))
        | .Rerr err => .Rerr err)) := by
  rw [evaluate_decs]; rfl

theorem evd_dlocal {ffi : Type} (st : cml_state ffi) (env : sem_env) (lds ds' : List dec) :
    evaluate_decs st env [.Dlocal lds ds'] =
    (match evaluate_decs st env lds with
    | (st1, .Rval env1) => evaluate_decs st1 (extend_dec_env env1 env) ds'
    | (st1, .Rerr e) => (st1, .Rerr e)) := by
  rw [evaluate_decs]
  split <;> rename_i heq <;> rw [fcd] at heq <;> rw [heq]

theorem evd_cons {ffi : Type} (st : cml_state ffi) (env : sem_env) (d1 d2 : dec) (ds' : List dec) :
    evaluate_decs st env (d1 :: d2 :: ds') =
    (match evaluate_decs st env [d1] with
    | (st1, .Rval env1) =>
      match evaluate_decs st1 (extend_dec_env env1 env) (d2 :: ds') with
      | (st2, r) => (st2, combine_dec_result env1 r)
    | (st1, .Rerr e) => (st1, .Rerr e)) := by
  rw [evaluate_decs]
  split <;> rename_i heq <;> rw [fcd] at heq <;> rw [heq] <;> rfl

theorem FUPDATE_LIST_cons {α β : Type} [BEq α] (m : Finmap α β) (a : α × β) (l : List (α × β)) :
    Finmap.FUPDATE_LIST m (a :: l) = Finmap.FUPDATE_LIST (Finmap.FUPDATE m a) l := rfl

theorem FUPDATE_LIST_append {α β : Type} [BEq α] (m : Finmap α β) (l1 l2 : List (α × β)) :
    Finmap.FUPDATE_LIST m (l1 ++ l2) = Finmap.FUPDATE_LIST (Finmap.FUPDATE_LIST m l1) l2 := by
  simp [Finmap.FUPDATE_LIST, List.foldl_append]

theorem FUPDATE_LIST_cases {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ (l : List (α × β)) (m : Finmap α β) (k : α) (x : β),
      Finmap.FUPDATE_LIST m l k = some x → m k = some x ∨ (k, x) ∈ l := by
  intro l
  induction l with
  | nil => intro m k x h; exact .inl h
  | cons a l ih =>
    intro m k x h
    rw [FUPDATE_LIST_cons] at h
    rcases ih _ k x h with h1 | h1
    · simp only [Finmap.FUPDATE] at h1
      split at h1
      · rename_i hk
        have hk' : k = a.1 := by simpa using hk
        simp only [Option.some.injEq] at h1
        right
        rw [hk', ← h1]
        simp
      · exact .inl h1
    · exact .inr (by simp [h1])

theorem FUPDATE_LIST_notin {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ (l : List (α × β)) (m : Finmap α β) (k : α),
      (∀ p, p ∈ l → p.1 ≠ k) → Finmap.FUPDATE_LIST m l k = m k := by
  intro l
  induction l with
  | nil => intro m k _; rfl
  | cons a l ih =>
    intro m k h
    rw [FUPDATE_LIST_cons, ih _ k (fun p hp => h p (by simp [hp]))]
    have : a.1 ≠ k := h a (by simp)
    simp only [Finmap.FUPDATE]
    rw [if_neg]
    intro hk
    have hk' : k = a.1 := by simpa using hk
    exact this hk'.symm

theorem LIST_REL_refl_mem {α : Type} {R : α → α → Prop} :
    ∀ (l : List α), (∀ x, x ∈ l → R x x) → LIST_REL R l l := by
  intro l
  induction l with
  | nil => intro _; exact .nil
  | cons a l ih =>
    intro h
    exact .cons _ _ _ _ (h a (by simp)) (ih (fun x hx => h x (by simp [hx])))

theorem lookup_ctors (tenvT : tenv_abbrev) (tvs : List tvarN) (id_ : type_ident) (next : Nat) :
    ∀ (ctors : List (conN × List ast_t)) (m : ctMap) (cn : conN) (ts : List ast_t),
      ALL_DISTINCT (ctors.map Prod.fst) = true → (cn, ts) ∈ ctors →
      Finmap.FUPDATE_LIST m (ctors.map fun (p : conN × List ast_t) =>
        (stamp.TypeStamp p.1 next, (tvs, p.2.map (type_name_subst tenvT), id_)))
        (stamp.TypeStamp cn next) = some (tvs, ts.map (type_name_subst tenvT), id_) := by
  intro ctors
  induction ctors with
  | nil => intro m cn ts _ h; simp at h
  | cons a rest ih =>
    intro m cn ts hd hmem
    simp only [List.map_cons, ALL_DISTINCT, Bool.and_eq_true, Bool.not_eq_true',
      List.any_eq_false] at hd
    rw [List.map_cons, FUPDATE_LIST_cons]
    rcases List.mem_cons.mp hmem with h | h
    · subst h
      rw [FUPDATE_LIST_notin]
      · simp [Finmap.FUPDATE]
      · intro p hp
        simp only [List.mem_map] at hp
        obtain ⟨q, hq, rfl⟩ := hp
        intro heq
        simp only [stamp.TypeStamp.injEq, and_true] at heq
        have := hd.1 q.1 (by simp only [List.mem_map]; exact ⟨q, hq, rfl⟩)
        simp [heq] at this
    · exact ih _ cn ts hd.2 h

theorem build_tdefs_build_tenv' :
    ∀ (tenvT : tenv_abbrev) (tds : type_def) (tids : List type_ident)
      (next : Nat) (ctMap_ : ctMap),
      EVERY (fun (p : List tvarN × typeN × List (conN × List ast_t)) =>
        ALL_DISTINCT (p.2.2.map Prod.fst)) tds ∧
      tds.length = tids.length →
      nsAll2
        (type_ctor (Finmap.FUPDATE_LIST ctMap_ (type_def_to_ctMap tenvT next tds tids).reverse))
        (build_tdefs next tds : env_ctor)
        (build_ctor_tenv tenvT tds tids) := by
  intro tenvT tds
  induction tds with
  | nil =>
    intro tids next c ⟨_, hlen⟩
    cases tids with
    | nil =>
      simp only [type_def_to_ctMap, build_tdefs, build_ctor_tenv, alist_to_ns_nil]
      exact nsAll2_nsEmpty _
    | cons a l => simp at hlen
  | cons td tds ih =>
    intro tids next c ⟨hev, hlen⟩
    obtain ⟨tvs, tn, ctors⟩ := td
    cases tids with
    | nil => simp at hlen
    | cons id_ ids =>
      have hlen' : tds.length = ids.length := by simpa using hlen
      simp only [EVERY, List.all_cons, Bool.and_eq_true] at hev
      simp only [type_def_to_ctMap, build_tdefs, build_ctor_tenv, List.reverse_append,
        List.reverse_reverse, FUPDATE_LIST_append]
      apply nsAll2_nsAppend
      refine ⟨ih ids (next + 1) _ ⟨hev.2, hlen'⟩, ?_⟩
      apply nsAll2_alist_to_ns
      apply LIST_REL_reverse
      simp only [build_constrs]
      rw [LIST_REL_map_left, LIST_REL_map_right]
      apply LIST_REL_refl_mem
      intro ⟨cn, ts⟩ hmem
      refine ⟨rfl, ?_, by simp⟩
      show Finmap.FUPDATE_LIST _ _ (stamp.TypeStamp cn next) = _
      rw [FUPDATE_LIST_notin]
      · exact lookup_ctors tenvT tvs id_ next ctors c cn ts hev.1 hmem
      · intro p hp heq
        obtain ⟨cn', i, h1, h2, _⟩ := mem_type_def_to_ctMap tenvT (next + 1) tds ids p.1 p.2
          ⟨by simpa using hp, hlen'⟩
        rw [h1] at heq
        simp only [stamp.TypeStamp.injEq] at heq
        omega

def dres (c' : ctMap) (s' : tenv_store) {ffi : Type} (st' : cml_state ffi) (env : sem_env)
    (tenv tenv' : type_env) : result sem_env v → Prop
  | .Rval env' =>
    type_all_env c' s' env' tenv' ∧
    type_sound_invariant st' (extend_dec_env env' env) c' s' ∅ (extend_dec_tenv tenv' tenv)
  | .Rerr (.Rraise err_v) =>
    type_v 0 c' s' err_v Texn ∧ type_sound_invariant st' env c' s' ∅ tenv
  | .Rerr (.Rabort .Rtype_error) => False
  | .Rerr (.Rabort .Rtimeout_error) => True
  | .Rerr (.Rabort (.Rffi_error _)) => True

def DR {ffi : Type} (st' : cml_state ffi) (env : sem_env) (c : ctMap) (s : tenv_store)
    (tids : Set type_ident) (tenv tenv' : type_env) (r : result sem_env v) : Prop :=
  ∃ (c' : ctMap) (s' : tenv_store),
    weakCT c' c ∧
    Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) c') \
      Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) c) ⊆ tids ∧
    ste s s' ∧ dres c' s' st' env tenv tenv' r

theorem frange_sub_refl (c : ctMap) (tids : Set type_ident) :
    Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) c) \
      Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) c) ⊆ tids :=
  fun _ hx => (hx.2 hx.1).elim

theorem consistent_stamps {ffi : Type} {st st1 : cml_state ffi} {tids : Set type_ident} {c : ctMap}
    (h : consistent_ctMap st tids c) (hn1 : st1.next_type_stamp = st.next_type_stamp)
    (hn2 : st1.next_exn_stamp = st.next_exn_stamp) : consistent_ctMap st1 tids c :=
  ⟨h.1, fun cn id_ => by rw [hn1, hn2]; exact h.2 cn id_⟩

theorem type_all_env_ste {c : ctMap} {s s' : tenv_store} {env : sem_env} {tenv : type_env}
    (h : type_all_env c s env tenv) (he : ste s s') : type_all_env c s' env tenv :=
  type_all_env_weakening c s tenv env c s' ⟨weakCT_refl c, ste_weakS he, h⟩

theorem type_all_env_weak {c c' : ctMap} {s s' : tenv_store} {env : sem_env} {tenv : type_env}
    (h : type_all_env c s env tenv) (hw : weakCT c' c) (he : ste s s') :
    type_all_env c' s' env tenv :=
  type_all_env_weakening c s tenv env c' s' ⟨hw, ste_weakS he, h⟩

theorem type_all_env_empty (c : ctMap) (s : tenv_store) :
    type_all_env c s (.mk nsEmpty nsEmpty) { v := nsEmpty, c := nsEmpty, t := nsEmpty } :=
  ⟨nsAll2_nsEmpty _, nsAll2_nsEmpty _⟩

section
variable {ffi : Type}

theorem pd_dlet {st st' : cml_state ffi} {env : sem_env} {c : ctMap} {s : tenv_store}
    {tenv : type_env} {l : locs} {p : pat} {e : exp} {tvs : Nat} {t : sem_t}
    {bindings : List (varN × sem_t)} {r : result sem_env v}
    (hval : tvs ≠ 0 → is_value e = true) (hd : ALL_DISTINCT (pat_bindings p []) = true)
    (hp : type_p tvs tenv p t bindings) (he : type_e tenv (bind_tvar tvs .Empty) e t)
    (htok' : tenv_ok (extend_dec_tenv
      { v := alist_to_ns (tenv_add_tvs tvs bindings), c := nsEmpty, t := nsEmpty } tenv))
    (heval : evaluate_decs st env [.Dlet l p e] = (st', r))
    (hinv : type_sound_invariant st env c s ∅ tenv) :
    DR st' env c s ∅ tenv
      { v := alist_to_ns (tenv_add_tvs tvs bindings), c := nsEmpty, t := nsEmpty } r := by
  obtain ⟨htok, hg, hcons, henv, hs⟩ := hinv
  have hall : nsAll2 (type_ctor c) env.c tenv.c := henv.1
  have hchk := con_check1 c env.c tenv hall he
  rw [evd_dlet, hd, hchk] at heval
  simp only [Bool.and_self, if_true] at heval
  cases h1 : evaluate st env [e] with
  | mk st1 r1 =>
    rw [h1] at heval
    obtain ⟨s1, hs1, hste, hn1, hn2, hres⟩ :=
      (es_main hg st.clock (sizeOf [e])).1 st env [e] rfl rfl r1 st1 tenv .Empty [t] tvs s h1
        ⟨htok, by simp [tenv_val_exp_ok], rfl, henv⟩ hs
        (by intro h; simp [EVERY, hval h]) (type_es_sing he)
    have henv1 : type_all_env c s1 env tenv := type_all_env_ste henv hste
    have hcons1 := consistent_stamps hcons hn1 hn2
    have hinv1 : type_sound_invariant st1 env c s1 ∅ tenv := ⟨htok, hg, hcons1, henv1, hs1⟩
    cases r1 with
    | Rval vs =>
      obtain ⟨v1, rfl, hv1⟩ := lr1 hres
      have hh : ([v1] : List v).head! = v1 := rfl
      simp only [hh] at heval
      rcases pat_sound1 hp env.c st1.refs v1 [] c [] s1 hg.1 hall hv1 hs1 .nil with
        hno | ⟨bs, hm, hrel⟩
      · rw [hno] at heval
        cases heval
        exact ⟨c, s1, weakCT_refl c, frange_sub_refl c _, hste,
          (type_v_exn' 0 c s1 hg.2.2.1).2.2.1, hinv1⟩
      · rw [hm] at heval
        cases heval
        have htae : type_all_env c s1 (.mk (alist_to_ns bs) nsEmpty)
            { v := alist_to_ns (tenv_add_tvs tvs bindings), c := nsEmpty, t := nsEmpty } := by
          refine ⟨nsAll2_nsEmpty _, ?_⟩
          apply nsAll2_alist_to_ns
          simp only [tenv_add_tvs]
          rw [LIST_REL_map_right]
          have hrel' : LIST_REL (bindR tvs c s1) bs bindings := by simpa using hrel
          exact LIST_REL_mono (fun a b hab => hab) hrel'
        exact ⟨c, s1, weakCT_refl c, frange_sub_refl c _, hste, htae,
          htok', hg, hcons1, type_all_env_extend' c s1 _ env _ tenv ⟨htae, henv1⟩, hs1⟩
    | Rerr err =>
      cases heval
      refine ⟨c, s1, weakCT_refl c, frange_sub_refl c _, hste, ?_⟩
      cases err with
      | Rraise x => exact ⟨hres, hinv1⟩
      | Rabort a => cases a <;> first | exact hres | exact trivial

theorem pd_dletrec {st st' : cml_state ffi} {env : sem_env} {c : ctMap} {s : tenv_store}
    {tenv : type_env} {l : locs} {funs : List (varN × varN × exp)} {tvs : Nat}
    {bindings : List (varN × sem_t)} {r : result sem_env v}
    (hfuns : type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs .Empty)) funs bindings)
    (htok' : tenv_ok (extend_dec_tenv
      { v := alist_to_ns (tenv_add_tvs tvs bindings), c := nsEmpty, t := nsEmpty } tenv))
    (heval : evaluate_decs st env [.Dletrec l funs] = (st', r))
    (hinv : type_sound_invariant st env c s ∅ tenv) :
    DR st' env c s ∅ tenv
      { v := alist_to_ns (tenv_add_tvs tvs bindings), c := nsEmpty, t := nsEmpty } r := by
  obtain ⟨htok, hg, hcons, henv, hs⟩ := hinv
  have hall : nsAll2 (type_ctor c) env.c tenv.c := henv.1
  have hd := type_funs_distinct _ _ _ _ hfuns
  have hchk := con_check3 c env.c tenv hall hfuns
  have hcond : (ALL_DISTINCT (funs.map fun (x, _, _) => x) &&
      funs.all fun (_, _, e) => every_exp (one_con_check env.c) e) = true := by
    rw [Bool.and_eq_true]
    exact ⟨hd, hchk⟩
  rw [evd_dletrec, if_pos hcond] at heval
  cases heval
  have hrel := type_recfun_env' funs c s tvs tenv .Empty env bindings
    ⟨htok, henv, by simp [tenv_val_exp_ok], rfl, hfuns, hd⟩
  have htae : type_all_env c s (.mk (build_rec_env funs env nsEmpty) nsEmpty)
      { v := alist_to_ns (tenv_add_tvs tvs bindings), c := nsEmpty, t := nsEmpty } := by
    refine ⟨nsAll2_nsEmpty _, ?_⟩
    show nsAll2 _ (build_rec_env funs env nsEmpty) (alist_to_ns (tenv_add_tvs tvs bindings))
    rw [build_rec_env_merge, (nsAppend_nsEmpty _).1]
    apply nsAll2_alist_to_ns
    exact hrel
  exact ⟨c, s, weakCT_refl c, frange_sub_refl c _, ste_refl s, htae,
    htok', hg, hcons, type_all_env_extend' c s _ env _ tenv ⟨htae, henv⟩, hs⟩

theorem pd_dtabbrev {st st' : cml_state ffi} {env : sem_env} {c : ctMap} {s : tenv_store}
    {tenv : type_env} {l : locs} {tvs : List tvarN} {tn : typeN} {t : ast_t} {x : tenv_abbrev}
    {r : result sem_env v}
    (htok' : tenv_ok (extend_dec_tenv { v := nsEmpty, c := nsEmpty, t := x } tenv))
    (heval : evaluate_decs st env [.Dtabbrev l tvs tn t] = (st', r))
    (hinv : type_sound_invariant st env c s ∅ tenv) :
    DR st' env c s ∅ tenv { v := nsEmpty, c := nsEmpty, t := x } r := by
  obtain ⟨htok, hg, hcons, henv, hs⟩ := hinv
  rw [evd_dtabbrev] at heval
  cases heval
  have htae : type_all_env c s (.mk nsEmpty nsEmpty) { v := nsEmpty, c := nsEmpty, t := x } :=
    ⟨nsAll2_nsEmpty _, nsAll2_nsEmpty _⟩
  exact ⟨c, s, weakCT_refl c, frange_sub_refl c _, ste_refl s, htae,
    htok', hg, hcons, type_all_env_extend' c s _ env _ tenv ⟨htae, henv⟩, hs⟩

theorem pds_nil {st st' : cml_state ffi} {env : sem_env} {c : ctMap} {s : tenv_store}
    {tenv : type_env} {r : result sem_env v}
    (heval : evaluate_decs st env [] = (st', r))
    (hinv : type_sound_invariant st env c s ∅ tenv) :
    DR st' env c s ∅ tenv { v := nsEmpty, c := nsEmpty, t := nsEmpty } r := by
  obtain ⟨htok, hg, hcons, henv, hs⟩ := hinv
  rw [evd_nil] at heval
  cases heval
  have htae := type_all_env_empty c s
  exact ⟨c, s, weakCT_refl c, frange_sub_refl c _, ste_refl s, htae,
    extend_dec_tenv_ok _ _ ⟨tenv_ok_empty, htok⟩, hg, hcons,
    type_all_env_extend' c s _ env _ tenv ⟨htae, henv⟩, hs⟩

end

section
variable {ffi : Type}

theorem exn_not_prim {c : ctMap} (hc : ctMap_ok c) {k : stamp} {tvs : List tvarN}
    {ts : List sem_t} (h : c k = some (tvs, ts, Texn_num)) : ∃ m, k = .ExnStamp m := by
  cases k with
  | ExnStamp m => exact ⟨m, rfl⟩
  | TypeStamp cn x =>
    exact absurd (by decide : prim_type_nums.elem Texn_num = true) (hc.2.2.1 cn x tvs ts _ h)

theorem pd_dexn {st st' : cml_state ffi} {env : sem_env} {c : ctMap} {s : tenv_store}
    {tenv : type_env} {l : locs} {cn : conN} {ts : List ast_t} {r : result sem_env v}
    (hf : ∀ t', t' ∈ ts → check_freevars_ast [] t' = true)
    (hn : ∀ t', t' ∈ ts → check_type_names tenv.t t' = true)
    (htok' : tenv_ok (extend_dec_tenv
      { v := nsEmpty, c := nsSing cn ([], ts.map (type_name_subst tenv.t), Texn_num),
        t := nsEmpty } tenv))
    (heval : evaluate_decs st env [.Dexn l cn ts] = (st', r))
    (hinv : type_sound_invariant st env c s ∅ tenv) :
    DR st' env c s ∅ tenv
      { v := nsEmpty, c := nsSing cn ([], ts.map (type_name_subst tenv.t), Texn_num),
        t := nsEmpty } r := by
  obtain ⟨htok, hg, hcons, henv, hs⟩ := hinv
  obtain ⟨hc, hb, hex, hl⟩ := hg
  rw [evd_dexn] at heval
  cases heval
  let n := st.next_exn_stamp
  let newv : List tvarN × List sem_t × type_ident :=
    ([], ts.map (type_name_subst tenv.t), Texn_num)
  let c' : ctMap := Finmap.FUPDATE c (stamp.ExnStamp n, newv)
  have hc' : ∀ k, c' k = if k == stamp.ExnStamp n then some newv else c k := fun k => rfl
  have hnot : c (stamp.ExnStamp n) = none := by
    cases h : c (stamp.ExnStamp n) with
    | none => rfl
    | some x =>
      have := (hcons.2 cn n).2 (by show (c (stamp.ExnStamp n)).isSome = true; simp [h])
      exact absurd this (Nat.lt_irrefl _)
  have hold : ∀ k x, c k = some x → c' k = some x := by
    intro k x h
    rw [hc']
    split
    · rename_i hk
      have hk' : k = stamp.ExnStamp n := by simpa using hk
      rw [hk', hnot] at h
      simp at h
    · exact h
  have hty : ∀ cn' i, c' (stamp.TypeStamp cn' i) = c (stamp.TypeStamp cn' i) := by
    intro cn' i
    rw [hc']
    simp
  have hnew : c' (stamp.ExnStamp n) = some newv := by
    rw [hc']; simp
  have hcases : ∀ k x, c' k = some x → (k = stamp.ExnStamp n ∧ x = newv) ∨ c k = some x := by
    intro k x h
    rw [hc'] at h
    split at h
    · rename_i hk
      have hk' : k = stamp.ExnStamp n := by simpa using hk
      simp only [Option.some.injEq] at h
      exact .inl ⟨hk', h.symm⟩
    · exact .inr h
  have hw : weakCT c' c := hold
  have hfr : Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) c') \
      Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) c) ⊆ (∅ : Set type_ident) := by
    intro x ⟨⟨a, ha⟩, hx2⟩
    exfalso
    apply hx2
    simp only [Finmap.o_f] at ha
    cases h : c' a with
    | none => rw [h] at ha; simp at ha
    | some y =>
      rw [h] at ha
      simp only [Option.map_some, Option.some.injEq] at ha
      rcases hcases a y h with ⟨_, rfl⟩ | h2
      · refine ⟨bind_stamp, ?_⟩
        have := hex.1
        simp only [Finmap.FLOOKUP] at this
        simp only [Finmap.o_f, this, Option.map_some]
        rw [← ha]
      · exact ⟨a, by simp only [Finmap.o_f, h2, Option.map_some, ha]⟩
  have hc'ok : ctMap_ok c' := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k val_ h
      rcases hcases k val_ h with ⟨_, rfl⟩ | h2
      · show EVERY (check_freevars 0 []) (ts.map (type_name_subst tenv.t)) = true
        rw [EVERY_iff]
        intro x hx
        simp only [List.mem_map] at hx
        obtain ⟨t', ht', rfl⟩ := hx
        exact check_freevars_type_name_subst [] t' 0 tenv.t ⟨htok.2.2, hn t' ht', hf t' ht'⟩
      · exact hc.1 k val_ h2
    · intro ex tvs ts' ti h
      rcases hcases _ _ h with ⟨_, h2⟩ | h2
      · simp only [newv, Prod.mk.injEq] at h2
        exact ⟨h2.1, h2.2.2⟩
      · exact hc.2.1 ex tvs ts' ti h2
    · intro cn' x tvs ts' ti h
      have h' : c (stamp.TypeStamp cn' x) = some (tvs, ts', ti) := by
        rw [← hty]; exact h
      exact hc.2.2.1 cn' x tvs ts' ti h'
    · intro stamp1 tvs1 ts1 ti stamp2 tvs2 ts2 ⟨h1, h2⟩
      rcases hcases _ _ h1 with ⟨rfl, e1⟩ | o1 <;> rcases hcases _ _ h2 with ⟨rfl, e2⟩ | o2
      · rfl
      · simp only [newv, Prod.mk.injEq] at e1
        obtain ⟨_, _, rfl⟩ := e1
        obtain ⟨m, rfl⟩ := exn_not_prim hc o2
        rfl
      · simp only [newv, Prod.mk.injEq] at e2
        obtain ⟨_, _, rfl⟩ := e2
        obtain ⟨m, rfl⟩ := exn_not_prim hc o1
        rfl
      · exact hc.2.2.2 stamp1 tvs1 ts1 ti stamp2 tvs2 ts2 ⟨o1, o2⟩
  have hg' : good_ctMap c' := by
    refine ⟨hc'ok, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
    · exact hold _ _ hb.1
    · exact hold _ _ hb.2.1
    · intro cn' h; show c' _ = none; rw [hty]; exact hb.2.2 cn' h
    · exact hold _ _ hex.1
    · exact hold _ _ hex.2.1
    · exact hold _ _ hex.2.2.1
    · exact hold _ _ hex.2.2.2
    · exact hold _ _ hl.1
    · exact hold _ _ hl.2.1
    · intro cn' h; show c' _ = none; rw [hty]; exact hl.2.2 cn' h
  have hcons' : consistent_ctMap { st with next_exn_stamp := st.next_exn_stamp + 1 } ∅ c' := by
    refine ⟨fun x hx => hx.1, fun cn' id_ => ⟨?_, ?_⟩⟩
    · intro h
      have h' : (c (stamp.TypeStamp cn' id_)).isSome = true := by rw [← hty]; exact h
      exact (hcons.2 cn' id_).1 h'
    · intro h
      have h' : (c' (stamp.ExnStamp id_)).isSome = true := h
      show id_ < st.next_exn_stamp + 1
      cases h2 : c' (stamp.ExnStamp id_) with
      | none => rw [h2] at h'; simp at h'
      | some y =>
        rcases hcases _ _ h2 with ⟨e, _⟩ | o
        · simp only [stamp.ExnStamp.injEq] at e
          omega
        · have := (hcons.2 cn' id_).2 (by show (c (stamp.ExnStamp id_)).isSome = true; simp [o])
          omega
  have hs' : type_s c' st.refs s := type_s_weakening c s st.refs c' ⟨hs, hw⟩
  have henv' : type_all_env c' s env tenv := type_all_env_weak henv hw (ste_refl s)
  have htae : type_all_env c' s
      (.mk nsEmpty (nsSing cn (ts.length, stamp.ExnStamp st.next_exn_stamp)))
      { v := nsEmpty, c := nsSing cn ([], ts.map (type_name_subst tenv.t), Texn_num),
        t := nsEmpty } := by
    refine ⟨?_, nsAll2_nsEmpty _⟩
    exact (nsAll2_nsSing _ cn _ cn _).mpr ⟨rfl, hnew, by simp⟩
  exact ⟨c', s, hw, hfr, ste_refl s, htae,
    htok', hg', hcons', type_all_env_extend' c' s _ env _ tenv ⟨htae, henv'⟩, hs'⟩

end

theorem type_def_to_ctMap_mem' (tenvT : tenv_abbrev) :
    ∀ (tds : List (List tvarN × mlstring × List (conN × List ast_t))) (tids : List type_ident)
      (next : Nat) (k : stamp) (x : List tvarN × List sem_t × type_ident),
      (k, x) ∈ type_def_to_ctMap tenvT next tds tids → x.2.2 ∈ tids := by
  intro tds
  induction tds with
  | nil =>
    intro tids next k x h
    cases tids <;> simp [type_def_to_ctMap] at h
  | cons td tds ih =>
    intro tids next k x h
    obtain ⟨tvs, tn, ctors⟩ := td
    cases tids with
    | nil => simp [type_def_to_ctMap] at h
    | cons id_ ids =>
      simp only [type_def_to_ctMap, List.mem_append, List.mem_reverse, List.mem_map] at h
      rcases h with h | ⟨q, _, hq⟩
      · exact List.mem_cons_of_mem _ (ih ids _ k x h)
      · simp only [Prod.mk.injEq] at hq
        rw [← hq.2]
        simp

section
variable {ffi : Type}

theorem pd_dtype {st st' : cml_state ffi} {env : sem_env} {c : ctMap} {s : tenv_store}
    {tenv : type_env} {l : locs} {tdefs : type_def} {tids : List type_ident}
    {tenvT : tenv_abbrev} {r : result sem_env v}
    (hdist : ALL_DISTINCT tids = true)
    (hdisj : Set.Disjoint (fun x => x ∈ tids)
      (fun x => x ∈ (Tlist_num :: Tbool_num :: prim_type_nums)))
    (hchk : check_ctor_tenv (nsAppend tenvT tenv.t) tdefs = true)
    (hlen : tids.length = tdefs.length)
    (htok' : tenv_ok (extend_dec_tenv
      { v := nsEmpty, c := build_ctor_tenv (nsAppend tenvT tenv.t) tdefs tids, t := tenvT } tenv))
    (heval : evaluate_decs st env [.Dtype l tdefs] = (st', r))
    (hinv : type_sound_invariant st env c s (fun x => x ∈ tids) tenv) :
    DR st' env c s (fun x => x ∈ tids) tenv
      { v := nsEmpty, c := build_ctor_tenv (nsAppend tenvT tenv.t) tdefs tids, t := tenvT } r := by
  obtain ⟨htok, hg, hcons, henv, hs⟩ := hinv
  obtain ⟨hc, hb, hex, hl⟩ := hg
  have hdups := check_ctor_tenv_dups' _ _ hchk
  have hdups' : tdefs.all check_dup_ctors = true := hdups
  rw [evd_dtype, if_pos hdups'] at heval
  cases heval
  let T := nsAppend tenvT tenv.t
  let n := st.next_type_stamp
  let L := type_def_to_ctMap T n tdefs tids
  let c' : ctMap := Finmap.FUPDATE_LIST c L.reverse
  have K1 : ∀ k x, c' k = some x → c k = some x ∨ (k, x) ∈ L := by
    intro k x h
    rcases FUPDATE_LIST_cases _ _ k x h with h1 | h1
    · exact .inl h1
    · exact .inr (by simpa using h1)
  have K2 : ∀ k x, (k, x) ∈ L → ∃ cn i, k = stamp.TypeStamp cn i ∧ n ≤ i ∧ i < n + tdefs.length :=
    fun k x h => mem_type_def_to_ctMap T n tdefs tids k x ⟨h, hlen.symm⟩
  have K3 : ∀ k x, (k, x) ∈ L → x.2.2 ∈ tids :=
    fun k x h => type_def_to_ctMap_mem' T tdefs tids n k x h
  have hbound : ∀ cn i, (c (stamp.TypeStamp cn i)).isSome = true → i < n :=
    fun cn i h => (hcons.2 cn i).1 h
  have K4 : ∀ k x, c k = some x → c' k = some x := by
    intro k x h
    show Finmap.FUPDATE_LIST c L.reverse k = some x
    rw [FUPDATE_LIST_notin]
    · exact h
    · intro p hp heq
      obtain ⟨cn, i, h1, h2, _⟩ := K2 p.1 p.2 (by simpa using hp)
      rw [heq] at h1
      rw [h1] at h
      have := hbound cn i (by simp [h])
      omega
  have hw : weakCT c' c := K4
  have hfr : Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) c') \
      Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) c) ⊆ (fun x => x ∈ tids : Set type_ident) := by
    intro x ⟨⟨a, ha⟩, hx2⟩
    simp only [Finmap.o_f] at ha
    cases h : c' a with
    | none => rw [h] at ha; simp at ha
    | some y =>
      rw [h] at ha
      simp only [Option.map_some, Option.some.injEq] at ha
      rcases K1 a y h with h2 | h2
      · exact absurd ⟨a, by simp only [Finmap.o_f, h2, Option.map_some, ha]⟩ hx2
      · rw [← ha]; exact K3 a y h2
  have hTok : tenv_abbrev_ok T := htok'.2.2
  have hc'ok : ctMap_ok c' := by
    have e : c' = Finmap.FUNION (Finmap.FUPDATE_LIST Finmap.FEMPTY L.reverse) c :=
      fupdate2_union c [] L.reverse
    rw [e]
    apply ctMap_ok_merge_imp
    refine ⟨?_, ?_, hc⟩
    · intro x ⟨⟨a, ha⟩, hx2⟩
      simp only [Finmap.o_f] at ha
      cases h : Finmap.FUPDATE_LIST (Finmap.FEMPTY : ctMap) L.reverse a with
      | none => rw [h] at ha; simp at ha
      | some y =>
        rw [h] at ha
        simp only [Option.map_some, Option.some.injEq] at ha
        rcases FUPDATE_LIST_cases _ _ a y h with h2 | h2
        · simp [Finmap.FEMPTY] at h2
        · have := K3 a y (by simpa using h2)
          rw [ha] at this
          exact hcons.1 x ⟨this, hx2⟩
    · exact ctMap_ok_type_defs T n tdefs tids ⟨hdist,
        fun x hx => hdisj x ⟨hx.1, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx.2)⟩,
        hlen.symm, hchk, hTok⟩
  have hnone : ∀ cn i, i < n → c (stamp.TypeStamp cn i) = none → c' (stamp.TypeStamp cn i) = none := by
    intro cn i hi h
    cases h2 : c' (stamp.TypeStamp cn i) with
    | none => rfl
    | some y =>
      rcases K1 _ _ h2 with h3 | h3
      · rw [h] at h3; simp at h3
      · obtain ⟨cn', i', e, hle, _⟩ := K2 _ _ h3
        simp only [stamp.TypeStamp.injEq] at e
        omega
  have hbn : bool_type_num < n := hbound (mlstring.strlit "True") bool_type_num
    (by rw [show c _ = _ from hb.1]; rfl)
  have hln : list_type_num < n := hbound (mlstring.strlit "[]") list_type_num
    (by rw [show c _ = _ from hl.1]; rfl)
  have hg' : good_ctMap c' := by
    refine ⟨hc'ok, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
    · exact K4 _ _ hb.1
    · exact K4 _ _ hb.2.1
    · intro cn' h; exact hnone _ _ hbn (hb.2.2 cn' h)
    · exact K4 _ _ hex.1
    · exact K4 _ _ hex.2.1
    · exact K4 _ _ hex.2.2.1
    · exact K4 _ _ hex.2.2.2
    · exact K4 _ _ hl.1
    · exact K4 _ _ hl.2.1
    · intro cn' h; exact hnone _ _ hln (hl.2.2 cn' h)
  have hcons' : consistent_ctMap
      { st with next_type_stamp := st.next_type_stamp + tdefs.length } ∅ c' := by
    refine ⟨fun x hx => hx.1, fun cn' id_ => ⟨?_, ?_⟩⟩
    · intro h
      have h' : (c' (stamp.TypeStamp cn' id_)).isSome = true := h
      show id_ < st.next_type_stamp + tdefs.length
      cases h2 : c' (stamp.TypeStamp cn' id_) with
      | none => rw [h2] at h'; simp at h'
      | some y =>
        rcases K1 _ _ h2 with o | o
        · have := hbound cn' id_ (by simp [o])
          omega
        · obtain ⟨cn'', i', e, _, hlt⟩ := K2 _ _ o
          simp only [stamp.TypeStamp.injEq] at e
          omega
    · intro h
      have h' : (c' (stamp.ExnStamp id_)).isSome = true := h
      show id_ < st.next_exn_stamp
      cases h2 : c' (stamp.ExnStamp id_) with
      | none => rw [h2] at h'; simp at h'
      | some y =>
        rcases K1 _ _ h2 with o | o
        · exact (hcons.2 cn' id_).2 (by show (c (stamp.ExnStamp id_)).isSome = true; simp [o])
        · obtain ⟨cn'', i', e, _, _⟩ := K2 _ _ o
          simp at e
  have hs' : type_s c' st.refs s := type_s_weakening c s st.refs c' ⟨hs, hw⟩
  have henv' : type_all_env c' s env tenv := type_all_env_weak henv hw (ste_refl s)
  have htae : type_all_env c' s (.mk nsEmpty (build_tdefs st.next_type_stamp tdefs))
      { v := nsEmpty, c := build_ctor_tenv (nsAppend tenvT tenv.t) tdefs tids, t := tenvT } := by
    refine ⟨?_, nsAll2_nsEmpty _⟩
    exact build_tdefs_build_tenv' T tdefs tids n c ⟨hdups, hlen.symm⟩
  exact ⟨c', s, hw, hfr, ste_refl s, htae,
    htok', hg', hcons', type_all_env_extend' c' s _ env _ tenv ⟨htae, henv'⟩, hs'⟩

end

def DS (ds : List dec) (tids : Set type_ident) (tenv tenv' : type_env) : Prop :=
  ∀ {ffi : Type} (st : cml_state ffi) (env : sem_env) (st' : cml_state ffi)
    (r : result sem_env v) (c : ctMap) (s : tenv_store),
    evaluate_decs st env ds = (st', r) → type_sound_invariant st env c s tids tenv →
    DR st' env c s tids tenv tenv' r

theorem evd_cons_gen {ffi : Type} (st : cml_state ffi) (env : sem_env) (d1 : dec) (ds : List dec) :
    evaluate_decs st env (d1 :: ds) =
    (match evaluate_decs st env [d1] with
    | (st1, .Rval env1) =>
      match evaluate_decs st1 (extend_dec_env env1 env) ds with
      | (st2, r) => (st2, combine_dec_result env1 r)
    | (st1, .Rerr e) => (st1, .Rerr e)) := by
  cases ds with
  | cons d2 ds' => exact evd_cons st env d1 d2 ds'
  | nil =>
    cases h : evaluate_decs st env [d1] with
    | mk st1 r1 =>
      cases r1 with
      | Rerr e => rfl
      | Rval env1 =>
        simp only [evd_nil, combine_dec_result]
        cases env1 with
        | mk a b => simp [sem_env.v_, sem_env.c, (nsAppend_nsEmpty _).2]

theorem extend_dec_env_assoc_aux (a b c : sem_env) :
    extend_dec_env a (extend_dec_env b c) = extend_dec_env (extend_dec_env a b) c := by
  simp [extend_dec_env, sem_env.v_, sem_env.c, nsAppend_assoc]

theorem dres_err {c' : ctMap} {s' : tenv_store} {ffi : Type} {st' : cml_state ffi} {env : sem_env}
    {tenv tenv1 tenv2 : type_env} {e : error_result v}
    (h : dres c' s' st' env tenv tenv1 (.Rerr e)) : dres c' s' st' env tenv tenv2 (.Rerr e) := by
  cases e with
  | Rraise x => exact h
  | Rabort a => cases a <;> exact h

theorem disj_step {c c1 : ctMap} {d1 d2 : Set type_ident}
    (h0 : Set.Disjoint (d1 ∪ d2) (Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) c)))
    (hfr : Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) c1) \
      Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) c) ⊆ d1)
    (hdj : Set.Disjoint d1 d2) :
    Set.Disjoint d2 (Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) c1)) := by
  intro x ⟨hx2, hxc1⟩
  by_cases hxc : x ∈ Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) c)
  · exact h0 x ⟨Or.inr hx2, hxc⟩
  · exact hdj x ⟨hfr x ⟨hxc1, hxc⟩, hx2⟩

theorem frange_comb {c c1 c2 : ctMap} {d1 d2 : Set type_ident}
    (hfr1 : Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) c1) \
      Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) c) ⊆ d1)
    (hfr2 : Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) c2) \
      Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) c1) ⊆ d2) :
    Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) c2) \
      Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) c) ⊆ d1 ∪ d2 := by
  intro x ⟨h2, hn⟩
  by_cases h1 : x ∈ Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) c1)
  · exact Or.inl (hfr1 x ⟨h1, hn⟩)
  · exact Or.inr (hfr2 x ⟨h2, h1⟩)

theorem inv_tids {ffi : Type} {st : cml_state ffi} {env : sem_env} {c : ctMap} {s : tenv_store}
    {tids : Set type_ident} {tenv : type_env}
    (h : type_sound_invariant st env c s ∅ tenv)
    (hd : Set.Disjoint tids (Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) c))) :
    type_sound_invariant st env c s tids tenv :=
  ⟨h.1, h.2.1, ⟨hd, h.2.2.1.2⟩, h.2.2.2.1, h.2.2.2.2⟩

theorem pds_cons {d : dec} {ds : List dec} {decls1 decls2 : Set type_ident}
    {tenv tenv1 tenv2 : type_env}
    (ih1 : DS [d] decls1 tenv tenv1) (ih2 : DS ds decls2 (extend_dec_tenv tenv1 tenv) tenv2)
    (hdj : Set.Disjoint decls1 decls2) :
    DS (d :: ds) (decls1 ∪ decls2) tenv (extend_dec_tenv tenv2 tenv1) := by
  intro ffi st env st' r c s heval hinv
  have hinv1 := type_sound_invariant_union' st env c s decls1 decls2 tenv hinv
  obtain ⟨htok, hg, hcons, henv, hs⟩ := hinv
  rw [evd_cons_gen] at heval
  cases h1 : evaluate_decs st env [d] with
  | mk st1 r1 =>
    rw [h1] at heval
    obtain ⟨c1, s1, hw1, hfr1, hste1, hres1⟩ := ih1 st env st1 r1 c s h1 hinv1
    cases r1 with
    | Rerr e =>
      simp only [] at heval
      cases heval
      exact ⟨c1, s1, hw1, fun x hx => Or.inl (hfr1 x hx), hste1, dres_err hres1⟩
    | Rval env1 =>
      simp only [] at heval
      obtain ⟨hae1, hinvA⟩ := hres1
      have hinvB := inv_tids hinvA (disj_step hcons.1 hfr1 hdj)
      cases h2 : evaluate_decs st1 (extend_dec_env env1 env) ds with
      | mk st2 r2 =>
        rw [h2] at heval
        simp only [] at heval
        cases heval
        obtain ⟨c2, s2, hw2, hfr2, hste2, hres2⟩ := ih2 st1 _ _ r2 c1 s1 h2 hinvB
        refine ⟨c2, s2, weakCT_trans c2 c1 c ⟨hw2, hw1⟩, frange_comb hfr1 hfr2,
          ste_trans hste1 hste2, ?_⟩
        cases r2 with
        | Rval env2 =>
          obtain ⟨hae2, hinvC⟩ := hres2
          show type_all_env c2 s2 (extend_dec_env env2 env1) (extend_dec_tenv tenv2 tenv1) ∧
            type_sound_invariant st' (extend_dec_env (extend_dec_env env2 env1) env) c2 s2 ∅
              (extend_dec_tenv (extend_dec_tenv tenv2 tenv1) tenv)
          refine ⟨type_all_env_extend' c2 s2 env2 env1 tenv2 tenv1
            ⟨hae2, type_all_env_weak hae1 hw2 hste2⟩, ?_⟩
          rw [← extend_dec_tenv_assoc_thm, ← extend_dec_env_assoc_aux]
          exact hinvC
        | Rerr e =>
          cases e with
          | Rraise x =>
            exact ⟨hres2.1, htok, hres2.2.2.1, hres2.2.2.2.1,
              type_all_env_weak henv (weakCT_trans c2 c1 c ⟨hw2, hw1⟩) (ste_trans hste1 hste2),
              hres2.2.2.2.2.2⟩
          | Rabort a => cases a <;> first | exact hres2 | exact trivial

theorem pd_dlocal {lds ds : List dec} {decls1 decls2 : Set type_ident}
    {tenv tenv1 tenv2 : type_env}
    (htok' : tenv_ok tenv → tenv_ok (extend_dec_tenv tenv2 tenv))
    (ih1 : DS lds decls1 tenv tenv1) (ih2 : DS ds decls2 (extend_dec_tenv tenv1 tenv) tenv2)
    (hdj : Set.Disjoint decls1 decls2) :
    DS [.Dlocal lds ds] (decls1 ∪ decls2) tenv tenv2 := by
  intro ffi st env st' r c s heval hinv
  have hinv1 := type_sound_invariant_union' st env c s decls1 decls2 tenv hinv
  obtain ⟨htok, hg, hcons, henv, hs⟩ := hinv
  rw [evd_dlocal] at heval
  cases h1 : evaluate_decs st env lds with
  | mk st1 r1 =>
    rw [h1] at heval
    obtain ⟨c1, s1, hw1, hfr1, hste1, hres1⟩ := ih1 st env st1 r1 c s h1 hinv1
    cases r1 with
    | Rerr e =>
      simp only [] at heval
      cases heval
      exact ⟨c1, s1, hw1, fun x hx => Or.inl (hfr1 x hx), hste1, dres_err hres1⟩
    | Rval env1 =>
      simp only [] at heval
      obtain ⟨hae1, hinvA⟩ := hres1
      have hinvB := inv_tids hinvA (disj_step hcons.1 hfr1 hdj)
      obtain ⟨c2, s2, hw2, hfr2, hste2, hres2⟩ := ih2 st1 _ st' r c1 s1 heval hinvB
      have hw := weakCT_trans c2 c1 c ⟨hw2, hw1⟩
      have hste := ste_trans hste1 hste2
      refine ⟨c2, s2, hw, frange_comb hfr1 hfr2, hste, ?_⟩
      cases r with
      | Rval env2 =>
        obtain ⟨hae2, hinvC⟩ := hres2
        exact ⟨hae2, htok' htok, hinvC.2.1, hinvC.2.2.1,
          type_all_env_extend' c2 s2 env2 env tenv2 tenv ⟨hae2, type_all_env_weak henv hw hste⟩,
          hinvC.2.2.2.2⟩
      | Rerr e =>
        cases e with
        | Rraise x =>
          exact ⟨hres2.1, htok, hres2.2.2.1, hres2.2.2.2.1,
            type_all_env_weak henv hw hste, hres2.2.2.2.2.2⟩
        | Rabort a => cases a <;> first | exact hres2 | exact trivial

theorem pd_dmod {mn : modN} {ds : List dec} {decls : Set type_ident} {tenv tenv2 : type_env}
    (htok' : tenv_ok tenv → tenv_ok (extend_dec_tenv (tenvLift mn tenv2) tenv))
    (ih : DS ds decls tenv tenv2) :
    DS [.Dmod mn ds] decls tenv (tenvLift mn tenv2) := by
  intro ffi st env st' r c s heval hinv
  have hinv0 := hinv
  obtain ⟨htok, hg, hcons, henv, hs⟩ := hinv
  rw [evd_dmod] at heval
  cases h1 : evaluate_decs st env ds with
  | mk st1 r1 =>
    rw [h1] at heval
    simp only [] at heval
    cases heval
    obtain ⟨c1, s1, hw1, hfr1, hste1, hres1⟩ := ih st env _ r1 c s h1 hinv0
    refine ⟨c1, s1, hw1, hfr1, hste1, ?_⟩
    cases r1 with
    | Rval env1 =>
      obtain ⟨hae1, hinvA⟩ := hres1
      have hlift : type_all_env c1 s1 (.mk (nsLift mn env1.v_) (nsLift mn env1.c))
          (tenvLift mn tenv2) :=
        ⟨(nsAll2_nsLift _ mn _ _).mpr hae1.1, (nsAll2_nsLift _ mn _ _).mpr hae1.2⟩
      exact ⟨hlift, htok' htok, hinvA.2.1, hinvA.2.2.1,
        type_all_env_extend' c1 s1 _ env _ tenv ⟨hlift, type_all_env_weak henv hw1 hste1⟩,
        hinvA.2.2.2.2⟩
    | Rerr e => exact dres_err hres1

theorem set_union_empty {α : Type} (s : Set α) : s ∪ (∅ : Set α) = s := by
  funext x
  apply propext
  constructor
  · intro h
    rcases h with h | h
    · exact h
    · exact h.elim
  · intro h; exact Or.inl h

mutual
theorem pd_main : ∀ {chk : Bool} {tenv : type_env} {d : dec} {tids : Set type_ident}
    {tenv' : type_env}, type_d chk tenv d tids tenv' → DS [d] tids tenv tenv'
  | _, _, _, _, _, .dlet_poly chk tenv l p e tvs t bindings hv hd hp he hx =>
    fun st env st' r c s heval hinv =>
      pd_dlet (fun _ => hv) hd hp he
        (type_d_tenv_ok chk tenv _ _ _
          ⟨.dlet_poly chk tenv l p e tvs t bindings hv hd hp he hx, hinv.1⟩) heval hinv
  | _, _, _, _, _, .dlet_mono chk tenv l p e t bindings hx hd hp he =>
    fun st env st' r c s heval hinv =>
      pd_dlet (tvs := 0) (fun h => absurd rfl h) hd hp (by rw [bind_tvar0]; exact he)
        (type_d_tenv_ok chk tenv _ _ _
          ⟨.dlet_mono chk tenv l p e t bindings hx hd hp he, hinv.1⟩) heval hinv
  | _, _, _, _, _, .dletrec chk tenv l funs tvs bindings hf hx =>
    fun st env st' r c s heval hinv =>
      pd_dletrec hf
        (type_d_tenv_ok chk tenv _ _ _
          ⟨.dletrec chk tenv l funs tvs bindings hf hx, hinv.1⟩) heval hinv
  | _, _, _, _, _, .dtype chk tenv l tdefs tids tenvT h1 h2 h3 h4 h5 =>
    fun st env st' r c s heval hinv =>
      pd_dtype h1 h2 h3 h4
        (type_d_tenv_ok chk tenv _ _ _
          ⟨.dtype chk tenv l tdefs tids tenvT h1 h2 h3 h4 h5, hinv.1⟩) heval hinv
  | _, _, _, _, _, .dtabbrev chk tenv l tvs tn t h1 h2 h3 =>
    fun st env st' r c s heval hinv =>
      pd_dtabbrev
        (type_d_tenv_ok chk tenv _ _ _
          ⟨.dtabbrev chk tenv l tvs tn t h1 h2 h3, hinv.1⟩) heval hinv
  | _, _, _, _, _, .dexn chk tenv l cn ts h1 h2 =>
    fun st env st' r c s heval hinv =>
      pd_dexn h1 h2
        (type_d_tenv_ok chk tenv _ _ _
          ⟨.dexn chk tenv l cn ts h1 h2, hinv.1⟩) heval hinv
  | _, _, _, _, _, .dmod chk tenv mn ds decls tenv2 h1 =>
    pd_dmod (fun htok => type_d_tenv_ok chk tenv _ _ _ ⟨.dmod chk tenv mn ds decls tenv2 h1, htok⟩)
      (pds_main h1)
  | _, _, _, _, _, .dlocal chk tenv lds ds decls1 tenv1 decls2 tenv2 h1 h2 h3 =>
    pd_dlocal
      (fun htok => type_d_tenv_ok chk tenv _ _ _
        ⟨.dlocal chk tenv lds ds decls1 tenv1 decls2 tenv2 h1 h2 h3, htok⟩)
      (pds_main h1) (pds_main h2) h3

theorem pds_main : ∀ {chk : Bool} {tenv : type_env} {ds : List dec} {tids : Set type_ident}
    {tenv' : type_env}, type_ds chk tenv ds tids tenv' → DS ds tids tenv tenv'
  | _, _, _, _, _, .nil chk tenv => fun st env st' r c s heval hinv => pds_nil heval hinv
  | _, _, _, _, _, .cons chk tenv d ds decls1 tenv1 decls2 tenv2 h1 h2 h3 =>
    pds_cons (pd_main h1) (pds_main h2) h3
end

theorem decs_type_sound_no_check' :
    ∀ {ffi : Type} (st : cml_state ffi) (env : sem_env) (ds : List dec)
      (st' : cml_state ffi) (r : result sem_env v) (ctMap_ : ctMap)
      (tenvS : tenv_store) (tenv : type_env) (tids : Set type_ident)
      (tenv' : type_env),
      evaluate_decs st env ds = (st', r) ∧
      type_ds false tenv ds tids tenv' ∧
      type_sound_invariant st env ctMap_ tenvS tids tenv →
      ∃ (ctMap' : ctMap) (tenvS' : tenv_store),
        weakCT ctMap' ctMap_ ∧
        Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) ctMap') \
          Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) ctMap_) ⊆ tids ∧
        ste tenvS tenvS' ∧
        match r with
        | .Rval env' =>
          type_all_env ctMap' tenvS' env' tenv' ∧
          type_sound_invariant st' (extend_dec_env env' env)
            ctMap' tenvS' ∅ (extend_dec_tenv tenv' tenv)
        | .Rerr (.Rraise err_v) =>
          type_v 0 ctMap' tenvS' err_v Texn ∧
          type_sound_invariant st' env ctMap' tenvS' ∅ tenv
        | .Rerr (.Rabort .Rtype_error) => False
        | .Rerr (.Rabort .Rtimeout_error) => True
        | .Rerr (.Rabort (.Rffi_error _)) => True := by
  intro ffi st env ds st' r c s tenv tids tenv' ⟨heval, htds, hinv⟩
  obtain ⟨c', s', hw, hfr, hste, hres⟩ := pds_main htds st env st' r c s heval hinv
  refine ⟨c', s', hw, hfr, hste, ?_⟩
  cases r with
  | Rval x => exact hres
  | Rerr e => cases e with
    | Rraise x => exact hres
    | Rabort a => cases a <;> exact hres

theorem decs_type_sound' :
    ∀ {ffi : Type} (st : cml_state ffi) (env : sem_env) (ds : List dec)
      (extra_checks : Bool) (st' : cml_state ffi) (r : result sem_env v)
      (ctMap_ : ctMap) (tenvS : tenv_store) (tenv : type_env) (tids : Set type_ident)
      (tenv' : type_env),
      evaluate_decs st env ds = (st', r) ∧
      type_ds extra_checks tenv ds tids tenv' ∧
      type_sound_invariant st env ctMap_ tenvS tids tenv →
      ∃ (ctMap' : ctMap) (tenvS' : tenv_store),
        weakCT ctMap' ctMap_ ∧
        Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) ctMap') \
          Finmap.FRANGE (Finmap.o_f (fun p => p.2.2) ctMap_) ⊆ tids ∧
        ste tenvS tenvS' ∧
        match r with
        | .Rval env' =>
          type_all_env ctMap' tenvS' env' tenv' ∧
          type_sound_invariant st' (extend_dec_env env' env)
            ctMap' tenvS' ∅ (extend_dec_tenv tenv' tenv)
        | .Rerr (.Rraise err_v) =>
          type_v 0 ctMap' tenvS' err_v Texn ∧
          type_sound_invariant st' env ctMap' tenvS' ∅ tenv
        | .Rerr (.Rabort .Rtype_error) => False
        | .Rerr (.Rabort (.Rffi_error _)) => True
        | .Rerr (.Rabort .Rtimeout_error) => True := by
  intro ffi st env ds chk st' r c s tenv tids tenv' ⟨heval, htds, hinv⟩
  obtain ⟨c', s', hw, hfr, hste, hres⟩ := pds_main htds st env st' r c s heval hinv
  refine ⟨c', s', hw, hfr, hste, ?_⟩
  cases r with
  | Rval x => exact hres
  | Rerr e => cases e with
    | Rraise x => exact hres
    | Rabort a => cases a <;> exact hres

theorem semantics_type_sound' :
    ∀ {ffi : Type} (st : cml_state ffi) (env : sem_env) (tops : List dec)
      (r : behaviour) (checks : Bool) (ctMap_ : ctMap) (tenvS : tenv_store)
      (tenv : type_env) (new_tenv : type_env) (tids : Set type_ident),
      semantics_prog st env tops r ∧
      type_ds checks tenv tops tids new_tenv ∧
      type_sound_invariant st env ctMap_ tenvS tids tenv →
      r ≠ .Fail := by
  intro ffi st env tops r chk c s tenv new_tenv tids ⟨hsem, htds, hinv⟩ hr
  subst hr
  obtain ⟨k, hk⟩ := hsem
  unfold evaluate_prog_with_clock at hk
  cases h : evaluate_decs { st with clock := k } env tops with
  | mk st2 r2 =>
    rw [h] at hk
    simp only [] at hk
    subst hk
    have hinv' : type_sound_invariant { st with clock := k } env c s tids tenv :=
      ⟨hinv.1, hinv.2.1, hinv.2.2.1, hinv.2.2.2.1, hinv.2.2.2.2⟩
    obtain ⟨c', s', hw, hfr, hste, hres⟩ := pds_main htds _ env st2 _ c s h hinv'
    exact hres

end DAux
