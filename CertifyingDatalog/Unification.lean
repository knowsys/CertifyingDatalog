import CertifyingDatalog.Datalog

section TermMatching
  variable {τ: Signature}

  namespace Substitution
    def extend [DecidableEq τ.vars] (s: Substitution τ) (v: τ.vars) (c: τ.constants) : Substitution τ := fun x => if x = v then Option.some c else s x

    lemma extend_subset [DecidableEq τ.vars] {s: Substitution τ} {v: τ.vars} {c: τ.constants} (p: Option.isNone (s v)): s ⊆ extend s v c := by
      unfold extend
      unfold_projs
      unfold subset
      intro v'
      simp only
      intro h
      by_cases v'_v: v' = v
      · simp only [v'_v, ↓reduceIte]
        unfold domain at h
        simp only [Set.mem_setOf_eq] at h
        rw [v'_v] at h
        exfalso
        cases h':(s v) with
        | none =>
          rw [h'] at h
          simp at h
        | some c' =>
          rw [h'] at p
          simp at p
      · simp [v'_v]

    lemma extend_subset_self [DecidableEq τ.vars] {s: Substitution τ} {v: τ.vars} {c: τ.constants} (p: s v = some c): s ⊆ extend s v c := by
      unfold extend
      unfold_projs
      unfold subset
      intro v'
      simp only
      intro h
      by_cases v'_v: v' = v
      · simp only [v'_v, ↓reduceIte]
        exact p
      · simp [v'_v]

    def matchTerm [DecidableEq τ.vars] [DecidableEq τ.constants] (s: Substitution τ) (t: Term τ) (c: τ.constants) : Option (Substitution τ) :=
      match t with
      | .constant c' => if c = c' then Option.some s else Option.none
      | .variableDL v =>
        (some (extend s v c)).filter (fun s' => (s v).isSome → s v = s' v)

    lemma matchTermSubset [DecidableEq τ.vars] [DecidableEq τ.constants] {s: Substitution τ} {t: Term τ} {c: τ.constants} (h : (s.matchTerm t c).isSome) : s ⊆ ((s.matchTerm t c).get h) := by
      simp only [matchTerm, decide_implies, dite_eq_ite, Bool.if_true_right, Bool.decide_eq_true,
        Option.bnot_isSome] at h ⊢
      cases t with
      | constant c' =>
        simp only [Option.get_ite]
        apply Substitution.subset_refl
      | variableDL v =>
        simp [Option.isSome_iff_exists] at h
        cases h with
        | inl h =>
          simp only [h, Option.isNone_none, Bool.true_or, Option.filter_true, Option.get_some]
          apply extend_subset
          simp [h]
        | inr h =>
          simp [h, Option.filter]
          simp [extend] at h
          apply extend_subset_self h

    lemma matchTermYieldsSubs [DecidableEq τ.vars] [DecidableEq τ.constants] {s: Substitution τ} {t: Term τ} {c: τ.constants} (h : (s.matchTerm t c).isSome) : ((s.matchTerm t c).get h).applyTerm t = c := by
      simp only [matchTerm, decide_implies, dite_eq_ite, Bool.if_true_right, Bool.decide_eq_true,
        Option.bnot_isSome] at h ⊢
      cases t with
      | constant c' =>
        simp only [Option.get_ite]
        cases Decidable.em (c = c') with
        | inl eq =>
          simp only [eq]
          unfold applyTerm
          simp
        | inr neq =>
          simp [neq] at h
      | variableDL v =>
        simp [Option.filter, extend, applyTerm] at h ⊢

    lemma matchTermIsMinimal [DecidableEq τ.vars] [DecidableEq τ.constants] {s: Substitution τ} {t: Term τ} {c: τ.constants} (h : (s.matchTerm t c).isSome) : ∀ s' : Substitution τ, s ⊆ s' ∧ s'.applyTerm t = c -> ((s.matchTerm t c).get h) ⊆ s' := by
      intro s' ⟨subset, apply_t⟩
      simp only [matchTerm, decide_implies, dite_eq_ite, Bool.if_true_right, Bool.decide_eq_true,
        Option.bnot_isSome] at h ⊢
      cases t with
      | constant c' =>
        simp only [Option.get_ite]
        apply subset
      | variableDL v =>
        simp only [Option.filter, Bool.or_eq_true, Option.isNone_iff_eq_none, decide_eq_true_eq,
          Option.isSome_ite, Option.get_ite] at h ⊢
        cases h with
        | inl h =>
          unfold_projs
          simp only [Substitution.subset, domain, extend, Set.mem_setOf_eq]
          intro v'
          by_cases v_v': v' = v
          · simp only [v_v', ↓reduceIte, Option.isSome_some, forall_const]
            simp only [applyTerm] at apply_t
            split at apply_t
            · rename_i o c' hc'
              simp only [v_v', hc', Option.some.injEq]
              simp only [Term.constant.injEq] at apply_t
              exact apply_t.symm
            · simp at apply_t
          · simp only [v_v', ↓reduceIte]
            apply subset
        | inr h =>
          unfold_projs
          simp only [Substitution.subset, domain, extend, Set.mem_setOf_eq]
          intro v'
          by_cases v_v': v' = v
          · simp only [v_v', ↓reduceIte, Option.isSome_some, forall_const]
            simp only [extend, ↓reduceIte] at h
            apply Eq.symm
            apply subset_some _ _ subset _ _ h
          · simp only [v_v', ↓reduceIte, Option.isSome_iff_exists, forall_exists_index]
            intro c' h'
            simp only [h', Eq.comm]
            apply subset_some _ _ subset _ _ h'


    lemma matchTermNoneThenNoSubs [DecidableEq τ.vars] [DecidableEq τ.constants] {s: Substitution τ} {t: Term τ}{c: τ.constants} (h : (s.matchTerm t c) = none) : ∀ s' : Substitution τ, s ⊆ s' -> s'.applyTerm t ≠ c := by
      intro s' subset apply_t
      simp only [matchTerm, decide_implies, dite_eq_ite, Bool.if_true_right, Bool.decide_eq_true,
        Option.bnot_isSome] at h
      cases t with
      | constant c' =>
        unfold applyTerm at apply_t
        simp only [Term.constant.injEq] at apply_t
        simp [apply_t] at h
      | variableDL v =>
        simp only [Option.filter_eq_none, reduceCtorEq, Option.mem_def, Option.some.injEq,
          Bool.or_eq_true, Option.isNone_iff_eq_none, decide_eq_true_eq, not_or,
          Option.ne_none_iff_exists, forall_eq', extend, ↓reduceIte, false_or] at h
        rcases h with ⟨hl, hr⟩
        rcases hl with ⟨c', hc'⟩
        simp only [← hc', Option.some.injEq] at hr
        have:= subset_some _ _ subset _ _ (Eq.symm hc')
        simp only [applyTerm, this, Term.constant.injEq] at apply_t
        contradiction

  end Substitution
end TermMatching

section AtomMatching
  variable {τ: Signature} [DecidableEq τ.constants] [DecidableEq τ.vars]

  namespace Substitution
    def matchTermList (s: Substitution τ) : List ((Term τ) × τ.constants) -> Option (Substitution τ)
    | .nil => Option.some s
    | .cons ⟨t, c⟩ l => match s.matchTerm t c with
      | .none => Option.none
      | .some s' => s'.matchTermList l

    lemma matchTermListSubset {s : Substitution τ} {l : List ((Term τ) × τ.constants)} (h : (s.matchTermList l).isSome) : s ⊆ (s.matchTermList l).get h := by
      induction l generalizing s with
      | nil => unfold matchTermList; apply subset_refl
      | cons pair l ih =>
        cases eq : s.matchTerm pair.fst pair.snd with
        | none => unfold matchTermList at h; simp [eq] at h
        | some s' =>
          have matchPairSome : (s.matchTerm pair.fst pair.snd).isSome := by simp [eq]
          have : s.matchTermList (pair::l) = ((s.matchTerm pair.fst pair.snd).get matchPairSome).matchTermList l := by
            conv => left; unfold matchTermList
            simp [eq]
          simp_rw [this]
          apply subset_trans
          · apply matchTermSubset
            apply matchPairSome
          · apply ih

    lemma matchTermListYieldsSubs {s: Substitution τ} {l: List ((Term τ) × τ.constants)} (h : (s.matchTermList l).isSome) : (l.map Prod.fst).map ((s.matchTermList l).get h).applyTerm = l.map (fun x => Term.constant (Prod.snd x)) := by
      induction l generalizing s with
      | nil => simp
      | cons pair l ih =>
        cases eq : s.matchTerm pair.fst pair.snd with
        | none => unfold matchTermList at h; simp [eq] at h
        | some s' =>
          have : (s.matchTerm pair.fst pair.snd).isSome := by simp [eq]
          have matchTermResult := s.matchTermYieldsSubs this
          have : s.matchTermList (pair::l) = ((s.matchTerm pair.fst pair.snd).get this).matchTermList l := by
            conv => left; unfold matchTermList
            simp [eq]
          simp
          constructor
          · unfold matchTermList at h
            cases eq : s.matchTerm pair.fst pair.snd with
            | none => simp [eq] at h
            | some s' =>
              apply subset_applyTerm_eq _ matchTermResult
              simp_rw [this]
              apply matchTermListSubset
          · simp_rw [this]
            simp only [List.map_map, List.map_inj_left, Function.comp_apply, Prod.forall] at ih
            apply ih

    lemma matchTermListIsMinimal {s: Substitution τ} {l: List ((Term τ) × τ.constants)} (h : (s.matchTermList l).isSome) : ∀ s' : Substitution τ, s ⊆ s' ∧ ((l.map Prod.fst).map s'.applyTerm = l.map (fun x => Term.constant (Prod.snd x))) -> ((s.matchTermList l).get h) ⊆ s' := by
      induction l generalizing s with
      | nil => intro s ⟨subset, _⟩; simp [matchTermList]; exact subset
      | cons pair l ih =>
        intro s' ⟨subset, apply_t⟩
        rw [List.map_map] at apply_t
        unfold List.map at apply_t
        simp only [Function.comp_apply, List.pure_def, List.bind_eq_flatMap, List.flatMap_cons,
          List.singleton_append, List.cons.injEq] at apply_t
        cases eq : s.matchTerm pair.fst pair.snd with
        | none => simp [matchTermList, eq] at h
        | some s'' =>
          simp only [matchTermList, eq]
          simp only [matchTermList, eq] at h
          simp only [List.map_map, List.pure_def, List.bind_eq_flatMap, and_imp] at ih
          apply ih h s' _ apply_t.right

          have isSome : (s.matchTerm pair.fst pair.snd).isSome := by simp [eq]
          have : s'' = (s.matchTerm pair.fst pair.snd).get isSome := by simp [eq]
          rw [this]
          apply matchTermIsMinimal
          constructor
          · apply subset
          · apply apply_t.left

    lemma matchTermListNoneThenNoSubs {s: Substitution τ} {l: List ((Term τ) × τ.constants)} (h : (s.matchTermList l) = none) : ∀ s' : Substitution τ, s ⊆ s' -> ¬ (l.map Prod.fst).map s'.applyTerm = l.map (fun x => Term.constant (Prod.snd x)) := by
      induction l generalizing s with
      | nil => simp [matchTermList] at h
      | cons pair l ih =>
        intro s' subset apply_t
        rw [List.map_map] at apply_t
        unfold List.map at apply_t
        simp only [Function.comp_apply, List.pure_def, List.bind_eq_flatMap, List.flatMap_cons,
          List.singleton_append, List.cons.injEq] at apply_t
        cases eq : s.matchTerm pair.fst pair.snd with
        | none =>
          apply matchTermNoneThenNoSubs eq s' subset
          apply apply_t.left
        | some s'' =>
          simp only [matchTermList, eq] at h
          simp only [List.map_map, List.pure_def, List.bind_eq_flatMap] at ih
          apply ih h s' _ apply_t.right

          have isSome : (s.matchTerm pair.fst pair.snd).isSome := by simp [eq]
          have : s'' = (s.matchTerm pair.fst pair.snd).get isSome := by simp [eq]
          rw [this]
          apply matchTermIsMinimal
          constructor
          · apply subset
          · apply apply_t.left

    variable [DecidableEq τ.relationSymbols]

    def matchAtom (s: Substitution τ) (a: Atom τ) (ga: GroundAtom τ): Option (Substitution τ) :=
      if a.symbol = ga.symbol
      -- NOTE: if the symbols are equal, we know that the arity is the same
      then s.matchTermList (a.atom_terms.zip ga.atom_terms)
      else none

    lemma matchAtomSubset {s: Substitution τ} {a: Atom τ} {ga: GroundAtom τ} (h : (s.matchAtom a ga).isSome) : s ⊆ ((s.matchAtom a ga).get h) := by
      have symb_eq : a.symbol = ga.symbol := by
        apply Decidable.by_contra
        intro contra
        unfold matchAtom at h
        simp [contra] at h
      unfold matchAtom
      simp only [symb_eq, ↓reduceIte]
      apply s.matchTermListSubset

    lemma matchAtomYieldsSubs {s: Substitution τ} {a: Atom τ} {ga: GroundAtom τ} (h : (s.matchAtom a ga).isSome) : ((s.matchAtom a ga).get h).applyAtom a = ga := by
      have symb_eq : a.symbol = ga.symbol := by
        apply Decidable.by_contra
        intro contra
        unfold matchAtom at h
        simp [contra] at h
      have term_lists_eq_len : a.atom_terms.length = ga.atom_terms.length := by rw [a.term_length, ga.term_length, symb_eq]
      unfold matchAtom
      simp only [symb_eq, ↓reduceIte]
      unfold applyAtom
      unfold GroundAtom.toAtom
      simp only [Atom.mk.injEq]
      constructor
      · exact symb_eq
      · unfold matchAtom at h
        simp only [symb_eq, ↓reduceIte] at h
        let term_list : List ((Term τ) × τ.constants) := a.atom_terms.zip ga.atom_terms
        have match_t_list := s.matchTermListYieldsSubs h
        have fst : a.atom_terms = term_list.map Prod.fst := by
          rw [List.map_fst_zip]
          apply Nat.le_of_eq
          rw [term_lists_eq_len]
        have snd : ga.atom_terms = term_list.map Prod.snd := by
          rw [List.map_snd_zip]
          apply Nat.le_of_eq
          rw [term_lists_eq_len]
        rw [← fst] at match_t_list
        rw [match_t_list]
        apply List.ext_get
        · simp [snd, fst]
        · intro n h₁ h₂
          simp

    lemma matchAtomIsMinimal {s: Substitution τ} {a: Atom τ} {ga: GroundAtom τ} (h : (s.matchAtom a ga).isSome) : ∀ s' : Substitution τ, s ⊆ s' ∧ s'.applyAtom a = ga -> ((s.matchAtom a ga).get h) ⊆ s' := by
      intro s' ⟨subset, apply_a⟩
      unfold applyAtom at apply_a
      unfold GroundAtom.toAtom at apply_a
      simp only [Atom.mk.injEq] at apply_a
      have ⟨symb_eq, terms_eq⟩ := apply_a
      have term_lists_eq_len : a.atom_terms.length = ga.atom_terms.length := by rw [a.term_length, ga.term_length, symb_eq]
      let term_list : List ((Term τ) × τ.constants) := a.atom_terms.zip ga.atom_terms
      unfold matchAtom
      simp only [symb_eq, ↓reduceIte]
      apply s.matchTermListIsMinimal
      constructor
      · apply subset
      · apply List.ext_get
        · simp
        · intro n h₁ h₂
          have := List.getElem_of_eq terms_eq (i := n)
          simp only [List.get_eq_getElem, List.map_map, List.getElem_map, List.getElem_zip,
            Function.comp_apply]
          simp only [List.length_map, List.getElem_map] at this
          apply this
          simp only [List.map_map, List.length_map, List.length_zip, lt_inf_iff] at h₁
          simp [h₁]

    lemma matchAtomNoneThenNoSubs {s: Substitution τ} {a: Atom τ} {ga: GroundAtom τ} (h : (s.matchAtom a ga) = none) : ∀ s' : Substitution τ, s ⊆ s' -> s'.applyAtom a ≠ ga := by
      intro s' subset apply_a
      unfold matchAtom at h
      unfold applyAtom at apply_a
      unfold GroundAtom.toAtom at apply_a
      simp at apply_a
      have ⟨symb_eq, terms_eq⟩ := apply_a
      have term_lists_eq_len : a.atom_terms.length = ga.atom_terms.length := by rw [a.term_length, ga.term_length, symb_eq]
      simp [symb_eq] at h
      let term_list : List ((Term τ) × τ.constants) := a.atom_terms.zip ga.atom_terms
      apply s.matchTermListNoneThenNoSubs h s' subset
      have fst : a.atom_terms = term_list.map Prod.fst := by
        rw [List.map_fst_zip]
        apply Nat.le_of_eq
        rw [term_lists_eq_len]
      have snd : ga.atom_terms = term_list.map Prod.snd := by
        rw [List.map_snd_zip]
        apply Nat.le_of_eq
        rw [term_lists_eq_len]
      rw [← fst,]
      rw [terms_eq]
      apply List.ext_get
      · simp [fst, snd]
      · intro n h₁ h₂
        simp
  end Substitution
end AtomMatching

section RuleMatching
  variable {τ: Signature} [DecidableEq τ.constants] [DecidableEq τ.vars] [DecidableEq τ.relationSymbols]

  namespace Substitution
    def matchAtomList (s: Substitution τ) : List ((Atom τ) × (GroundAtom τ)) -> Option (Substitution τ)
    | .nil => Option.some s
    | .cons ⟨a, ga⟩ l => match s.matchAtom a ga with
      | .none => Option.none
      | .some s' => s'.matchAtomList l

    lemma matchAtomListSubset {s : Substitution τ} {l : List ((Atom τ) × (GroundAtom τ))} (h : (s.matchAtomList l).isSome) : s ⊆ (s.matchAtomList l).get h := by
      induction l generalizing s with
      | nil => unfold matchAtomList; apply subset_refl
      | cons pair l ih =>
        cases eq : s.matchAtom pair.fst pair.snd with
        | none => unfold matchAtomList at h; simp [eq] at h
        | some s' =>
          have matchPairSome : (s.matchAtom pair.fst pair.snd).isSome := by simp [eq]
          have : s.matchAtomList (pair::l) = ((s.matchAtom pair.fst pair.snd).get matchPairSome).matchAtomList l := by
            conv => left; unfold matchAtomList
            simp [eq]
          simp_rw [this]
          apply subset_trans
          · apply matchAtomSubset
            apply matchPairSome
          · apply ih

    lemma matchAtomListYieldsSubs {s: Substitution τ} {l: List ((Atom τ) × (GroundAtom τ))} (h : (s.matchAtomList l).isSome) : (l.map Prod.fst).map ((s.matchAtomList l).get h).applyAtom = l.map (fun x => GroundAtom.toAtom (Prod.snd x)) := by
      induction l generalizing s with
      | nil => simp
      | cons pair l ih =>
        cases eq : s.matchAtom pair.fst pair.snd with
        | none => unfold matchAtomList at h; simp [eq] at h
        | some s' =>
          have : (s.matchAtom pair.fst pair.snd).isSome := by simp [eq]
          have matchAtomResult := s.matchAtomYieldsSubs this
          have : s.matchAtomList (pair::l) = ((s.matchAtom pair.fst pair.snd).get this).matchAtomList l := by
            conv => left; unfold matchAtomList
            simp [eq]
          simp only [List.map_cons, List.map_map, List.pure_def, List.bind_eq_flatMap,
            List.flatMap_cons, List.singleton_append, List.cons.injEq]
          constructor
          · unfold matchAtomList at h
            cases eq : s.matchAtom pair.fst pair.snd with
            | none => simp [eq] at h
            | some s' =>
              apply subset_applyAtom_eq _ matchAtomResult
              simp_rw [this]
              apply matchAtomListSubset
          · simp_rw [this]
            simp only [List.map_map, List.pure_def, List.bind_eq_flatMap] at ih
            apply ih

    lemma matchAtomListNoneThenNoSubs {s: Substitution τ} {l: List ((Atom τ) × (GroundAtom τ))} (h : (s.matchAtomList l) = none) : ∀ s' : Substitution τ, s ⊆ s' -> ¬ (l.map Prod.fst).map s'.applyAtom = l.map (fun x => GroundAtom.toAtom (Prod.snd x)) := by
      induction l generalizing s with
      | nil => simp [matchAtomList] at h
      | cons pair l ih =>
        intro s' subset apply_t
        rw [List.map_map] at apply_t
        unfold List.map at apply_t
        simp only [Function.comp_apply, List.cons.injEq, List.map_inj_left, Prod.forall] at apply_t

        cases eq : s.matchAtom pair.fst pair.snd with
        | none =>
          apply matchAtomNoneThenNoSubs eq
          apply subset
          apply apply_t.left
        | some s'' =>
          simp [matchAtomList, eq] at h
          simp [List.map_map] at ih
          have isSome : (s.matchAtom pair.fst pair.snd).isSome := by simp [eq]
          have : s'' = (s.matchAtom pair.fst pair.snd).get isSome := by simp [eq]
          have subset' : s'' ⊆ s' := by
            rw [this]
            apply matchAtomIsMinimal
            constructor
            · apply subset
            · apply apply_t.left
          specialize ih h s' subset'
          rcases ih with ⟨a, ga, mem, ha⟩
          apply ha
          apply And.right apply_t
          exact mem

    def matchRule (r: Rule τ) (gr: GroundRule τ): Option (Substitution τ):=
      ((empty.matchAtom r.head gr.head).bind fun s => s.matchAtomList (r.body.zip gr.body)).filter (fun _ => r.body.length = gr.body.length)

    theorem matchRuleYieldsSubs {r : Rule τ} {gr : GroundRule τ} (h : (matchRule r gr).isSome) : ((matchRule r gr).get h).applyRule r = gr := by
      cases eq : empty.matchAtom r.head gr.head with
      | none => simp [matchRule, eq] at h
      | some s =>
        have body_eq_len : r.body.length = gr.body.length := by
          unfold matchRule at h
          simp only [eq, Option.some_bind, Option.isSome_iff_exists, Option.filter_eq_some,
            Option.mem_def, decide_eq_true_eq, exists_and_right] at h
          apply And.right h
        unfold applyRule
        unfold GroundRule.toRule
        simp only [Rule.mk.injEq]
        constructor
        · apply s.subset_applyAtom_eq
          · unfold matchRule
            simp [eq, body_eq_len, ↓reduceIte, Option.filter_true]
            apply matchAtomListSubset
          · have : (empty.matchAtom r.head gr.head).isSome := by simp [eq]
            have : s = (empty.matchAtom r.head gr.head).get this := by simp [eq]
            rw [this]
            apply matchAtomYieldsSubs
        · simp only [matchRule, body_eq_len, decide_true, eq, Option.some_bind, Option.filter_true]
          simp only [matchRule, body_eq_len, decide_true, eq, Option.some_bind,
            Option.filter_true] at h
          let atom_list := r.body.zip gr.body
          have match_a_list := s.matchAtomListYieldsSubs h
          have fst : r.body = atom_list.map Prod.fst := by
            rw [List.map_fst_zip]
            apply Nat.le_of_eq
            rw [body_eq_len]
          have snd : gr.body = atom_list.map Prod.snd := by
            rw [List.map_snd_zip]
            apply Nat.le_of_eq
            rw [body_eq_len]
          apply List.ext_get
          · simp [fst, snd]
          · intro n h₁ h₂
            simp only [Option.some_bind, List.get_eq_getElem, List.getElem_map]
            have := List.getElem_of_eq match_a_list (i := n)
            simp only [List.map_map, List.length_map, List.length_zip, lt_inf_iff, List.getElem_map,
              List.getElem_zip, Function.comp_apply] at this
            apply this
            simp only [List.length_map] at h₁ h₂
            exact And.intro h₁ h₂

    theorem matchRuleNoneThenNoSubs {r : Rule τ} {gr : GroundRule τ} (h : (matchRule r gr) = none) : ∀ s : Substitution τ, s.applyRule r ≠ gr := by
      simp only [ne_eq]
      intro s contra
      unfold applyRule at contra
      unfold GroundRule.toRule at contra
      simp only [Rule.mk.injEq] at contra

      cases eq : empty.matchAtom r.head gr.head with
      | none =>
        apply empty.matchAtomNoneThenNoSubs eq
        apply empty_isMinimal
        apply contra.left
      | some s' =>
        unfold matchRule at h
        have body_eq_len : r.body.length = gr.body.length := by
          have : (r.body.map s.applyAtom).length = (gr.body.map GroundAtom.toAtom).length := by rw [contra.right]
          rw [List.length_map, List.length_map] at this
          exact this
        simp only [body_eq_len, decide_true, eq, Option.some_bind, Option.filter_eq_none,
          Option.mem_def, not_true_eq_false, imp_false, Option.forall_ne, or_self] at h
        let atom_list := r.body.zip gr.body
        have h_atom_list : atom_list = r.body.zip gr.body := by simp [atom_list]
        apply s'.matchAtomListNoneThenNoSubs h
        · have isSome : (empty.matchAtom r.head gr.head).isSome := by simp [eq]
          have : s' = (empty.matchAtom r.head gr.head).get isSome := by simp [eq]
          rw [this]
          apply matchAtomIsMinimal
          constructor
          · apply empty_isMinimal
          · apply contra.left
        · have fst : r.body = atom_list.map Prod.fst := by
            rw [List.map_fst_zip]
            apply Nat.le_of_eq
            rw [body_eq_len]
          have snd : gr.body = atom_list.map Prod.snd := by
            rw [List.map_snd_zip]
            apply Nat.le_of_eq
            rw [body_eq_len]
          apply List.ext_get
          · simp [fst, snd]
          · intro n h₁ h₂
            simp only [List.get_eq_getElem, List.map_map, List.getElem_map, List.getElem_zip,
              Function.comp_apply]
            have := List.getElem_of_eq contra.right (i := n)
            simp only [List.map_map, List.length_map, List.length_zip, lt_inf_iff, List.getElem_map,
              List.getElem_zip, Function.comp_apply] at this
            apply this
            simp only [List.map_map, List.length_map, List.length_zip, lt_inf_iff, atom_list] at h₁
            rw [fst, h_atom_list]
            simp [h₁]
  end Substitution
end RuleMatching
