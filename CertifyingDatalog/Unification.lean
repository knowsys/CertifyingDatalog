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

    def matchTerm [DecidableEq τ.vars] [DecidableEq τ.constants] (s: Substitution τ) (t: Term τ) (c: τ.constants) : Option (Substitution τ) :=
      match t with
      | .constant c' => if c = c' then Option.some s else Option.none
      | .variableDL v => match s v with
        | .some c' => if c = c' then Option.some s else Option.none
        | .none => s.extend v c

    lemma matchTermSubset [DecidableEq τ.vars] [DecidableEq τ.constants] {s: Substitution τ} {t: Term τ} {c: τ.constants} (h : (s.matchTerm t c).isSome) : s ⊆ ((s.matchTerm t c).get h) := by
      unfold matchTerm
      cases t with
      | constant c' =>
        simp
        apply Substitution.subset_refl
      | variableDL v =>
        cases eq : (s v) with
        | none =>
          simp [eq]
          apply extend_subset
          simp [eq]
        | some c' =>
          simp [eq]
          apply Substitution.subset_refl

    lemma matchTermYieldsSubs [DecidableEq τ.vars] [DecidableEq τ.constants] {s: Substitution τ} {t: Term τ} {c: τ.constants} (h : (s.matchTerm t c).isSome) : ((s.matchTerm t c).get h).applyTerm t = c := by
      unfold matchTerm
      cases t with
      | constant c' =>
        simp only [Option.get_ite]
        cases Decidable.em (c = c') with
        | inl eq =>
          simp only [eq]
          unfold applyTerm
          simp
        | inr neq =>
          unfold matchTerm at h
          simp [neq] at h
      | variableDL v =>
        cases eq : (s v) with
        | none =>
          simp only [eq, Option.get_some]
          unfold applyTerm
          unfold extend
          simp
        | some c' =>
          simp only [eq, Option.get_ite]
          cases Decidable.em (c = c') with
          | inl eq2 =>
            simp only [eq2]
            unfold applyTerm
            simp [eq]
          | inr neq =>
            unfold matchTerm at h
            simp [eq, neq] at h

    lemma matchTermIsMinimal [DecidableEq τ.vars] [DecidableEq τ.constants] {s: Substitution τ} {t: Term τ} {c: τ.constants} (h : (s.matchTerm t c).isSome) : ∀ s' : Substitution τ, s ⊆ s' ∧ s'.applyTerm t = c -> ((s.matchTerm t c).get h) ⊆ s' := by
      intro s' ⟨subset, apply_t⟩
      unfold matchTerm
      cases t with
      | constant c' =>
        simp only [Option.get_ite]
        apply subset
      | variableDL v =>
        cases eq2 : (s v) with
        | some c' =>
          simp only [eq2, Option.get_ite]
          apply subset
        | none =>
          simp only [eq2, Option.get_some]
          unfold extend
          unfold_projs
          unfold Substitution.subset
          intro v' v'_dom
          by_cases h': (v' = v)
          · simp only [h', ↓reduceIte]
            unfold applyTerm at apply_t
            simp only at apply_t
            cases eq3 : s' v with
            | none => simp [eq3] at apply_t
            | some c' => simp [eq3] at apply_t; rw [apply_t]
          · simp only [h', ↓reduceIte]
            apply subset
            unfold domain at v'_dom
            simp only [Set.mem_setOf_eq, h', ↓reduceIte] at v'_dom
            unfold domain
            simp only [Set.mem_setOf_eq]
            exact v'_dom

    lemma matchTermNoneThenNoSubs [DecidableEq τ.vars] [DecidableEq τ.constants] {s: Substitution τ} {t: Term τ}{c: τ.constants} (h : (s.matchTerm t c) = none) : ∀ s' : Substitution τ, s ⊆ s' -> s'.applyTerm t ≠ c := by
      intro s' subset apply_t
      unfold matchTerm at h
      cases t with
      | constant c' =>
        unfold applyTerm at apply_t
        simp only [Term.constant.injEq] at apply_t
        simp [apply_t] at h
      | variableDL v =>
        simp only [Option.isNone_iff_eq_none] at h
        cases eq : (s v) with
        | none => simp [eq] at h
        | some c' =>
          simp only [eq, ite_eq_right_iff, reduceCtorEq, imp_false] at h
          have : s.applyTerm (Term.variableDL v) = Term.constant c' := by unfold applyTerm; simp [eq]
          rw [subset_applyTerm_eq subset this] at apply_t
          injection apply_t with apply_t
          simp [apply_t] at h
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

    lemma matchTermListYieldsSubs {s: Substitution τ} {l: List ((Term τ) × τ.constants)} (h : (s.matchTermList l).isSome) : (l.map Prod.fst).map ((s.matchTermList l).get h).applyTerm = l.map Prod.snd := by
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
            simp only [List.map_map, List.pure_def, List.bind_eq_flatMap] at ih
            apply ih

    lemma matchTermListIsMinimal {s: Substitution τ} {l: List ((Term τ) × τ.constants)} (h : (s.matchTermList l).isSome) : ∀ s' : Substitution τ, s ⊆ s' ∧ ((l.map Prod.fst).map s'.applyTerm = l.map Prod.snd) -> ((s.matchTermList l).get h) ⊆ s' := by
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

    lemma matchTermListNoneThenNoSubs {s: Substitution τ} {l: List ((Term τ) × τ.constants)} (h : (s.matchTermList l) = none) : ∀ s' : Substitution τ, s ⊆ s' -> ¬ (l.map Prod.fst).map s'.applyTerm = l.map Prod.snd := by
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
        rw [← fst, ← snd] at match_t_list
        rw [match_t_list]
        simp [List.map_eq_flatMap]

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
      · have fst : a.atom_terms = term_list.map Prod.fst := by
          rw [List.map_fst_zip]
          apply Nat.le_of_eq
          rw [term_lists_eq_len]
        have snd : ga.atom_terms = term_list.map Prod.snd := by
          rw [List.map_snd_zip]
          apply Nat.le_of_eq
          rw [term_lists_eq_len]
        rw [← fst, ← snd]
        rw [terms_eq]
        simp [List.map_eq_flatMap]

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
      rw [← fst, ← snd]
      rw [terms_eq]
      simp [List.map_eq_flatMap]
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

    lemma matchAtomListYieldsSubs {s: Substitution τ} {l: List ((Atom τ) × (GroundAtom τ))} (h : (s.matchAtomList l).isSome) : (l.map Prod.fst).map ((s.matchAtomList l).get h).applyAtom = l.map Prod.snd := by
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

    lemma matchAtomListNoneThenNoSubs {s: Substitution τ} {l: List ((Atom τ) × (GroundAtom τ))} (h : (s.matchAtomList l) = none) : ∀ s' : Substitution τ, s ⊆ s' -> ¬ (l.map Prod.fst).map s'.applyAtom = l.map Prod.snd := by
      induction l generalizing s with
      | nil => simp [matchAtomList] at h
      | cons pair l ih =>
        intro s' subset apply_t
        rw [List.map_map] at apply_t
        unfold List.map at apply_t
        simp only [Function.comp_apply, List.pure_def, List.bind_eq_flatMap, List.flatMap_cons,
          List.singleton_append, List.cons.injEq] at apply_t

        cases eq : s.matchAtom pair.fst pair.snd with
        | none =>
          apply matchAtomNoneThenNoSubs eq
          apply subset
          apply apply_t.left
        | some s'' =>
          simp [matchAtomList, eq] at h
          simp [List.map_map] at ih
          apply ih h s' _ apply_t.right

          have isSome : (s.matchAtom pair.fst pair.snd).isSome := by simp [eq]
          have : s'' = (s.matchAtom pair.fst pair.snd).get isSome := by simp [eq]
          rw [this]
          apply matchAtomIsMinimal
          constructor
          · apply subset
          · apply apply_t.left

    def matchRule (r: Rule τ) (gr: GroundRule τ): Option (Substitution τ):=
      match empty.matchAtom r.head gr.head with
      | .none => Option.none
      | .some s => if r.body.length = gr.body.length then s.matchAtomList (r.body.zip gr.body) else Option.none

    theorem matchRuleYieldsSubs {r : Rule τ} {gr : GroundRule τ} (h : (matchRule r gr).isSome) : ((matchRule r gr).get h).applyRule r = gr := by
      cases eq : empty.matchAtom r.head gr.head with
      | none => simp [matchRule, eq] at h
      | some s =>
        have body_eq_len : r.body.length = gr.body.length := by
          unfold matchRule at h
          simp only [eq] at h
          apply Decidable.by_contra
          intro contra
          simp [contra] at h
        unfold applyRule
        unfold GroundRule.toRule
        simp only [Rule.mk.injEq]
        constructor
        · apply s.subset_applyAtom_eq
          · unfold matchRule
            simp only [eq, body_eq_len, ↓reduceIte]
            apply matchAtomListSubset
          · have : (empty.matchAtom r.head gr.head).isSome := by simp [eq]
            have : s = (empty.matchAtom r.head gr.head).get this := by simp [eq]
            rw [this]
            apply matchAtomYieldsSubs
        · simp only [matchRule, eq, body_eq_len, ↓reduceIte]
          simp only [matchRule, eq, body_eq_len, ↓reduceIte] at h
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
          rw [← fst, ← snd] at match_a_list
          rw [match_a_list]
          simp [List.map_eq_flatMap]

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
        simp only [eq, body_eq_len] at h
        let atom_list := r.body.zip gr.body
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
          rw [← fst, ← snd]
          rw [contra.right]
          simp [List.map_eq_flatMap]
  end Substitution
end RuleMatching
