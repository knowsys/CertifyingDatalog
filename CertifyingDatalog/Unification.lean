module

public import CertifyingDatalog.Datalog.Substitution
import CertifyingDatalog.Basic

@[expose] public section

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
        simp only [Set.mem_ofPred_eq] at h
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
      simp only [matchTerm, decide_implies, dite_eq_ite, Bool.ite_true_right, Bool.decide_eq_true,
        Option.not_isSome] at h ⊢
      cases t with
      | constant c' =>
        simp only [Option.get_ite]
        apply Substitution.subset_refl
      | variableDL v =>
        simp only [Option.isSome_filter, Option.any_some, Bool.or_eq_true,
          Option.isNone_iff_eq_none, decide_eq_true_eq] at h
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
      simp only [matchTerm, decide_implies, dite_eq_ite, Bool.ite_true_right, Bool.decide_eq_true,
        Option.not_isSome] at h ⊢
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
        simp [applyTerm, extend]

    lemma matchTermIsMinimal [DecidableEq τ.vars] [DecidableEq τ.constants] {s: Substitution τ} {t: Term τ} {c: τ.constants} (h : (s.matchTerm t c).isSome) : ∀ s' : Substitution τ, s ⊆ s' ∧ s'.applyTerm t = c -> ((s.matchTerm t c).get h) ⊆ s' := by
      intro s' ⟨subset, apply_t⟩
      simp only [matchTerm, decide_implies, dite_eq_ite, Bool.ite_true_right, Bool.decide_eq_true,
        Option.not_isSome] at h ⊢
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
          simp only [Substitution.subset, domain, extend, Set.mem_ofPred_eq]
          intro v'
          by_cases v_v': v' = v
          · simp only [v_v', ↓reduceIte, Option.isSome_some, forall_const]
            simp only [applyTerm] at apply_t
            split at apply_t
            · rename_i o c' hc'
              simp only [hc', Option.some.injEq]
              simp only [Term.constant.injEq] at apply_t
              exact apply_t.symm
            · simp at apply_t
          · simp only [v_v', ↓reduceIte]
            apply subset
        | inr h =>
          unfold_projs
          simp only [Substitution.subset, domain, extend, Set.mem_ofPred_eq]
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
      simp only [matchTerm, decide_implies, dite_eq_ite, Bool.ite_true_right, Bool.decide_eq_true,
        Option.not_isSome] at h
      cases t with
      | constant c' =>
        unfold applyTerm at apply_t
        simp only [Term.constant.injEq] at apply_t
        simp [apply_t] at h
      | variableDL v =>
        simp only [Option.filter_eq_none_iff, Option.some.injEq,
          Bool.or_eq_true, Option.isNone_iff_eq_none, decide_eq_true_eq, not_or,
          Option.ne_none_iff_exists, forall_eq', extend, ↓reduceIte] at h
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
        simp only [Function.comp_apply, List.cons.injEq] at apply_t
        cases eq : s.matchTerm pair.fst pair.snd with
        | none => simp [matchTermList, eq] at h
        | some s'' =>
          simp only [matchTermList, eq]
          simp only [matchTermList, eq] at h
          simp only [List.map_map, and_imp] at ih
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
        simp only [Function.comp_apply,  List.cons.injEq] at apply_t
        cases eq : s.matchTerm pair.fst pair.snd with
        | none =>
          apply matchTermNoneThenNoSubs eq s' subset
          apply apply_t.left
        | some s'' =>
          simp only [matchTermList, eq] at h
          simp only [List.map_map] at ih
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
      simp only [Atom.eq_GroundAtom_iff, applyAtom_symbol, applyAtom_terms, List.length_map,
        List.getElem_map]
      have symb_eq : a.symbol = ga.symbol := by
        apply Decidable.by_contra
        intro contra
        unfold matchAtom at h
        simp [contra] at h
      have term_lists_eq_len : a.atom_terms.length = ga.atom_terms.length := by rw [a.term_length, ga.term_length, symb_eq]
      simp only [matchAtom, symb_eq, ↓reduceIte, true_and] at h ⊢
      apply matchTermListYieldsSubs at h
      simp only [List.map_map, List.map_inj_left, Function.comp_apply, Prod.forall] at h
      use term_lists_eq_len
      intro i hi
      apply h
      simp only [List.mem_iff_get, List.get_eq_getElem, List.getElem_zip, Prod.mk.injEq]
      use ⟨i, by simp[hi, ← term_lists_eq_len]⟩

    lemma matchAtomIsMinimal {s: Substitution τ} {a: Atom τ} {ga: GroundAtom τ} (h : (s.matchAtom a ga).isSome) : ∀ s' : Substitution τ, s ⊆ s' ∧ s'.applyAtom a = ga -> ((s.matchAtom a ga).get h) ⊆ s' := by
      intro s' ⟨subset, apply_a⟩
      simp only [Atom.eq_GroundAtom_iff, applyAtom_symbol, applyAtom_terms, List.length_map,
        List.getElem_map] at apply_a
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
          simp only [List.get_eq_getElem, List.map_map, List.getElem_map, List.getElem_zip,
            Function.comp_apply]
          apply terms_eq.2
          simp only [List.map_map, List.length_map, List.length_zip, lt_min_iff] at h₁
          apply h₁.1

    lemma matchAtomNoneThenNoSubs {s: Substitution τ} {a: Atom τ} {ga: GroundAtom τ} (h : (s.matchAtom a ga) = none) : ∀ s' : Substitution τ, s ⊆ s' -> s'.applyAtom a ≠ ga := by
      intro s' subset apply_a
      simp only [Atom.eq_GroundAtom_iff, applyAtom_symbol, applyAtom_terms, List.length_map,
        List.getElem_map] at apply_a
      unfold matchAtom at h
      unfold applyAtom at apply_a
      have ⟨symb_eq, terms_eq⟩ := apply_a
      have term_lists_eq_len : a.atom_terms.length = ga.atom_terms.length := by rw [a.term_length, ga.term_length, symb_eq]
      simp only [symb_eq, ↓reduceIte] at h
      let term_list : List ((Term τ) × τ.constants) := a.atom_terms.zip ga.atom_terms
      apply s.matchTermListNoneThenNoSubs h s' subset
      simp only [List.map_map, List.map_inj_left, List.mem_iff_get, List.get_eq_getElem,
        List.getElem_zip, Function.comp_apply, forall_exists_index, forall_apply_eq_imp_iff]
      intro i
      apply terms_eq.2
      grind
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
          simp only [List.map_cons, List.map_map, List.cons.injEq]
          constructor
          · unfold matchAtomList at h
            cases eq : s.matchAtom pair.fst pair.snd with
            | none => simp [eq] at h
            | some s' =>
              apply subset_applyAtom_eq _ matchAtomResult
              simp_rw [this]
              apply matchAtomListSubset
          · simp_rw [this]
            simp only [List.map_map] at ih
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
          simp only [eq, Option.bind_some, Option.isSome_iff_exists, Option.filter_eq_some_iff,
            decide_eq_true_eq, exists_and_right] at h
          apply And.right h
        simp [Rule.eq_GroundRule_iff, matchRule]
        constructor
        · rw [s.subset_applyAtom_eq]
          · unfold matchRule
            simp [eq]
            apply matchAtomListSubset
          · have : (empty.matchAtom r.head gr.head).isSome := by simp [eq]
            have : s = (empty.matchAtom r.head gr.head).get this := by simp [eq]
            rw [this]
            apply matchAtomYieldsSubs
        · simp only [body_eq_len, eq, Option.get_some, exists_true_left]
          simp only [matchRule, body_eq_len, decide_true, eq, Option.bind_some,
            Option.filter_true] at h
          let atom_list := r.body.zip gr.body
          have match_a_list := s.matchAtomListYieldsSubs h
          simp only [List.map_map, List.map_inj_left, List.mem_iff_getElem, List.getElem_zip,
            List.length_zip, lt_min_iff, Function.comp_apply, forall_exists_index, forall_and_index,
            Prod.forall, Prod.mk.injEq] at match_a_list
          intro i hi
          rw [← match_a_list _ _ i (by simp [body_eq_len, hi]) hi (by rfl) (by rfl)]

    theorem matchRuleNoneThenNoSubs {r : Rule τ} {gr : GroundRule τ} (h : (matchRule r gr) = none) : ∀ s : Substitution τ, s.applyRule r ≠ gr := by
      simp only [ne_eq]
      intro s contra
      simp only [applyRule, Rule.eq_GroundRule_iff, List.length_map, List.getElem_map] at contra
      cases eq : empty.matchAtom r.head gr.head with
      | none =>
        apply empty.matchAtomNoneThenNoSubs eq (s' := s)
        apply empty_isMinimal
        rw [contra.1]
      | some s' =>
        simp only [matchRule, contra.2.1, decide_true, eq, Option.bind_some,
          Option.filter_eq_none_iff, not_true_eq_false, imp_false, ne_eq] at h
        have matchNone : s'.matchAtomList (r.body.zip gr.body) = none := by
          by_contra p
          simp only [Option.eq_none_iff_forall_some_ne, ne_eq, not_forall, not_not] at p
          rcases p with ⟨t, ht⟩
          specialize h t
          simp [ht] at h
        have hs : s' ⊆ s := by
          have := matchAtomIsMinimal (s:= empty) (a:= r.head) (ga := gr.head)
          simp only [eq, Option.isSome_some, Option.get_some, and_imp, forall_const] at this
          apply this _ (by exact empty_isMinimal s)
          rw [contra.1]
        apply matchAtomListNoneThenNoSubs matchNone _ hs
        simp only [List.map_map, List.map_inj_left, List.mem_iff_getElem, List.getElem_zip,
          List.length_zip, lt_min_iff, Function.comp_apply, forall_exists_index, forall_and_index,
          Prod.forall, Prod.mk.injEq]
        rcases contra with ⟨_, h₁, h₂⟩
        intro a ga i hi₁ hi₂ h₃ h₄
        simp [← h₃, ← h₄, h₂, hi₁]
  end Substitution
end RuleMatching
