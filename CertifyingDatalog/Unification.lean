import CertifyingDatalog.Datalog

section term_matching
variable {τ: signature} [DecidableEq τ.constants][DecidableEq τ.vars] [DecidableEq τ.relationSymbols] [Hashable τ.constants] [Hashable τ.vars] [Hashable τ.relationSymbols]

def extend (s: substitution τ) (v: τ.vars) (c: τ.constants) : substitution τ := fun x => if x = v then Option.some c else s x

lemma s_subset_extend_s (s: substitution τ) (v: τ.vars) (c: τ.constants) (p: Option.isNone (s v)): s ⊆ extend s v c :=
by
  unfold extend
  unfold_projs
  unfold substitution_subs
  intro v'
  simp
  intro h
  by_cases v'_v: v' = v
  simp [v'_v]
  unfold substitution_domain at h
  simp at h
  rw [v'_v] at h
  exfalso
  cases h':(s v) with
  | none =>
    rw [h'] at h
    simp at h
  | some c' =>
    rw [h'] at p
    simp at p

  simp [v'_v]


def matchTerm (t: term τ)(c: τ.constants) (s: substitution τ): Option (substitution τ) :=
  match t with
  | term.constant c' =>
    if c = c'
      then Option.some s
      else Option.none
  | term.variableDL v =>
    if p:Option.isSome (s v)
    then  if Option.get (s v) p = c
          then
            Option.some s
          else
              Option.none
    else
      extend s v c

lemma matchTermFindsSolution (t: term τ) (c: τ.constants) (s: substitution τ) (h: Option.isSome (matchTerm t c s)): applySubstitutionTerm (Option.get (matchTerm t c s) h) t = c ∧ s ⊆ (Option.get (matchTerm t c s) h) :=
by
  cases t with
  | constant c' =>
    simp
    unfold matchTerm at h
    simp at h
    have c_c': c = c' := by
      by_contra h'
      simp [h'] at h
    constructor
    unfold matchTerm
    unfold applySubstitutionTerm
    simp [c_c']
    unfold matchTerm
    simp [c_c']
    apply substitution_subs_refl
  | variableDL v =>
    unfold matchTerm at h
    by_cases p: Option.isSome (s v)
    have sv_c: Option.get (s v) p = c := by
      by_contra h'
      simp [p, h'] at h
    have h': (Option.get (matchTerm (term.variableDL v) c s) h) = s := by
      unfold matchTerm
      simp [p, sv_c]
    simp
    constructor
    rw [h']
    unfold applySubstitutionTerm
    simp [p, sv_c]
    rw [h']
    apply substitution_subs_refl
    have h': Option.get (matchTerm (term.variableDL v) c s) h = extend s v c := by
      unfold matchTerm
      simp [p]
    rw [h']
    constructor
    unfold applySubstitutionTerm
    unfold extend
    simp
    apply s_subset_extend_s
    simp at p
    apply p

lemma matchTermFindsMinimalSolution' (t: term τ) (c: τ.constants) (s: substitution τ) (h: Option.isSome (matchTerm t c s)): ∀ (s': substitution τ), (s ⊆ s' ∧ applySubstitutionTerm s' t = c) → (Option.get (matchTerm t c s) h) ⊆ s' :=
by
  cases t with
  | constant c' =>
    unfold matchTerm at h
    simp at h
    have c_c': c = c' := by
      by_contra h'
      simp [h'] at h
    intros s' s'_prop
    unfold matchTerm
    simp [c_c', s'_prop]
  | variableDL v =>
    intros s' s_s'
    rcases s_s' with ⟨s_s', apply_s'⟩
    unfold matchTerm at h
    simp at h
    unfold matchTerm
    by_cases p: Option.isSome (s v) = true
    have h': Option.get (s v) p = c := by
      by_contra p'
      simp [p, p'] at h
    simp [p, h']
    simp [s_s']
    simp [p]
    by_contra h'
    unfold_projs at h'
    unfold substitution_subs at h'
    unfold extend at h'
    simp at h'
    rcases h' with ⟨x, x_prop⟩
    by_cases x_v: x = v
    simp [x_v] at x_prop
    cases sv: s' v with
    | some c' =>
      simp [sv] at x_prop
      unfold applySubstitutionTerm at apply_s'
      have p': Option.isSome (s' v) = true := by
        rw [sv]
        simp
      simp [p'] at apply_s'
      rw [option_get_iff_eq_some] at apply_s'
      simp [apply_s'] at sv
      rcases x_prop with ⟨_,right⟩
      exact absurd sv right
    | none =>
      unfold applySubstitutionTerm at apply_s'
      simp [sv] at apply_s'
    simp [x_v] at x_prop
    cases q:s x with
    | some c =>
      simp [q] at x_prop
      have s'x: s' x = some c := by
        apply substitution_subs_get s s' s_s' _ _ q
      simp [s'x] at x_prop
    | none =>
      rcases x_prop with ⟨left,_⟩
      unfold substitution_domain at left
      simp [x_v, q] at left


lemma matchTermNoneImpNoSolution (t: term τ) (c: τ.constants) (s: substitution τ) (h: Option.isNone (matchTerm t c s)): ¬ (∃(s': substitution τ), s ⊆ s' ∧ applySubstitutionTerm s' t = c) :=
by
  push_neg
  unfold matchTerm at h
  cases t with
  | constant c' =>
    simp at h
    have c_c': ¬ c' = c := by
      by_contra h'
      simp [h'] at h
    intros s' _
    unfold applySubstitutionTerm
    simp [c_c']
  | variableDL v =>
    simp at h
    have h': Option.isSome (s v) = true := by
      by_contra p
      simp [p] at h
    simp [h'] at h
    have p: ¬ Option.get (s v) h' = c := by
      by_contra q
      simp [q] at h
    intros s' s_s'
    unfold applySubstitutionTerm
    unfold_projs at s_s'
    unfold substitution_subs at s_s'
    specialize s_s' v
    simp
    rw [Option.isSome_iff_exists] at h'
    rcases h' with ⟨c', sv_c'⟩
    simp [sv_c'] at s_s'
    by_cases q: Option.isSome (s' v) = true
    simp [q]
    rw [Option.isSome_iff_exists] at q
    rcases q with ⟨b,s'v_b⟩
    simp [s'v_b] at *
    rw [← s_s']
    simp [sv_c'] at h
    by_contra q
    simp [q] at h
    unfold substitution_domain
    simp
    rw [sv_c']
    simp

    simp [q]

lemma matchTermIsSomeIffSolution (t: term τ) (c: τ.constants): Option.isSome (matchTerm t c emptySubstitution) ↔ ∃ (s: substitution τ), applySubstitutionTerm s t = c :=
by
  constructor
  intro h
  use Option.get (matchTerm t c emptySubstitution) h
  simp [matchTermFindsSolution]

  by_contra h
  push_neg at h
  rcases h with ⟨left, right⟩
  simp at right
  have h': ¬ ∃ s, emptySubstitution ⊆ s ∧ applySubstitutionTerm s t = term.constant c := by
    apply matchTermNoneImpNoSolution (h:= right)
  push_neg at h'
  rcases left with ⟨s, s_prop⟩
  specialize h' s
  have p: emptySubstitution ⊆ s := by
    apply emptySubstitutionIsMinimal
  specialize h' p
  exact absurd s_prop h'


end term_matching

section atom_matching
variable {τ: signature} [DecidableEq τ.constants] [DecidableEq τ.vars] [DecidableEq τ.relationSymbols] [Hashable τ.constants] [Hashable τ.vars] [Hashable τ.relationSymbols]

def matchTermList (s: substitution τ) (l1: List (term τ)) (l2: List (τ.constants)): Option (substitution τ) :=
  match l1 with
  | List.nil =>
    match l2 with
    | List.nil =>
      some s
    | List.cons _ _ =>
      none
  | List.cons hd tl =>
    match l2 with
    | List.nil => none
    | List.cons hd' tl' =>
      let s' := matchTerm hd hd' s
      if p: Option.isSome s'
      then matchTermList (Option.get s' p) tl tl'
      else none

lemma matchTermListFindsSolution (s: substitution τ) (l1: List (term τ)) (l2: List (τ.constants)) (h: Option.isSome (matchTermList s l1 l2)): List.map (applySubstitutionTerm (Option.get (matchTermList s l1 l2) h ) ) l1 = List.map term.constant l2 ∧ s ⊆ (Option.get (matchTermList s l1 l2) h ) :=
by
  induction l1 generalizing l2 s with
  | nil =>
    cases l2 with
    | nil =>
      constructor
      simp
      unfold matchTermList
      simp
      apply substitution_subs_refl
    | cons hd tl =>
      unfold matchTermList at h
      simp at h
  | cons hd tl ih =>
    cases l2 with
    | nil =>
      unfold matchTermList at h
      simp at h
    | cons hd' tl' =>
      unfold matchTermList at h
      simp at h
      have p : Option.isSome (matchTerm hd hd' s) = true := by
        by_contra p'
        simp [p'] at h
      simp [p] at h
      constructor
      simp
      constructor
      unfold matchTermList
      simp [p]
      apply subs_ext_groundTerm (s1:= Option.get (matchTerm hd hd' s) p)
      specialize ih (Option.get (matchTerm hd hd' s) p) tl' h
      simp [ih]
      simp [matchTermFindsSolution]

      unfold matchTermList
      simp [p, h]
      specialize ih (Option.get (matchTerm hd hd' s) p) tl' h
      simp [ih]

      unfold matchTermList
      simp [p,h]
      apply substitution_subs_trans (s2:= Option.get (matchTerm hd hd' s) p)
      simp [matchTermFindsSolution]
      specialize ih (Option.get (matchTerm hd hd' s) p) tl' h
      simp [ih]

lemma matchTermListFindsMinimalSolution (s: substitution τ) (l1: List (term τ)) (l2: List (τ.constants)) (h: Option.isSome (matchTermList s l1 l2)):∀ (s': substitution τ), List.map (applySubstitutionTerm s') l1 = List.map term.constant l2 ∧ s ⊆ s' → (Option.get (matchTermList s l1 l2) h ) ⊆ s' :=
by
  induction l1 generalizing l2 s with
  | nil =>
    intros s' s'_prop
    unfold matchTermList
    cases l2 with
    | nil =>
      simp [s'_prop]
    | cons hd tl =>
      unfold matchTermList at h
      simp at h
  | cons hd tl ih=>
    cases l2 with
    | nil =>
      unfold matchTermList at h
      simp at h
    | cons hd' tl' =>
      intros s' s'_prop
      unfold matchTermList
      unfold matchTermList at h
      have p : Option.isSome (matchTerm hd hd' s) = true := by
        by_contra p'
        simp [p'] at h
      simp [p]
      apply ih
      constructor
      simp at s'_prop
      simp [s'_prop]
      apply matchTermFindsMinimalSolution'
      constructor
      simp [s'_prop]
      simp at s'_prop
      simp [s'_prop]

lemma matchTermListNoneImplNoSolution (s: substitution τ) (l1: List (term τ)) (l2: List (τ.constants)) (h: Option.isNone (matchTermList s l1 l2)): ∀ (s': substitution τ), s ⊆ s' → ¬  List.map (applySubstitutionTerm s') l1 = List.map term.constant l2 :=
by
  intros s' s_s'
  induction l1 generalizing l2 s with
  | nil =>
    cases l2 with
    | nil =>
      unfold matchTermList at h
      simp at h
    | cons hd tl =>
      simp
  | cons hd tl ih =>
    cases l2 with
    | nil =>
      simp
    | cons hd' tl' =>
      unfold matchTermList at h
      simp at h
      by_cases p : Option.isSome (matchTerm hd hd' s) = true
      simp [p] at h
      specialize ih (Option.get (matchTerm hd hd' s) p) tl'
      simp
      intro s'_hd
      apply ih
      apply h
      apply matchTermFindsMinimalSolution'
      constructor
      apply s_s'
      simp [s'_hd]

      simp at p
      have h': ¬ ∃ (s1: substitution τ), s ⊆ s1 ∧ applySubstitutionTerm s1 hd = hd' := by
        apply matchTermNoneImpNoSolution (h:= p)
      push_neg at h'
      specialize h' s' s_s'
      simp [h']

def matchAtom (s: substitution τ) (a: atom τ) (ga: groundAtom τ): Option (substitution τ) :=
  if a.symbol = ga.symbol
  then
    matchTermList s a.atom_terms ga.atom_terms
  else none

lemma matchAtomFindsSolution (s: substitution τ) (a: atom τ) (ga: groundAtom τ) (h: Option.isSome (matchAtom s a ga)): applySubstitutionAtom (Option.get (matchAtom s a ga) h) a = ga ∧ s ⊆ (Option.get (matchAtom s a ga) h) :=
by
  unfold matchAtom at h
  have symbol_eq: a.symbol = ga.symbol := by
    by_contra p
    simp [p] at h
  simp [symbol_eq] at h
  unfold matchAtom
  simp [symbol_eq]
  unfold applySubstitutionAtom
  unfold groundAtom.toAtom
  simp [ruleEquality]
  rw [and_assoc]
  constructor
  apply symbol_eq
  apply matchTermListFindsSolution

lemma matchAtomFindsMinimalSolution (s: substitution τ) (a: atom τ) (ga: groundAtom τ) (h: Option.isSome (matchAtom s a ga)): ∀ (s': substitution τ), applySubstitutionAtom s' a = ga ∧ s ⊆ s' → (Option.get (matchAtom s a ga) h) ⊆ s' :=
by
  unfold matchAtom at h
  have symbol_eq: a.symbol = ga.symbol := by
    by_contra p
    simp [p] at h
  simp [symbol_eq] at h
  unfold matchAtom
  simp [symbol_eq]
  intro s'
  unfold applySubstitutionAtom
  unfold groundAtom.toAtom
  simp [symbol_eq]
  intros apply_s' s_s'
  apply matchTermListFindsMinimalSolution
  constructor
  apply apply_s'
  apply s_s'

lemma matchAtomNoneImplNoSolution (s: substitution τ) (a: atom τ) (ga: groundAtom τ) (h: Option.isNone (matchAtom s a ga)): ∀ (s': substitution τ), s ⊆ s' →  ¬ applySubstitutionAtom s' a = ga :=
by
  unfold matchAtom at h
  by_cases symbol_eq: a.symbol = ga.symbol
  unfold applySubstitutionAtom
  unfold groundAtom.toAtom
  simp [symbol_eq] at h
  have h': ∀ s', s ⊆ s' → ¬  List.map (applySubstitutionTerm s') a.atom_terms = List.map term.constant ga.atom_terms := by
    apply matchTermListNoneImplNoSolution
    apply h
  intros s' s_s'
  simp [symbol_eq]
  apply h' s' s_s'

  push_neg
  intro s' _
  unfold applySubstitutionAtom
  unfold groundAtom.toAtom
  simp [symbol_eq]

lemma matchAtomIsSomeIffSolution (a: atom τ) (ga: groundAtom τ): Option.isSome (matchAtom emptySubstitution a ga) ↔ ∃ (s': substitution τ), applySubstitutionAtom s' a = ga :=
by
  constructor
  intro h
  use Option.get (matchAtom emptySubstitution a ga) h
  simp [matchAtomFindsSolution]

  by_contra h
  push_neg at h
  simp at h
  rcases h with ⟨left,right⟩
  have h': ∀ (s': substitution τ), emptySubstitution ⊆ s' →  ¬ applySubstitutionAtom s' a = ga := by
    apply matchAtomNoneImplNoSolution (h:= right)
  push_neg at h'
  rcases left with ⟨s, s_prop⟩
  specialize h' s (emptySubstitutionIsMinimal (τ:= τ) s)
  exact absurd s_prop h'

end atom_matching

section rule_matching
variable {τ: signature} [DecidableEq τ.constants][DecidableEq τ.vars] [DecidableEq τ.relationSymbols] [Hashable τ.constants] [Hashable τ.vars] [Hashable τ.relationSymbols]

def matchAtomList (s: substitution τ) (l1: List (atom τ)) (l2: List (groundAtom τ)): Option (substitution τ) :=
  match l1 with
    | List.nil =>
      match l2 with
      | List.nil => some s
      | List.cons _ _ => none
    | List.cons hd tl =>
      match l2 with
      | List.nil => none
      | List.cons hd' tl' =>
        let s' := matchAtom s hd hd'
        if p: Option.isSome s'
        then matchAtomList (Option.get s' p) tl tl'
        else none

lemma matchAtomListFindsSolution (s: substitution τ) (l1: List (atom τ)) (l2: List (groundAtom τ)) (h: Option.isSome (matchAtomList s l1 l2)): List.map (applySubstitutionAtom (Option.get (matchAtomList s l1 l2) h )) l1 = List.map groundAtom.toAtom l2 ∧ s ⊆ (Option.get (matchAtomList s l1 l2) h ):=
by
  induction l1 generalizing l2 s with
  | nil =>
    cases l2 with
    | nil =>
      simp
      unfold matchAtomList
      simp
      apply substitution_subs_refl
    | cons hd tl =>
      unfold matchAtomList at h
      simp at h
  | cons hd tl ih =>
    cases l2 with
    | nil =>
      unfold matchAtomList at h
      simp at h
    | cons hd' tl' =>
      unfold matchAtomList at h
      simp at h
      unfold matchAtomList
      have p: Option.isSome (matchAtom s hd hd') = true := by
        by_contra h'
        simp [h'] at h
      simp [p]
      simp [p] at h
      specialize ih (Option.get (matchAtom s hd hd') p) tl' h
      simp [ih]
      constructor
      apply subs_ext_groundAtom (s1:= Option.get (matchAtom s hd hd') p)
      simp [ih]
      simp [matchAtomFindsSolution]
      apply substitution_subs_trans (s2:=Option.get (matchAtom s hd hd') p)
      simp [matchAtomFindsSolution]
      simp [ih]

lemma matchAtomListFindsMinimalSolution (s: substitution τ) (l1: List (atom τ)) (l2: List (groundAtom τ)) (h: Option.isSome (matchAtomList s l1 l2)): ∀ (s': substitution τ), List.map (applySubstitutionAtom s') l1 = List.map groundAtom.toAtom l2 ∧ s ⊆ s' → (Option.get (matchAtomList s l1 l2) h ) ⊆ s' :=
by
  intros s' s_s'
  induction l1 generalizing l2 s with
  | nil =>
    cases l2 with
    | nil =>
      unfold matchAtomList
      simp [s_s']
    | cons hd tl =>
      simp at s_s'
  | cons hd tl ih =>
    cases l2 with
    | nil =>
      simp at s_s'
    | cons hd' tl' =>
      unfold matchAtomList
      simp
      unfold matchAtomList at h
      simp at h
      have p : Option.isSome (matchAtom s hd hd') = true := by
        by_contra q
        simp [q] at h
      simp [p]
      simp [p] at h
      apply ih
      rcases s_s' with ⟨map_s', s_s'⟩
      simp at map_s'
      constructor
      simp [map_s']
      apply matchAtomFindsMinimalSolution
      constructor
      simp [map_s']
      apply s_s'

lemma matchAtomListNoneImplNoSolution (s: substitution τ) (l1: List (atom τ)) (l2: List (groundAtom τ)) (h: Option.isNone (matchAtomList s l1 l2)): ∀ (s': substitution τ), s ⊆ s' → ¬  List.map (applySubstitutionAtom s') l1 = List.map groundAtom.toAtom l2 :=
by
  push_neg
  intros s' s_s'
  induction l1 generalizing l2 s with
  | nil =>
    cases l2 with
    | nil =>
      unfold matchAtomList at h
      simp at h
    | cons hd tl =>
      simp
  | cons hd tl ih =>
    cases l2 with
    | nil =>
      simp
    | cons hd' tl' =>
      unfold matchAtomList at h
      simp at h
      by_cases p: Option.isSome (matchAtom s hd hd') = true
      simp [p] at h
      simp
      intro h'
      specialize ih (Option.get (matchAtom s hd hd') p) tl'
      apply ih
      apply h
      apply matchAtomFindsMinimalSolution
      simp [h', s_s']

      have h': ∀ (s': substitution τ), s ⊆ s' → ¬ applySubstitutionAtom s' hd = hd' := by
        apply matchAtomNoneImplNoSolution
        simp at p
        apply p
      push_neg at h'
      specialize h' s' s_s'
      simp
      intro q
      exfalso
      exact absurd q h'


def matchRule (r: rule τ) (gr: groundRule τ): Option (substitution τ):=
  let s := matchAtom emptySubstitution r.head gr.head
  if p: Option.isSome s
  then matchAtomList (Option.get s p) r.body gr.body
  else none

lemma matchRuleFindsSolution (r: rule τ) (gr: groundRule τ)  (h: Option.isSome (matchRule r gr) = true): applySubstitutionRule (Option.get (matchRule r gr) h) r = gr :=
by
  unfold applySubstitutionRule
  unfold groundRule.toRule
  unfold matchRule at *
  simp at h
  simp
  have p: Option.isSome (matchAtom emptySubstitution r.head gr.head) = true := by
    by_contra q
    simp [q] at h
  simp [p]
  simp [p] at h
  have h': List.map (applySubstitutionAtom (Option.get (matchAtomList (Option.get (matchAtom emptySubstitution r.head gr.head) p) r.body gr.body) h )) r.body = List.map groundAtom.toAtom gr.body ∧ (Option.get (matchAtom emptySubstitution r.head gr.head) p) ⊆ (Option.get (matchAtomList (Option.get (matchAtom emptySubstitution r.head gr.head) p) r.body gr.body) h ) := by
    apply matchAtomListFindsSolution
  rcases h' with ⟨left,right⟩
  constructor
  apply subs_ext_groundAtom (s1:= Option.get (matchAtom emptySubstitution r.head gr.head) p)
  apply right
  simp [matchAtomFindsSolution]
  apply left

lemma matchRuleNoneImplNoSolution (r: rule τ) (gr: groundRule τ) (h: Option.isNone (matchRule r gr) = true): ¬ ∃ (s: substitution τ), applySubstitutionRule s r = gr :=
by
  push_neg
  intro s
  unfold matchRule at h
  simp at h
  unfold applySubstitutionRule
  unfold groundRule.toRule
  simp
  intro s_hd
  by_cases p: Option.isSome (matchAtom emptySubstitution r.head gr.head)
  simp [p] at h
  have h': ∀ (s': substitution τ), Option.get (matchAtom emptySubstitution r.head gr.head) p ⊆ s' → ¬  List.map (applySubstitutionAtom s') r.body = List.map groundAtom.toAtom gr.body := by
    apply matchAtomListNoneImplNoSolution (h:= h)
  specialize h' s
  apply h'
  apply matchAtomFindsMinimalSolution
  simp [s_hd]
  apply emptySubstitutionIsMinimal

  simp at p
  have n_s_hd: ¬ applySubstitutionAtom s r.head = groundAtom.toAtom gr.head := by
    apply matchAtomNoneImplNoSolution (h:= p)
    apply emptySubstitutionIsMinimal
  exfalso
  exact absurd s_hd n_s_hd

theorem matchRuleIsSomeIffSolution (r: rule τ) (gr: groundRule τ) : Option.isSome (matchRule r gr) ↔ ∃ (s: substitution τ), applySubstitutionRule s r = gr :=
by
  simp
  constructor
  intro h
  use Option.get (matchRule r gr) h
  apply matchRuleFindsSolution

  by_contra h
  push_neg at h
  rcases h with ⟨left,right⟩
  simp at right
  have h: ¬ ∃ (s: substitution τ), applySubstitutionRule s r = gr := by
    apply matchRuleNoneImplNoSolution (h:= right)
  exact absurd left h

end rule_matching
