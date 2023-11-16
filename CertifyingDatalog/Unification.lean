import CertifyingDatalog.Datalog

section term_matching
variable {τ: signature} [DecidableEq τ.constants][DecidableEq τ.vars]

def extend (s: substitution τ) (v: τ.vars) (c: τ.constants) : substitution τ := fun x => if x = v then Option.some c else s x

lemma s_subset_extend_s (s: substitution τ) (v: τ.vars) (c: τ.constants) (p: Option.isNone (s v)): s ⊆ extend s v c :=
by
  unfold extend
  unfold_projs
  unfold substitution_subs
  intro v'
  cases h: s v' with
  | some c' =>
    simp
    have v'_v: ¬ v' = v
    by_contra h'
    rw [← h']  at p
    rw [h] at p
    simp at p
    simp [v'_v, h]
  | none =>
    simp

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
    have c_c': c = c'
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
    have sv_c: Option.get (s v) p = c
    by_contra h'
    simp [p, h'] at h
    have h': (Option.get (matchTerm (term.variableDL v) c s) h) = s
    unfold matchTerm
    simp [p, sv_c]
    simp
    constructor
    rw [h']
    unfold applySubstitutionTerm
    simp [p, sv_c]
    rw [h']
    apply substitution_subs_refl
    have h': Option.get (matchTerm (term.variableDL v) c s) h = extend s v c
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
    have c_c': c = c'
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
    have h': Option.get (s v) p = c
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
      have p': Option.isSome (s' v) = true
      rw [sv]
      simp
      simp [p'] at apply_s'
      rw [option_get_iff_eq_some] at apply_s'
      simp [apply_s'] at sv
      exact absurd sv x_prop
    | none =>
      unfold applySubstitutionTerm at apply_s'
      simp [sv] at apply_s'
    simp [x_v] at x_prop
    cases q:s x with
    | some c =>
      simp [q] at x_prop
      have s'x: s' x = some c
      apply substitution_subs_get s s' s_s' _ _ q
      simp [s'x] at x_prop
    | none =>
      simp [q] at x_prop

lemma matchTermNoneImpNoSolution (t: term τ) (c: τ.constants) (s: substitution τ) (h: Option.isNone (matchTerm t c s)): ¬ (∃(s': substitution τ), s ⊆ s' ∧ applySubstitutionTerm s' t = c) :=
by
  push_neg
  unfold matchTerm at h
  cases t with
  | constant c' =>
    simp at h
    have c_c': ¬ c' = c
    by_contra h'
    simp [h'] at h
    intros s' _
    unfold applySubstitutionTerm
    simp [c_c']
  | variableDL v =>
    simp at h
    have h': Option.isSome (s v) = true
    by_contra p
    simp [p] at h
    simp [h'] at h
    have p: ¬ Option.get (s v) h' = c
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
  have h': ¬ ∃ s, emptySubstitution ⊆ s ∧ applySubstitutionTerm s t = term.constant c
  apply matchTermNoneImpNoSolution (h:= right)
  push_neg at h'
  rcases left with ⟨s, s_prop⟩
  specialize h' s
  have p: emptySubstitution ⊆ s
  apply emptySubstitutionIsMinimal
  specialize h' p
  exact absurd s_prop h'


end term_matching

section atom_matching
variable {τ: signature} [DecidableEq τ.constants][DecidableEq τ.vars] [DecidableEq τ.relationSymbols]

def matchTermList (s: substitution τ) (l1: List (term τ)) (l2: List (τ.constants)): Option (substitution τ) :=
  match l1 with
  | List.nil => some s
  | List.cons hd tl =>
    match l2 with
    | List.nil => none
    | List.cons hd' tl' =>
      let s' := matchTerm hd hd' s
      if p: Option.isSome s'
      then matchTermList (Option.get s' p) tl tl'
      else none

lemma matchTermListFindsSolution (s: substitution τ) (l1: List (term τ)) (l2: List (τ.constants)) (len: l1.length = l2.length) (h: Option.isSome (matchTermList s l1 l2)): List.map (applySubstitutionTerm (Option.get (matchTermList s l1 l2) h ) ) l1 = List.map term.constant l2 ∧ s ⊆ (Option.get (matchTermList s l1 l2) h ) :=
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
      simp at len
  | cons hd tl ih =>
    cases l2 with
    | nil =>
      simp at len
    | cons hd' tl' =>
      simp at len
      unfold matchTermList at h
      simp at h
      have p : Option.isSome (matchTerm hd hd' s) = true
      by_contra p'
      simp [p'] at h
      simp [p] at h
      constructor
      simp
      constructor
      unfold matchTermList
      simp [p]
      apply subs_ext_groundTerm (s1:= Option.get (matchTerm hd hd' s) p)
      specialize ih (Option.get (matchTerm hd hd' s) p) tl' len h
      simp [ih]
      simp [matchTermFindsSolution]

      unfold matchTermList
      simp [p, h]
      specialize ih (Option.get (matchTerm hd hd' s) p) tl' len h
      simp [ih]

      unfold matchTermList
      simp [p,h]
      apply substitution_subs_trans (s2:= Option.get (matchTerm hd hd' s) p)
      simp [matchTermFindsSolution]
      specialize ih (Option.get (matchTerm hd hd' s) p) tl' len h
      simp [ih]

lemma matchTermListFindsMinimalSolution (s: substitution τ) (l1: List (term τ)) (l2: List (τ.constants)) (len: l1.length = l2.length) (h: Option.isSome (matchTermList s l1 l2)):∀ (s': substitution τ), List.map (applySubstitutionTerm s') l1 = List.map term.constant l2 ∧ s ⊆ s' → (Option.get (matchTermList s l1 l2) h ) ⊆ s' :=
by
  induction l1 generalizing l2 s with
  | nil =>
    intros s' s'_prop
    unfold matchTermList
    simp [s'_prop]
  | cons hd tl ih=>
    cases l2 with
    | nil =>
      simp at len
    | cons hd' tl' =>
      intros s' s'_prop
      unfold matchTermList
      unfold matchTermList at h
      have p : Option.isSome (matchTerm hd hd' s) = true
      by_contra p'
      simp [p'] at h
      simp [p]
      apply ih
      simp at len
      apply len
      constructor
      simp at s'_prop
      simp [s'_prop]
      apply matchTermFindsMinimalSolution'
      constructor
      simp [s'_prop]
      simp at s'_prop
      simp [s'_prop]

lemma matchTermListNoneImplNoSolution (s: substitution τ) (l1: List (term τ)) (l2: List (τ.constants)) (len: l1.length = l2.length) (h: Option.isNone (matchTermList s l1 l2)): ¬ ∃ (s': substitution τ), s ⊆ s' ∧ List.map (applySubstitutionTerm s') l1 = List.map term.constant l2 :=
by
  push_neg
  intros s' s_s'
  induction l1 generalizing l2 s with
  | nil =>
    cases l2 with
    | nil =>
      unfold matchTermList at h
      simp at h
    | cons hd tl =>
      simp at len
  | cons hd tl ih =>
    cases l2 with
    | nil =>
      simp at len
    | cons hd' tl' =>
      unfold matchTermList at h
      simp at h
      by_cases p : Option.isSome (matchTerm hd hd' s) = true
      simp [p] at h
      specialize ih (Option.get (matchTerm hd hd' s) p) tl'
      simp
      intro s'_hd
      apply ih
      simp at len
      apply len
      apply h
      apply matchTermFindsMinimalSolution'
      constructor
      apply s_s'
      simp [s'_hd]

      simp at p
      have h': ¬ ∃ (s1: substitution τ), s ⊆ s1 ∧ applySubstitutionTerm s1 hd = hd'
      apply matchTermNoneImpNoSolution (h:= p)
      push_neg at h'
      specialize h' s' s_s'
      simp [h']

def matchAtom (s: substitution τ) (a: atom τ) (ga: groundAtom τ): Option (substitution τ) :=
  if a.symbol = ga.symbol
  then
    if a.atom_terms.length = ga.atom_terms.length
    then matchTermList s a.atom_terms ga.atom_terms
    else none
  else none

lemma matchAtomFindsSolution (s: substitution τ) (a: atom τ) (ga: groundAtom τ) (h: Option.isSome (matchAtom s a ga)): applySubstitutionAtom (Option.get (matchAtom s a ga) h) a = ga ∧ s ⊆ (Option.get (matchAtom s a ga) h) :=
by
  unfold matchAtom at h
  have symbol_eq: a.symbol = ga.symbol
  by_contra p
  simp [p] at h
  have length_eq: a.atom_terms.length = ga.atom_terms.length
  by_contra p
  simp [symbol_eq, p] at h
  simp [symbol_eq, length_eq] at h
  unfold matchAtom
  simp [symbol_eq, length_eq]
  unfold applySubstitutionAtom
  unfold groundAtom.toAtom
  simp [ruleEquality]
  rw [and_assoc]
  constructor
  apply symbol_eq
  apply matchTermListFindsSolution (len:= length_eq)

lemma matchAtomFindsMinimalSolution (s: substitution τ) (a: atom τ) (ga: groundAtom τ) (h: Option.isSome (matchAtom s a ga)): ∀ (s': substitution τ), applySubstitutionAtom s' a = ga ∧ s ⊆ s' → (Option.get (matchAtom s a ga) h) ⊆ s' :=
by
  unfold matchAtom at h
  have symbol_eq: a.symbol = ga.symbol
  by_contra p
  simp [p] at h
  have length_eq: a.atom_terms.length = ga.atom_terms.length
  by_contra p
  simp [symbol_eq, p] at h
  simp [symbol_eq, length_eq] at h
  unfold matchAtom
  simp [symbol_eq, length_eq]
  intro s'
  unfold applySubstitutionAtom
  unfold groundAtom.toAtom
  simp [symbol_eq]
  intros apply_s' s_s'
  apply matchTermListFindsMinimalSolution (len:= length_eq)
  constructor
  apply apply_s'
  apply s_s'

lemma matchAtomNoneImplNoSolution (s: substitution τ) (a: atom τ) (ga: groundAtom τ) (h: Option.isNone (matchAtom s a ga)): ¬ ∃ (s': substitution τ), s ⊆ s' ∧ applySubstitutionAtom s' a = ga :=
by
  unfold matchAtom at h
  by_cases symbol_eq: a.symbol = ga.symbol
  by_cases length_eq: a.atom_terms.length = ga.atom_terms.length
  unfold applySubstitutionAtom
  unfold groundAtom.toAtom
  simp [symbol_eq, length_eq] at h
  have h': ¬∃ s', s ⊆ s' ∧ List.map (applySubstitutionTerm s') a.atom_terms = List.map term.constant ga.atom_terms
  apply matchTermListNoneImplNoSolution (len:= length_eq) (h:= h)
  push_neg at *
  intros s' s_s'
  simp [symbol_eq]
  apply h' s' s_s'

  push_neg
  intros s' _
  unfold groundAtom.toAtom
  unfold applySubstitutionAtom
  simp [symbol_eq]
  by_contra h'
  rw [← List.length_map a.atom_terms (applySubstitutionTerm s')] at length_eq
  rw [← List.length_map ga.atom_terms term.constant] at length_eq
  rw [h'] at length_eq
  simp at length_eq

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
  have h': ¬ ∃ (s': substitution τ), emptySubstitution ⊆ s' ∧ applySubstitutionAtom s' a = ga
  apply matchAtomNoneImplNoSolution (h:= right)
  push_neg at h'
  rcases left with ⟨s, s_prop⟩
  specialize h' s (emptySubstitutionIsMinimal (τ:= τ) s)
  exact absurd s_prop h'

end atom_matching
