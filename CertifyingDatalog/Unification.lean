import CertifyingDatalog.Datalog

section matching
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

def match_term (t: term τ)(c: τ.constants) (s: substitution τ): Option (substitution τ) :=
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

lemma matchTermIsSomeIffSolution (t: term τ) (c: τ.constants): Option.isSome (match_term t c (fun _ => Option.none)) ↔ ∃ (s: substitution τ), applySubstitutionTerm s t = c :=
by
  simp
  constructor
  intro h
  use Option.get (match_term t c (fun _ => Option.none)) h
  cases t with
    | constant c' =>
      unfold match_term
      simp
      by_cases p: c= c'
      simp [p]
      unfold applySubstitutionTerm
      simp
      exfalso
      unfold match_term at h
      simp [p] at h
    | variableDL v =>
      unfold match_term
      simp
      unfold extend
      unfold applySubstitutionTerm
      simp
  by_contra h
  simp at h
  rcases h with ⟨s, none⟩
  rcases s with ⟨s, s_prop⟩
  cases t with
  | constant c' =>
    unfold match_term at none
    simp at none
    by_cases p: c' = c
    simp [p] at none
    unfold applySubstitutionTerm at s_prop
    simp at s_prop
    exact absurd s_prop p
  | variableDL v =>
    unfold match_term at none
    simp at none

lemma matchTermFindsMinimalSolution (t: term τ) (c: τ.constants) (s: substitution τ) (h: Option.isSome (match_term t c s)): applySubstitutionTerm (Option.get (match_term t c s) h) t = c ∧ s ⊆ (Option.get (match_term t c s) h) ∧ ∀ (s': substitution τ), (s ⊆ s' ∧ applySubstitutionTerm s' t = c) → (Option.get (match_term t c s) h) ⊆ s' :=
by
  cases t with
  | constant c' =>
    simp
    unfold match_term at h
    simp at h
    have c_c': c = c'
    by_contra h'
    simp [h'] at h
    constructor
    unfold match_term
    unfold applySubstitutionTerm
    simp [c_c']
    constructor
    unfold match_term
    simp [c_c']
    apply substitution_subs_refl
    intros s' s_s' _
    unfold match_term
    simp [c_c', s_s']
  | variableDL v =>
    unfold match_term at h
    by_cases p: Option.isSome (s v)
    have sv_c: Option.get (s v) p = c
    by_contra h'
    simp [p, h'] at h
    have h': (Option.get (match_term (term.variableDL v) c s) h) = s
    unfold match_term
    simp [p, sv_c]
    simp
    constructor
    rw [h']
    unfold applySubstitutionTerm
    simp [p, sv_c]
    constructor
    rw [h']
    apply substitution_subs_refl
    intro s' s_s' _
    rw [h']
    apply s_s'
    have h': Option.get (match_term (term.variableDL v) c s) h = extend s v c
    unfold match_term
    simp [p]
    rw [h']
    constructor
    unfold applySubstitutionTerm
    unfold extend
    simp
    constructor
    apply s_subset_extend_s
    simp at p
    apply p
    by_contra not_min
    push_neg at not_min
    rcases not_min with ⟨s', right⟩
    rcases right with ⟨left, not_extend⟩
    rcases left with ⟨s_s', apply_s'⟩
    unfold_projs at not_extend
    unfold substitution_subs at not_extend
    push_neg at not_extend
    unfold extend at not_extend
    rcases not_extend with ⟨v', not_subs⟩
    by_cases v'_v: v' = v
    simp [v'_v] at not_subs
    have s'v_c: s' v = some c
    unfold applySubstitutionTerm at apply_s'
    simp at apply_s'
    by_cases p': Option.isSome (s' v)
    simp [p'] at apply_s'
    rw [Option.eq_some_iff_get_eq]
    simp [apply_s']
    apply p'
    simp [p'] at apply_s'
    simp [s'v_c] at not_subs

    simp [v'_v] at not_subs
    cases sv': s v' with
    | some c' =>
      simp [sv'] at not_subs
      have s'_v': s' v' = some c'
      apply substitution_subs_get s s' s_s' _ _ sv'
      simp[s'_v'] at not_subs
    | none =>
      simp [sv'] at not_subs
end matching
