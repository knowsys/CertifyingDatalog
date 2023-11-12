import CertifyingDatalog.Datalog

section matching
variable {τ: signature} [DecidableEq τ.constants][DecidableEq τ.vars]

def extend (s: substitution τ) (v: τ.vars) (c: τ.constants) : substitution τ := fun x => if x = v then Option.some c else s x

def match_term (t: term τ)(c: τ.constants) (s: substitution τ): Option (substitution τ) :=
  match t with
  | term.constant c' =>
    if c = c'
      then s
      else Option.none
  | term.variableDL v =>
    if p:Option.isSome (s v)
    then  if Option.get (s v) p = c
          then
            s
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


end matching
