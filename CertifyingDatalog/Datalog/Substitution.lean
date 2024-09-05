import CertifyingDatalog.Basic
import CertifyingDatalog.Datalog.Basic
import CertifyingDatalog.Datalog.Grounding

def Substitution (τ: Signature) := τ.vars → Option (τ.constants)

namespace Substitution
  def domain (s: Substitution τ): Set (τ.vars) := {v | Option.isSome (s v) = true}

  def empty : Substitution τ := (fun _ => none)

  def subset (s1 s2: Substitution τ): Prop :=
    ∀ (v: τ.vars), v ∈ s1.domain → s1 v = s2 v

  instance: HasSubset (Substitution τ) where
    Subset := Substitution.subset

  lemma empty_isMinimal : ∀ s : Substitution τ, Substitution.empty ⊆ s := by
    unfold_projs
    unfold subset
    intro v
    unfold empty
    unfold domain
    simp

  lemma subset_some (s1 s2: Substitution τ) (subs: s1 ⊆ s2) (c: τ.constants) (v: τ.vars) (h: s1 v = Option.some c): s2 v = Option.some c := by
    unfold_projs at subs
    unfold subset at subs
    rw [← h]
    apply Eq.symm
    apply subs
    unfold domain
    simp
    rw [h]
    simp

  lemma subset_none (s1 s2: Substitution τ) (subs: s1 ⊆ s2) (v: τ.vars) (h: s2 v = Option.none): s1 v = Option.none := by
    unfold_projs at subs
    unfold Substitution.subset at subs
    specialize subs v
    by_contra p
    cases q:(s1 v) with
    | none =>
      exact absurd q p
    | some c =>
      have s1_s2: s1 v = s2 v := by
        apply subs
        unfold domain
        simp
        rw [q]
        simp
      rw [s1_s2] at p
      exact absurd h p

  lemma subset_refl (s: Substitution τ): s ⊆ s := by
    unfold_projs
    unfold subset
    simp

  lemma subset_antisymm (s1 s2: Substitution τ) (subs_l: s1 ⊆ s2) (subs_r: s2 ⊆ s1): s1 = s2 := by
    funext x
    cases p: s1 x with
    | some c =>
      apply Eq.symm
      apply subset_some s1 s2 subs_l c x p
    | none =>
      apply Eq.symm
      apply subset_none s2 s1 subs_r x p

  lemma subset_trans (s1 s2 s3: Substitution τ) (subs_l: s1 ⊆ s2) (subs_r: s2 ⊆ s3): s1 ⊆ s3 := by
    unfold_projs at *
    unfold subset at *
    intro v
    intro h
    specialize subs_l v h
    rw [subs_l]
    apply subs_r
    unfold domain
    simp
    rw [← subs_l]
    unfold domain at h
    simp at h
    apply h

end Substitution


namespace Substitution
  variable {τ: Signature} [DecidableEq τ.vars] [DecidableEq τ.relationSymbols] [DecidableEq τ.constants] [Hashable τ.constants] [Hashable τ.vars] [Hashable τ.relationSymbols]

  def applyTerm (s: Substitution τ) : Term τ -> Term τ
  | Term.constant c => Term.constant c
  | Term.variableDL v => match s v with
    | .some c => Term.constant c
    | .none => Term.variableDL v

  lemma applyTerm_preservesLength (s: Substitution τ) (a: Atom τ): (List.map s.applyTerm a.atom_terms ).length = τ.relationArity a.symbol :=
  by
    rw [List.length_map]
    apply a.term_length

  def applyAtom (s: Substitution τ) (a: Atom τ) : Atom τ :=
    {symbol := a.symbol, atom_terms := List.map s.applyTerm a.atom_terms, term_length := s.applyTerm_preservesLength a}

  def applyRule (s: Substitution τ) (r: Rule τ) : Rule τ := {head := s.applyAtom r.head, body := List.map s.applyAtom r.body}

  lemma varInDom_iff {s: Substitution τ}: ∀ v : τ.vars, v ∈ s.domain ↔ ∃ (c: τ.constants), s.applyTerm (Term.variableDL v) = Term.constant c :=
  by
    intro v
    constructor
    intro h
    unfold domain at h
    rw [Set.mem_setOf] at h
    rw [Option.isSome_iff_exists] at h
    rcases h with ⟨c, c_prop⟩
    exists c
    simp [applyTerm, c_prop]

    intro h
    rcases h with ⟨c, c_prop⟩
    unfold applyTerm at c_prop
    simp at c_prop
    by_cases p: Option.isSome (s v) = true
    · unfold domain
      rw [Set.mem_setOf]
      apply p
    · simp at p
      simp [p] at c_prop

  lemma applyAtom_isGround_impl_varsSubsetDomain {a: Atom τ} {s: Substitution τ} (subs_ground: ∃ (a': GroundAtom τ), s.applyAtom a = a'): ↑ a.vars ⊆ s.domain :=
  by
    unfold Atom.vars
    rcases subs_ground with ⟨a', a'_prop⟩
    unfold applyAtom at a'_prop
    unfold GroundAtom.toAtom at a'_prop
    rw [Atom.ext_iff] at a'_prop
    simp at a'_prop
    rcases a'_prop with ⟨_, terms_eq⟩
    rw [List.foldl_union_subset_set]
    simp

    intros t t_mem
    cases t with
    | constant c =>
      unfold Term.vars
      simp
    | variableDL v =>
      unfold Term.vars
      simp
      rw [varInDom_iff]
      rw [List.mem_iff_get] at t_mem
      rcases t_mem with ⟨v_pos, v_pos_proof⟩
      rw [← v_pos_proof]
      rcases v_pos with ⟨v_pos, v_pos_a⟩
      have v_pos_a': v_pos < List.length a'.atom_terms := by
        rw [← List.length_map (f:= Term.constant), ← terms_eq, List.length_map]
        apply v_pos_a
      use List.get a'.atom_terms {val:= v_pos, isLt:= v_pos_a'}
      have get_of_terms_eq := List.get_of_eq terms_eq ⟨v_pos, by rw [List.length_map]; exact v_pos_a⟩
      simp at get_of_terms_eq
      simp
      rw [get_of_terms_eq]

  lemma applyRule_isGround_impl_varsSubsetDomain {r: Rule τ} {s: Substitution τ} (subs_ground: ∃ (r': GroundRule τ), s.applyRule r = r'): ↑ r.vars ⊆ s.domain :=
  by
    unfold Rule.vars
    simp at subs_ground
    rcases subs_ground with ⟨r', r'_prop⟩
    unfold applyRule at r'_prop
    rw [Rule.ext_iff] at r'_prop
    simp at r'_prop
    rcases r'_prop with ⟨left,right⟩
    simp
    constructor
    apply applyAtom_isGround_impl_varsSubsetDomain
    use r'.head
    rw [left]
    unfold GroundRule.toRule
    simp

    rw [List.foldl_union_subset_set]
    simp
    intros a a_mem
    apply applyAtom_isGround_impl_varsSubsetDomain
    unfold GroundRule.toRule at right
    simp at right
    rw [List.mem_iff_get] at a_mem
    rcases a_mem with ⟨a_pos, pos_prop⟩
    rcases a_pos with ⟨a_pos, a_pos_proof⟩
    have a_pos_proof': a_pos < List.length r'.body := by
      rw [← List.length_map r'.body GroundAtom.toAtom, ← right, List.length_map r.body]
      apply a_pos_proof
    use List.get r'.body (Fin.mk a_pos a_pos_proof')
    rw [← pos_prop]
    have h: a_pos < (List.map s.applyAtom r.body ).length := by
      rw [List.length_map]
      apply a_pos_proof
    have get_of_right := List.get_of_eq right ⟨a_pos, h⟩
    simp at get_of_right
    simp
    rw [get_of_right]

  def toGrounding [ex: Inhabited τ.constants] (s: Substitution τ): Grounding τ := fun t => match s t with
    | .some c => c
    | .none => ex.default

  lemma toGrounding_applyTerm_eq [Inhabited τ.constants] (t: Term τ) (s: Substitution τ) (h: ↑ t.vars ⊆ s.domain): Term.constant (s.toGrounding.applyTerm' t) = s.applyTerm t := by
    unfold toGrounding
    unfold Grounding.applyTerm'
    unfold applyTerm
    simp
    cases t with
    | constant c =>
      simp
    | variableDL v =>
      simp
      cases eq : s v with
      | some c => simp
      | none =>
        unfold Term.vars at h
        unfold domain at h
        unfold Option.isSome at h
        simp [eq] at h

  lemma toGrounding_applyAtom_eq [Inhabited τ.constants] (a: Atom τ) (s: Substitution τ) (h: ↑ a.vars ⊆ s.domain): (s.toGrounding.applyAtom' a).toAtom = s.applyAtom a := by
    unfold Grounding.applyAtom'
    unfold GroundAtom.toAtom
    unfold applyAtom
    rw [Atom.ext_iff]
    simp
    intro n h'
    apply toGrounding_applyTerm_eq
    apply Atom.vars_subset_impl_term_vars_subset
    exact h'
    exact h

  lemma toGrounding_applyRule_eq [Inhabited τ.constants] (r: Rule τ) (s: Substitution τ) (h: ↑ r.vars ⊆ s.domain): (s.toGrounding.applyRule' r).toRule = s.applyRule r := by
    unfold GroundRule.toRule
    unfold Grounding.applyRule'
    unfold Substitution.applyRule
    rw [Rule.ext_iff]
    simp
    constructor
    apply toGrounding_applyAtom_eq
    apply Rule.vars_subset_impl_atom_vars_subset (a:=r.head) (r:=r)
    left
    rfl
    apply h
    intro n h'
    apply toGrounding_applyAtom_eq
    apply Rule.vars_subset_impl_atom_vars_subset (r:=r)
    right
    exact h'
    exact h

  lemma subset_applyTerm_eq {s1 s2: Substitution τ} {t: Term τ} {c: τ.constants} (subs: s1 ⊆ s2) (eq: s1.applyTerm t = c): s2.applyTerm t = c := by
    cases t with
    | constant c' =>
      unfold applyTerm
      simp
      unfold applyTerm at eq
      simp at eq
      apply eq
    | variableDL v =>
      unfold applyTerm at *
      simp at *
      cases eq2 : s1 v with
      | none => rw [eq2] at eq; simp at eq
      | some c =>
        rw [eq2] at eq
        simp at eq
        have s2_v: s2 v = some c := by
          apply subset_some s1 s2 subs
          exact eq2
        simp [s2_v]
        exact eq

  lemma subset_applyTermList_eq {s1 s2: Substitution τ} {l1: List (Term τ)} {l2: List (τ.constants)} (subs: s1 ⊆ s2) (eq: List.map s1.applyTerm l1 = List.map Term.constant l2): List.map s2.applyTerm l1 = List.map Term.constant l2 := by
    induction l1 generalizing l2 with
    | nil =>
      cases l2 with
      | nil =>
        simp
      | cons hd tl =>
        simp at eq
    | cons hd tl ih =>
      cases l2 with
      | nil =>
        simp at eq
      | cons hd' tl' =>
        simp at eq
        rcases eq with ⟨left,right⟩
        simp
        constructor
        apply subset_applyTerm_eq subs left
        apply ih
        apply right

  lemma subset_applyAtom_eq {s1 s2: Substitution τ} {a: Atom τ} {ga: GroundAtom τ} (subs: s1 ⊆ s2) (eq: s1.applyAtom a = ga): s2.applyAtom a = ga := by
    unfold applyAtom at *
    unfold GroundAtom.toAtom at *
    simp at *
    rcases eq with ⟨left,right⟩
    constructor
    apply left
    apply subset_applyTermList_eq subs right

  lemma applyTerm_remainingVarsNotInDomain (t: Term τ) (s: Substitution τ): (s.applyTerm t).vars = t.vars.filter_nc (fun x => ¬ x ∈ s.domain) := by
    cases t with
    | constant c =>
      unfold applyTerm
      unfold Term.vars
      rw [Finset.ext_iff]
      simp
      simp [Finset.mem_filter_nc]
    | variableDL v =>
      unfold applyTerm
      unfold Term.vars
      rw [Finset.ext_iff]
      simp

      cases eq : s v with
      | some c =>
        simp
        intro v'
        simp [Finset.mem_filter_nc]
        unfold domain
        simp
        intro h' p
        rw [p] at h'
        rw [eq] at h'
        contradiction
      | none =>
        simp
        intro v'
        simp [Finset.mem_filter_nc]
        intro h'
        unfold domain
        simp
        rw [h', eq]

  lemma applyAtom_remainingVarsNotInDomain (a: Atom τ) (s: Substitution τ): (s.applyAtom a).vars = a.vars.filter_nc (fun x => ¬ x ∈ s.domain)  := by
    apply Finset.ext
    intro v
    unfold Atom.vars
    rw [List.mem_foldl_union, Finset.mem_filter_nc, List.mem_foldl_union]
    simp
    unfold applyAtom
    simp
    simp_rw [applyTerm_remainingVarsNotInDomain, Finset.mem_filter_nc]
    tauto
end Substitution

namespace Grounding
  variable {τ: Signature} [DecidableEq τ.vars] [DecidableEq τ.relationSymbols] [DecidableEq τ.constants] [Hashable τ.constants] [Hashable τ.vars] [Hashable τ.relationSymbols]

  def toSubstitution (g: Grounding τ): Substitution τ := fun t => Option.some (g t)

  lemma toSubsitution_applyTerm_eq (g: Grounding τ) (t: Term τ): g.applyTerm' t = g.toSubstitution.applyTerm t := by
    unfold applyTerm'
    unfold toSubstitution
    unfold Substitution.applyTerm
    cases t <;> simp

  lemma toSubsitution_applyAtom_eq (a: Atom τ) (g: Grounding τ): g.applyAtom' a = g.toSubstitution.applyAtom a := by
    rw [Atom.ext_iff]
    unfold applyAtom'
    unfold Substitution.applyAtom
    simp
    constructor
    unfold GroundAtom.toAtom
    simp

    unfold GroundAtom.toAtom
    simp
    intros
    rw [toSubsitution_applyTerm_eq]

  lemma toSubsitution_applyRule_eq (r: Rule τ) (g: Grounding τ): g.applyRule' r = g.toSubstitution.applyRule r := by
    simp
    unfold applyRule'
    unfold Substitution.applyRule
    unfold GroundRule.toRule
    rw [Rule.ext_iff]
    constructor
    simp
    apply toSubsitution_applyAtom_eq

    simp
    intros
    rw [toSubsitution_applyAtom_eq]
end Grounding

theorem grounding_substitution_equiv {τ: Signature} [DecidableEq τ.vars] [DecidableEq τ.relationSymbols] [DecidableEq τ.constants] [Hashable τ.constants] [Hashable τ.vars] [Hashable τ.relationSymbols] [Inhabited τ.constants] (r: GroundRule τ) (r': Rule τ): (∃ (g: Grounding τ), g.applyRule' r' = r) ↔ (∃ (s: Substitution τ), s.applyRule r'= r) :=
  by
    simp
    constructor
    intro h
    rcases h with ⟨g, g_prop⟩
    use g.toSubstitution
    rw [← g_prop]
    simp [Grounding.toSubsitution_applyRule_eq]

    intro h
    rcases h with ⟨s, s_prop⟩
    use s.toGrounding
    rw [GroundRule.eq_iff_toRule_eq]
    rw [← s_prop]
    apply Substitution.toGrounding_applyRule_eq
    apply Substitution.applyRule_isGround_impl_varsSubsetDomain
    use r

