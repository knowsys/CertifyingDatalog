module

public import CertifyingDatalog.Datalog.Grounding
public import CertifyingDatalog.Datastructures.Finset

@[expose] public section

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
    simp only [Set.mem_ofPred_eq]
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
        simp only [Set.mem_ofPred_eq]
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
    intro v h
    specialize subs_l v h
    rw [subs_l]
    apply subs_r
    unfold domain
    simp only [Set.mem_ofPred_eq]
    rw [← subs_l]
    unfold domain at h
    simp at h
    apply h

end Substitution

namespace Substitution
  variable {τ: Signature}

  def applyTerm (s: Substitution τ) : Term τ -> Term τ
  | Term.constant c => Term.constant c
  | Term.variableDL v => match s v with
    | .some c => Term.constant c
    | .none => Term.variableDL v

  lemma applyTerm_preservesLength {s: Substitution τ} {a: Atom τ}: (List.map s.applyTerm a.atom_terms ).length = τ.relationArity a.symbol :=
  by
    rw [List.length_map]
    apply a.term_length

  @[simp]
  lemma applyTerm_const {s : Substitution τ} {c : τ.constants} :
      s.applyTerm (Term.constant c) = Term.constant c := by
    rfl

  lemma applyTerm_var {s : Substitution τ} {v : τ.vars} :
      s.applyTerm (Term.variableDL v) =
        if h : (s v).isSome
        then Term.constant ((s v).get h)
        else Term.variableDL v := by
    simp [applyTerm]
    cases s v with
    | none => simp
    | some val => simp

  lemma applyTerm_eq_var_iff {t : Term τ} {s : Substitution τ} {v : τ.vars} :
      s.applyTerm t = Term.variableDL v ↔ ¬ v ∈ s.domain ∧ t = Term.variableDL v := by
    simp only [applyTerm, domain, Set.mem_ofPred_eq, Bool.not_eq_true, Option.isSome_eq_false_iff,
      Option.isNone_iff_eq_none]
    cases t with
    | constant _ => simp
    | variableDL v' =>
      simp
      cases h : s v' with
      | none => simp; intro h'; rwa[← h']
      | some val =>
        simp
        intro h₂ h₃
        rw [h₃, h₂] at h
        simp at h

  def applyAtom (s: Substitution τ) (a: Atom τ) : Atom τ :=
    {symbol := a.symbol, atom_terms := List.map s.applyTerm a.atom_terms, term_length := s.applyTerm_preservesLength}

  def applyRule (s: Substitution τ) (r: Rule τ) : Rule τ := {head := s.applyAtom r.head, body := List.map s.applyAtom r.body}

  lemma varInDom_iff {s: Substitution τ}: ∀ v : τ.vars, v ∈ s.domain ↔ ∃ (c: τ.constants), s.applyTerm (Term.variableDL v) = Term.constant c :=
  by
    intro v
    constructor
    · intro h
      unfold domain at h
      rw [Set.mem_ofPred_eq] at h
      rw [Option.isSome_iff_exists] at h
      rcases h with ⟨c, c_prop⟩
      exists c
      simp only [applyTerm, c_prop]
    · intro h
      rcases h with ⟨c, c_prop⟩
      unfold applyTerm at c_prop
      simp only at c_prop
      by_cases p: Option.isSome (s v) = true
      · unfold domain
        rw [Set.mem_ofPred_eq]
        apply p
      · simp only [Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at p
        simp [p] at c_prop

  lemma applyAtom_isGround_impl_varsSubsetDomain [DecidableEq τ.vars] {a: Atom τ} {s: Substitution τ} (subs_ground: ∃ (a': GroundAtom τ), s.applyAtom a = a'): ↑ a.vars ⊆ s.domain :=
  by
    rcases subs_ground with ⟨a', a'_prop⟩
    simp only [applyAtom, GroundAtom.toAtom, Atom.mk.injEq, List.ext_get_iff, List.length_map,
      List.get_eq_getElem, List.getElem_map] at a'_prop
    rcases a'_prop with ⟨_, terms_eq⟩
    simp only [Set.subset_def, SetLike.mem_coe, Atom.mem_vars_iff, List.mem_iff_get,
      List.get_eq_getElem, varInDom_iff, forall_exists_index]
    intro v h hv
    use a'.atom_terms[↑h]
    rw [← hv]
    apply terms_eq.2 h.1 h.2
    grind -- grind solves some universe issue here

  lemma applyRule_isGround_impl_varsSubsetDomain [DecidableEq τ.vars] {r: Rule τ} {s: Substitution τ} (subs_ground: ∃ (r': GroundRule τ), s.applyRule r = r'): ↑ r.vars ⊆ s.domain :=
  by
    simp only [Set.subset_def, SetLike.mem_coe, Rule.mem_vars_iff]
    simp only [applyRule, Rule.ext_iff] at subs_ground
    rcases subs_ground with ⟨r', hhead, hbody⟩
    intro v hv
    cases hv with
    | inl hv =>
      have : ∃ (a : GroundAtom τ), s.applyAtom r.head = a := by
        use r'.head
        rw [hhead]
        simp [GroundRule.toRule]
      have := applyAtom_isGround_impl_varsSubsetDomain this
      simp only [Set.subset_def, SetLike.mem_coe] at this
      apply this v hv
    | inr hv =>
      rcases hv with ⟨a, ha, hv⟩
      rw [List.mem_iff_getElem] at ha
      have : ∃ (a' : GroundAtom τ), s.applyAtom a = a' := by
        rcases ha with ⟨i, hi, h⟩
        have hi' : i < r'.body.length := by
          simp only [GroundRule.toRule] at hbody
          rw [← List.length_map, ← hbody]
          simpa
        use r'.body[i]
        rw [List.ext_get_iff] at hbody
        have := hbody.2 i
        simp only [List.length_map, GroundRule.toRule, List.get_eq_getElem,
          List.getElem_map] at this
        rw [← h]
        apply this hi hi'
      have := applyAtom_isGround_impl_varsSubsetDomain this
      simp only [Set.subset_def, SetLike.mem_coe] at this
      apply this v hv

  def toGrounding [ex: Inhabited τ.constants] (s: Substitution τ): Grounding τ := fun t => match s t with
    | .some c => c
    | .none => ex.default

  lemma toGrounding_applyTerm_eq [Inhabited τ.constants] {t: Term τ} {s: Substitution τ} (h: ↑ t.vars ⊆ s.domain): Term.constant (s.toGrounding.applyTerm' t) = s.applyTerm t := by
    simp [toGrounding, Grounding.applyTerm', applyTerm]
    cases t with
    | constant c =>
      simp
    | variableDL v =>
      simp only
      cases eq : s v with
      | some c => simp
      | none =>
        simp [domain, Set.subset_def, Term.mem_vars_iff, eq] at h

  lemma toGrounding_applyAtom_eq [DecidableEq τ.vars] [Inhabited τ.constants] {a: Atom τ} {s: Substitution τ} (h: ↑ a.vars ⊆ s.domain): (s.toGrounding.applyAtom' a).toAtom = s.applyAtom a := by
    unfold Grounding.applyAtom'
    unfold GroundAtom.toAtom
    unfold applyAtom
    rw [Atom.ext_iff]
    simp only [List.map_map, List.map_inj_left, Function.comp_apply, true_and]
    intro n h'
    apply toGrounding_applyTerm_eq
    apply Atom.vars_subset_impl_term_vars_subset
    exact h'
    exact h

  lemma toGrounding_applyRule_eq [DecidableEq τ.vars] [Inhabited τ.constants] {r: Rule τ} {s: Substitution τ} (h: ↑ r.vars ⊆ s.domain): (s.toGrounding.applyRule' r).toRule = s.applyRule r := by
    unfold GroundRule.toRule
    unfold Grounding.applyRule'
    unfold Substitution.applyRule
    rw [Rule.ext_iff]
    simp only [List.map_map, List.map_inj_left, Function.comp_apply]
    constructor
    · apply toGrounding_applyAtom_eq
      apply Rule.vars_subset_impl_atom_vars_subset (a:=r.head) (r:=r)
      · left
        rfl
      · apply h
    · intro n h'
      apply toGrounding_applyAtom_eq
      apply Rule.vars_subset_impl_atom_vars_subset (r:=r)
      · right
        exact h'
      · exact h

  lemma subset_applyTerm_eq {s1 s2: Substitution τ} {t: Term τ} {c: τ.constants} (subs: s1 ⊆ s2) (eq: s1.applyTerm t = c): s2.applyTerm t = c := by
    cases t with
    | constant c' =>
      unfold applyTerm
      simp only [Term.constant.injEq]
      unfold applyTerm at eq
      simp only [Term.constant.injEq] at eq
      apply eq
    | variableDL v =>
      unfold applyTerm at *
      simp only at *
      cases eq2 : s1 v with
      | none => rw [eq2] at eq; simp at eq
      | some c =>
        rw [eq2] at eq
        simp only [Term.constant.injEq] at eq
        have s2_v: s2 v = some c := by
          apply subset_some s1 s2 subs
          exact eq2
        simp only [s2_v, Term.constant.injEq]
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
        simp only [List.map_cons, List.cons.injEq] at eq
        rcases eq with ⟨left,right⟩
        simp only [List.map_cons, List.cons.injEq]
        constructor
        · apply subset_applyTerm_eq subs left
        · apply ih
          apply right

  lemma subset_applyAtom_eq {s1 s2: Substitution τ} {a: Atom τ} {ga: GroundAtom τ} (subs: s1 ⊆ s2) (eq: s1.applyAtom a = ga): s2.applyAtom a = ga := by
    unfold applyAtom at *
    unfold GroundAtom.toAtom at *
    simp only [Atom.mk.injEq] at *
    rcases eq with ⟨left,right⟩
    constructor
    · apply left
    · apply subset_applyTermList_eq subs right

  lemma applyTerm_remainingVarsNotInDomain {t: Term τ} {s: Substitution τ}: (s.applyTerm t).vars = t.vars.filter_nc (fun x => ¬ x ∈ s.domain) := by
    simp[Finset.ext_iff, Finset.mem_filter_nc, Term.mem_vars_iff, Eq.comm (b := s.applyTerm t), applyTerm_eq_var_iff, Eq.comm]

  lemma applyAtom_remainingVarsNotInDomain [DecidableEq τ.vars] {a: Atom τ} {s: Substitution τ}: (s.applyAtom a).vars = a.vars.filter_nc (fun x => ¬ x ∈ s.domain)  := by
    apply Finset.ext
    simp [Atom.mem_vars_iff, Finset.mem_filter_nc, applyAtom, applyTerm_eq_var_iff]
    tauto
end Substitution

namespace Grounding
  variable {τ: Signature}

  def toSubstitution (g: Grounding τ): Substitution τ := fun t => Option.some (g t)

  lemma toSubstitution_applyTerm_eq {g: Grounding τ} {t: Term τ}: g.applyTerm' t = g.toSubstitution.applyTerm t := by
    unfold applyTerm'
    unfold toSubstitution
    unfold Substitution.applyTerm
    cases t <;> simp

  lemma toSubstitution_applyAtom_eq {a: Atom τ} {g: Grounding τ}: g.applyAtom' a = g.toSubstitution.applyAtom a := by
    rw [Atom.ext_iff]
    unfold applyAtom'
    unfold Substitution.applyAtom
    simp only
    constructor
    · unfold GroundAtom.toAtom
      simp
    · unfold GroundAtom.toAtom
      simp only [List.map_map, List.map_inj_left, Function.comp_apply]
      intros
      rw [toSubstitution_applyTerm_eq]

  lemma toSubstitution_applyRule_eq {r: Rule τ} {g: Grounding τ} : g.applyRule' r = g.toSubstitution.applyRule r := by
    simp only
    unfold applyRule'
    unfold Substitution.applyRule
    unfold GroundRule.toRule
    rw [Rule.ext_iff]
    constructor
    · simp only
      apply toSubstitution_applyAtom_eq
    · simp only [List.map_map, List.map_inj_left, Function.comp_apply]
      intros
      rw [toSubstitution_applyAtom_eq]
end Grounding

theorem grounding_substitution_equiv {τ: Signature} [DecidableEq τ.vars] [Inhabited τ.constants] {r: GroundRule τ} {r': Rule τ}: (∃ (g: Grounding τ), g.applyRule' r' = r) ↔ (∃ (s: Substitution τ), s.applyRule r'= r) :=
  by
    simp only
    constructor
    · intro h
      rcases h with ⟨g, g_prop⟩
      use g.toSubstitution
      rw [← g_prop]
      simp [Grounding.toSubstitution_applyRule_eq]
    · intro h
      rcases h with ⟨s, s_prop⟩
      use s.toGrounding
      rw [GroundRule.eq_iff_toRule_eq]
      rw [← s_prop]
      apply Substitution.toGrounding_applyRule_eq
      apply Substitution.applyRule_isGround_impl_varsSubsetDomain
      use r
