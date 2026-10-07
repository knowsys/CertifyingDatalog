module

public import CertifyingDatalog.Datalog.Grounding
public import CertifyingDatalog.Datastructures.Finset
import Mathlib.Data.Finset.Attr

public section

-- The compiler requires us to expose this function.
@[expose]
def Substitution (τ: Signature) := τ.vars → Option (τ.constants)

namespace Substitution
  def domain (s: Substitution τ): Set (τ.vars) := {v | Option.isSome (s v) = true}

  @[simp]
  lemma mem_domain_iff {s : Substitution τ} {v : τ.vars} :
      v ∈ s.domain ↔ (s v).isSome := by simp [domain]

  def empty : Substitution τ := (fun _ => none)

  def subset (s1 s2: Substitution τ): Prop :=
    ∀ (v: τ.vars), v ∈ s1.domain → s1 v = s2 v

  instance: HasSubset (Substitution τ) where
    Subset := Substitution.subset

  lemma subset_iff {s1 s2 : Substitution τ} :
    s1 ⊆ s2 ↔ ∀ v, (s1 v).isSome → s1 v = s2 v := by
      unfold_projs; simp [subset]

  lemma empty_isMinimal : ∀ s : Substitution τ, Substitution.empty ⊆ s := by
    simp [empty, subset_iff]

  lemma subset_some (s1 s2: Substitution τ) (subs: s1 ⊆ s2) (c: τ.constants) (v: τ.vars) (h: s1 v = Option.some c): s2 v = Option.some c := by
    simp only [subset_iff] at subs
    specialize subs v
    simp only [h, Option.isSome_some, forall_const] at subs
    rw [subs]

  lemma subset_none (s1 s2: Substitution τ) (subs: s1 ⊆ s2) (v: τ.vars) (h: s2 v = Option.none): s1 v = Option.none := by
    simp only [subset_iff] at subs
    specialize subs v
    by_contra p
    cases q: (s1 v) with
    | none =>
      exact absurd q p
    | some c =>
      simp [q, h] at subs

  lemma subset_refl (s: Substitution τ): s ⊆ s := by
    simp [subset_iff]

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
    simp only [subset_iff] at *
    intro v h
    specialize subs_l v h
    rw [subs_l]
    apply subs_r
    rw [← subs_l]
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

  @[simp]
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

  lemma applyTerm_eq_const_iff {t : Term τ} {s : Substitution τ} {c : τ.constants} :
      s.applyTerm t = Term.constant c ↔ (t = Term.constant c) ∨ ∃ v, t = Term.variableDL v ∧ s v = some c := by
    cases t with
    | variableDL v =>
      simp
      split
      · rename_i h
        have := Option.isSome_iff_exists.mp h
        grind
      · grind
    | constant c' => simp

  def applyAtom (s: Substitution τ) (a: Atom τ) : Atom τ :=
    {symbol := a.symbol, atom_terms := List.map s.applyTerm a.atom_terms, term_length := s.applyTerm_preservesLength}

  @[simp]
  lemma applyAtom_symbol {a : Atom τ} {s : Substitution τ} :
    (s.applyAtom a).symbol = a.symbol := by rfl

  @[simp]
  lemma applyAtom_terms {a : Atom τ} {s : Substitution τ} :
    (s.applyAtom a).atom_terms = a.atom_terms.map s.applyTerm := by rfl

  def applyRule (s: Substitution τ) (r: Rule τ) : Rule τ := {head := s.applyAtom r.head, body := List.map s.applyAtom r.body}

  @[simp]
  lemma applyRule_head {r : Rule τ} {s : Substitution τ} : (s.applyRule r).head = s.applyAtom r.head := by rfl

  @[simp]
  lemma applyRule_body {r : Rule τ} {s : Substitution τ} :
    (s.applyRule r).body = r.body.map s.applyAtom := by rfl

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
    simp only [applyAtom, Atom.eq_GroundAtom_iff, List.length_map, List.getElem_map] at subs_ground
    simp only [Set.subset_def, SetLike.mem_coe, Atom.mem_vars_iff, List.mem_iff_get,
      List.get_eq_getElem, varInDom_iff, forall_exists_index]
    grind

  lemma applyRule_isGround_impl_varsSubsetDomain [DecidableEq τ.vars] {r: Rule τ} {s: Substitution τ} (subs_ground: ∃ (r': GroundRule τ), s.applyRule r = r'): ↑ r.vars ⊆ s.domain :=
  by
    simp only [applyRule, Rule.eq_GroundRule_iff, List.length_map, List.getElem_map] at subs_ground
    simp only [Set.subset_def, SetLike.mem_coe, Rule.mem_vars_iff]
    rcases subs_ground with ⟨r', hhead, hbody⟩
    intro v hv
    cases hv with
    | inl hv =>
      apply applyAtom_isGround_impl_varsSubsetDomain
      use r'.head
      exact hv
    | inr hv =>
      rcases hv with ⟨a, ha, hv⟩
      apply applyAtom_isGround_impl_varsSubsetDomain (a:= a)
      · simp only [List.mem_iff_get, List.get_eq_getElem] at ha
        rcases ha with ⟨n, hn⟩
        rcases hbody with ⟨hl, hbody⟩
        use r'.body[n]
        simp [← hn, ← hbody]
      · exact hv

  def toGrounding [ex: Inhabited τ.constants] (s: Substitution τ): Grounding τ := fun t => match s t with
    | .some c => c
    | .none => ex.default

  lemma toGrounding_applyTerm_eq [Inhabited τ.constants] {t: Term τ} {s: Substitution τ} (h: ↑ t.vars ⊆ s.domain): Term.constant (s.toGrounding.applyTerm' t) = s.applyTerm t := by
    cases t with
    | constant c => simp
    | variableDL v =>
      simp only [Grounding.applyTerm'_var, toGrounding, applyTerm]
      cases eq : s v with
      | some c => simp
      | none =>
        simp [domain, Set.subset_def, Term.mem_vars_iff, eq] at h

  lemma toGrounding_applyAtom_eq [DecidableEq τ.vars] [Inhabited τ.constants] {a: Atom τ} {s: Substitution τ} (h: ↑ a.vars ⊆ s.domain): (s.toGrounding.applyAtom' a).toAtom = s.applyAtom a := by
    simp only [GroundAtom.eq_atom_iff, Grounding.applyAtom'_symbol, applyAtom_symbol,
      applyAtom_terms, List.length_map, List.getElem_map, Grounding.applyAtom'_terms,
      exists_true_left]
    intro i hi
    rw [toGrounding_applyTerm_eq]
    apply Atom.vars_subset_impl_term_vars_subset (by simp) h

  lemma toGrounding_applyRule_eq [DecidableEq τ.vars] [Inhabited τ.constants] {r: Rule τ} {s: Substitution τ} (h: ↑ r.vars ⊆ s.domain): (s.toGrounding.applyRule' r).toRule = s.applyRule r := by
    simp only [GroundRule.eq_rule_iff, Grounding.applyRule'_head, applyRule_head, applyRule_body,
      List.length_map, Grounding.applyRule'_body, List.getElem_map, exists_true_left]
    constructor
    · apply toGrounding_applyAtom_eq
      apply Rule.vars_subset_impl_atom_vars_subset (by simp) h
    · intro i hi
      apply toGrounding_applyAtom_eq
      apply Rule.vars_subset_impl_atom_vars_subset (by simp) h

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

  lemma subset_applyAtom_eq {s1 s2: Substitution τ} {a: Atom τ} {ga: GroundAtom τ} (subs: s1 ⊆ s2) (eq: s1.applyAtom a = ga): s2.applyAtom a = ga := by
    simp only [Atom.eq_GroundAtom_iff, applyAtom_symbol, applyAtom_terms, List.length_map,
      List.getElem_map] at ⊢ eq
    rcases eq with ⟨h, h₂⟩
    use h
    intro i hi
    apply subset_applyTerm_eq subs (h₂ i hi)

  lemma applyTerm_remainingVarsNotInDomain {t: Term τ} {s: Substitution τ}: (s.applyTerm t).vars = t.vars.filter_nc (fun x => ¬ x ∈ s.domain) := by
    simp only [mem_domain_iff, Bool.not_eq_true, Option.isSome_eq_false_iff,
      Option.isNone_iff_eq_none, Finset.ext_iff, Term.mem_vars_iff, Eq.comm (b := s.applyTerm t),
      applyTerm_eq_var_iff, Finset.mem_filter_nc, and_congr_right_iff]
    exact fun a a_1 => eq_comm

  lemma applyAtom_remainingVarsNotInDomain [DecidableEq τ.vars] {a: Atom τ} {s: Substitution τ}: (s.applyAtom a).vars = a.vars.filter_nc (fun x => ¬ x ∈ s.domain)  := by
    apply Finset.ext
    simp [Atom.mem_vars_iff, Finset.mem_filter_nc, applyAtom, applyTerm_eq_var_iff]
    tauto
end Substitution

namespace Grounding
  variable {τ: Signature}

  def toSubstitution (g: Grounding τ): Substitution τ := fun t => Option.some (g t)

  lemma toSubstitution_applyTerm_eq {g: Grounding τ} {t: Term τ}: g.applyTerm' t = g.toSubstitution.applyTerm t := by
    cases t with
    | constant _ => simp
    | variableDL _ => simp [toSubstitution, Substitution.applyTerm_var]

  lemma toSubstitution_applyAtom_eq {a: Atom τ} {g: Grounding τ}: g.applyAtom' a = g.toSubstitution.applyAtom a := by
    simp [GroundAtom.eq_atom_iff, toSubstitution_applyTerm_eq]

  lemma toSubstitution_applyRule_eq {r: Rule τ} {g: Grounding τ} : g.applyRule' r = g.toSubstitution.applyRule r := by
    simp [GroundRule.eq_rule_iff, toSubstitution_applyAtom_eq]
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
