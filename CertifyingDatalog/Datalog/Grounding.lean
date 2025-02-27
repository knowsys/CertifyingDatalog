import CertifyingDatalog.Basic
import CertifyingDatalog.Datalog.Basic

@[ext]
structure GroundAtom (τ: Signature)
where
  symbol: τ.relationSymbols
  atom_terms: List (τ.constants)
  term_length: atom_terms.length = τ.relationArity symbol

instance {τ: Signature} [DecidableEq τ.vars] [DecidableEq τ.relationSymbols] [DecidableEq τ.constants] : DecidableEq (GroundAtom τ) :=
  fun l r =>
    if h: l.symbol = r.symbol
    then
      if h': l.atom_terms = r.atom_terms
      then isTrue (by ext; exact h; simp [h'])
      else isFalse (by by_contra p; rw[p] at h'; contradiction)
    else isFalse (by by_contra p; rw[p] at h; contradiction)

instance {τ: Signature} [Hashable τ.vars] [Hashable τ.relationSymbols] [Hashable τ.constants] : Hashable (GroundAtom τ) where
  hash :=
    fun a => mixHash (hash a.symbol) (hash a.atom_terms)

@[ext]
structure GroundRule (τ: Signature) where
  head: GroundAtom τ
  body: List (GroundAtom τ)

instance {τ: Signature} [DecidableEq τ.vars] [DecidableEq τ.relationSymbols] [DecidableEq τ.constants] : DecidableEq (GroundRule τ) :=
  fun l r =>
    if h:l.head = r.head
    then
      if h':l.body = r.body
      then isTrue (by ext; rw[h]; rw[h]; rw[h'])
      else isFalse (by by_contra p; rw [p] at h'; contradiction)
    else isFalse (by by_contra p; rw[p] at h; contradiction)

abbrev Grounding (τ: Signature) := τ.vars → τ.constants

variable {τ: Signature}

namespace GroundAtom
  def toAtom (ga: GroundAtom τ): Atom τ:= {symbol:=ga.symbol, atom_terms:= List.map Term.constant ga.atom_terms,term_length := by rw [List.length_map]; exact ga.term_length}

  lemma eq_iff_toAtom_eq {a1 a2: GroundAtom τ}: a1 = a2 ↔ a1.toAtom = a2.toAtom :=
  by
    constructor
    · intro h
      rw [h]
    · unfold GroundAtom.toAtom
      simp only [Atom.mk.injEq, and_imp]
      intros sym terms
      rw [GroundAtom.ext_iff]
      constructor
      · apply sym
      · have : Function.Injective (List.map (Term.constant (τ := τ))) := by
          rw [List.map_injective_iff]
          intro _ _ term_eq
          injection term_eq
        apply this
        exact terms

  instance: Coe (GroundAtom τ) (Atom τ) where
    coe := GroundAtom.toAtom

  lemma vars_empty {ga : GroundAtom τ} [DecidableEq τ.vars] : ga.toAtom.vars = ∅ := by
    unfold toAtom
    unfold Atom.vars
    simp only
    rw [List.foldl_union_empty]
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, true_and]
    intro _ _
    unfold Term.vars
    simp
end GroundAtom

namespace Atom
  def toGroundAtom (a: Atom τ) [DecidableEq τ.vars] (h: a.vars = ∅) : GroundAtom τ :=
  {
    symbol:= a.symbol,
    atom_terms := List.map (fun ⟨t, t_in_a⟩ => t.toConstant (a.vars_empty_iff.mp h t t_in_a)) a.atom_terms.attach,
    term_length := by simp; apply a.term_length
  }

  lemma toGroundAtom_isSelf [DecidableEq τ.vars] {a: Atom τ} (h: a.vars = ∅): a = a.toGroundAtom h :=
  by
    unfold GroundAtom.toAtom
    unfold toGroundAtom
    simp only [List.map_map]
    rw [Atom.ext_iff]
    simp only [true_and]
    rw [vars_empty_iff] at h
    apply List.ext_get
    · simp
    · intro n h1 h2
      simp only [List.get_eq_getElem, List.getElem_map, List.getElem_attach, Function.comp_apply]
      have h': ∀ (t : Term τ) (noVars : t.vars = ∅), t = t.toConstant noVars := by
        intro t noVars
        unfold Term.toConstant
        cases t with
        | constant c => simp
        | variableDL v =>
          unfold Term.vars at noVars
          simp at noVars
      apply h'
end Atom

namespace GroundAtom
  lemma toAtom_toGroundAtom [DecidableEq τ.vars] (ga : GroundAtom τ) : ga.toAtom.toGroundAtom GroundAtom.vars_empty = ga := by
    simp only [Atom.toGroundAtom]
    rw [GroundAtom.eq_iff_toAtom_eq]
    simp only [GroundAtom.toAtom, List.map_map, Atom.mk.injEq, true_and]
    apply List.ext_get
    · simp
    · intro n h1 h2
      simp [Term.toConstant]
end GroundAtom

namespace GroundRule
  def toRule (r: GroundRule τ): Rule τ := {head:= r.head.toAtom, body := List.map GroundAtom.toAtom r.body}

  instance [ToString τ.constants] [ToString τ.vars] [ToString τ.relationSymbols] : ToString (GroundRule τ) where
    toString gr := ToString.toString gr.toRule

  instance: Coe (GroundRule τ) (Rule τ) where
    coe
      | r => r.toRule

  lemma eq_iff_toRule_eq {r1 r2: GroundRule τ} : r1 = r2 ↔ r1.toRule = r2.toRule :=
  by
    constructor
    · intro h
      rw [h]
    · unfold GroundRule.toRule
      rw [GroundRule.ext_iff]
      intro h
      simp only [Rule.mk.injEq] at h
      rcases h with ⟨head_eq, body_eq⟩
      have inj_toAtom: Function.Injective (GroundAtom.toAtom (τ:= τ)) := by
        unfold Function.Injective
        intros a1 a2 h
        rw [GroundAtom.eq_iff_toAtom_eq]
        apply h
      constructor
      · unfold Function.Injective at inj_toAtom
        apply inj_toAtom head_eq
      · rw [← List.map_injective_iff] at inj_toAtom
        apply inj_toAtom
        exact body_eq

  def bodySet [DecidableEq τ.constants] [DecidableEq τ.vars] [DecidableEq τ.relationSymbols] (r: GroundRule τ): Finset (GroundAtom τ) := List.toFinset r.body

  lemma in_bodySet_iff_in_body [DecidableEq τ.constants] [DecidableEq τ.vars] [DecidableEq τ.relationSymbols] {r: GroundRule τ} : ∀ a, a ∈ r.body ↔ a ∈ r.bodySet := by simp [bodySet]
end GroundRule

namespace Grounding
  def applyTerm (g: Grounding τ) : Term τ -> Term τ
  | Term.constant c => Term.constant c
  | Term.variableDL v => Term.constant (g v)

  lemma applyTerm_removesVars {g: Grounding τ} {t: Term τ} : (g.applyTerm t).vars = ∅ := by
    cases t <;> (unfold applyTerm; unfold Term.vars; simp)

  lemma applyTerm_preservesLength {g: Grounding τ} {a: Atom τ}: (List.map g.applyTerm a.atom_terms).length = τ.relationArity a.symbol :=
  by
    rcases a with ⟨symbol, terms, term_length⟩
    simp only [List.length_map]
    rw [term_length]

  def applyAtom (g: Grounding τ) (a: Atom τ): Atom τ := {symbol := a.symbol, atom_terms := List.map g.applyTerm a.atom_terms, term_length := applyTerm_preservesLength}

  lemma applyAtom_removesVars [DecidableEq τ.vars] {a: Atom τ} {g: Grounding τ}: (g.applyAtom a).vars = ∅ :=
  by
    unfold applyAtom
    unfold Atom.vars
    simp only
    rw [List.foldl_union_empty]
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, true_and]
    intro x _
    unfold Term.vars
    unfold applyTerm
    cases x <;> simp

  def applyTerm' (g: Grounding τ) : Term τ -> τ.constants
  | Term.constant c =>  c
  | Term.variableDL v => (g v)

  lemma applyTerm'_on_constant_unchanged {g : Grounding τ} {c : τ.constants} : g.applyTerm' c = c := by unfold applyTerm'; simp

  lemma applyTerm'_preservesLength {g: Grounding τ} {a: Atom τ}: (List.map g.applyTerm' a.atom_terms ).length = τ.relationArity a.symbol :=
  by
    rw [List.length_map]
    apply a.term_length

  def applyAtom' (g: Grounding τ) (a: Atom τ): GroundAtom τ := {symbol := a.symbol, atom_terms := List.map g.applyTerm' a.atom_terms, term_length := applyTerm'_preservesLength}

  lemma applyAtom'_on_GroundAtom_unchanged {g : Grounding τ} {ga : GroundAtom τ} : g.applyAtom' ga = ga := by
    unfold applyAtom'
    rw [GroundAtom.ext_iff]
    simp only [GroundAtom.toAtom, List.map_map, true_and]
    apply List.ext_get
    · rw [List.length_map]
    · intro _ _ _
      simp only [List.get_eq_getElem, List.getElem_map, Function.comp_apply]
      rw [applyTerm'_on_constant_unchanged]

  lemma applyAtom'_on_Atom_without_vars_unchanged [DecidableEq τ.vars] {g : Grounding τ} {a : Atom τ} (noVars : a.vars = ∅) : g.applyAtom' a = a := by
    rw [a.toGroundAtom_isSelf noVars]
    rw [applyAtom'_on_GroundAtom_unchanged]

  def applyRule (r: Rule τ) (g: Grounding τ): Rule τ := {head := g.applyAtom r.head, body := List.map g.applyAtom r.body }

  lemma applyRule_removesVars [DecidableEq τ.vars] {r: Rule τ} {g: Grounding τ}: (g.applyRule r).vars = ∅ := by
    unfold applyRule
    unfold Rule.vars
    simp only [Finset.union_eq_empty]
    rw [applyAtom_removesVars]
    simp only [true_and]
    rw [List.foldl_union_empty]
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, true_and]
    intro a _
    apply applyAtom_removesVars

  def applyRule' (g: Grounding τ) (r: Rule τ) : GroundRule τ := {head := g.applyAtom' r.head, body:= List.map g.applyAtom' r.body }
end Grounding

def Program.groundProgram (p : Program τ) := {r : GroundRule τ | ∃ (r': Rule τ) (g: Grounding τ), r' ∈ p ∧ r = g.applyRule' r'}
