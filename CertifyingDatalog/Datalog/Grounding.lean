module

public import CertifyingDatalog.Datalog.Basic
import Mathlib.Data.Finset.Lattice.Lemmas

public section

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

  lemma eq_atom_iff {ga : GroundAtom τ} {a : Atom τ} :
      ga = a ↔ ga.symbol = a.symbol ∧ ∃ (h : a.atom_terms.length = ga.atom_terms.length),
        ∀ (i : ℕ) (hi : i < a.atom_terms.length), a.atom_terms[i] = Term.constant ga.atom_terms[i] := by
    simp only [toAtom, Atom.ext_iff, List.ext_get_iff, List.length_map, List.get_eq_getElem,
      List.getElem_map, and_congr_right_iff]
    grind

  lemma vars_empty {ga : GroundAtom τ} [DecidableEq τ.vars] : ga.toAtom.vars = ∅ := by
    simp only [toAtom, Atom.vars_empty_iff, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    intro _ _
    simp [Term.vars_eq_emptyset_iff]
end GroundAtom

namespace Atom
  lemma eq_GroundAtom_iff {ga : GroundAtom τ} {a : Atom τ} :
      a = ga ↔ ga.symbol = a.symbol ∧ ∃ (h : a.atom_terms.length = ga.atom_terms.length),
        ∀ (i : ℕ) (hi : i < a.atom_terms.length), a.atom_terms[i] = Term.constant ga.atom_terms[i] := by
    simp [← GroundAtom.eq_atom_iff, Eq.comm (a:= a)]

  def toGroundAtom (a: Atom τ) [DecidableEq τ.vars] (h: a.vars = ∅) : GroundAtom τ :=
  {
    symbol:= a.symbol,
    atom_terms := List.map (fun ⟨t, t_in_a⟩ => t.toConstant (a.vars_empty_iff.mp h t t_in_a)) a.atom_terms.attach,
    term_length := by simp; apply a.term_length
  }

  @[simp]
  lemma toGroundAtom_symbol {a : Atom τ} [DecidableEq τ.vars] (h: a.vars = ∅) :
    (a.toGroundAtom h).symbol = a.symbol := by rfl

  @[simp]
  lemma toGroundAtom_atomTerms {a : Atom τ} [DecidableEq τ.vars] (h: a.vars = ∅) :
    (a.toGroundAtom h).atom_terms = a.atom_terms.attach.map (fun ⟨t, t_in_a⟩ => t.toConstant (a.vars_empty_iff.mp h t t_in_a)) := by rfl

  lemma toGroundAtom_isSelf [DecidableEq τ.vars] {a: Atom τ} (h: a.vars = ∅): a = a.toGroundAtom h :=
  by
    simp only [GroundAtom.toAtom, toGroundAtom, List.map_map, Atom.ext_iff, true_and]
    apply List.ext_get
    · simp
    · intro n h1 h2
      simp [Term.toConstant_eq_self]
end Atom

namespace GroundAtom
  lemma toAtom_toGroundAtom [DecidableEq τ.vars] (ga : GroundAtom τ) : ga.toAtom.toGroundAtom GroundAtom.vars_empty = ga := by
    simp only [Atom.toGroundAtom]
    rw [GroundAtom.eq_iff_toAtom_eq]
    simp only [GroundAtom.toAtom, List.map_map, Atom.mk.injEq, true_and]
    apply List.ext_get
    · simp
    · intro n h1 h2
      simp
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

  lemma eq_rule_iff {gr : GroundRule τ} {r : Rule τ} :
      gr = r ↔ gr.head = r.head ∧ ∃ (h : gr.body.length = r.body.length), ∀ (i : ℕ) (hi : i < r.body.length),
        gr.body[i] = r.body[i] := by
    simp only [toRule, Rule.ext_iff, and_congr_right_iff]
    intro _
    simp only [List.ext_get_iff, List.length_map, List.get_eq_getElem, List.getElem_map]
    grind

  def bodySet [DecidableEq τ.constants] [DecidableEq τ.vars] [DecidableEq τ.relationSymbols] (r: GroundRule τ): Finset (GroundAtom τ) := List.toFinset r.body

  lemma in_bodySet_iff_in_body [DecidableEq τ.constants] [DecidableEq τ.vars] [DecidableEq τ.relationSymbols] {r: GroundRule τ} : ∀ a, a ∈ r.body ↔ a ∈ r.bodySet := by simp [bodySet]
end GroundRule

lemma Rule.eq_GroundRule_iff {gr : GroundRule τ} {r : Rule τ} :
    r = gr ↔ gr.head = r.head ∧ ∃ (h : gr.body.length = r.body.length), ∀ (i : ℕ) (hi : i < r.body.length),
      gr.body[i] = r.body[i] := by
  simp [← GroundRule.eq_rule_iff, Eq.comm (a := r)]

namespace Grounding
  def applyTerm (g: Grounding τ) : Term τ -> Term τ
  | Term.constant c => Term.constant c
  | Term.variableDL v => Term.constant (g v)

  @[simp]
  lemma applyTerm_const {c : τ.constants} {g : Grounding τ} :
    g.applyTerm (Term.constant c) = Term.constant c := by rfl

  @[simp]
  lemma applyTerm_var {v : τ.vars} {g : Grounding τ} :
    g.applyTerm (Term.variableDL v) = Term.constant (g v) := by rfl

  lemma applyTerm_removesVars {g: Grounding τ} {t: Term τ} : (g.applyTerm t).vars = ∅ := by
    simp only [applyTerm, Term.vars_eq_emptyset_iff]
    cases t <;> simp

  lemma applyTerm_preservesLength {g: Grounding τ} {a: Atom τ}: (List.map g.applyTerm a.atom_terms).length = τ.relationArity a.symbol :=
  by
    rcases a with ⟨symbol, terms, term_length⟩
    simp only [List.length_map]
    rw [term_length]

  def applyAtom (g: Grounding τ) (a: Atom τ): Atom τ := {symbol := a.symbol, atom_terms := List.map g.applyTerm a.atom_terms, term_length := applyTerm_preservesLength}

  lemma applyAtom_removesVars [DecidableEq τ.vars] {a: Atom τ} {g: Grounding τ}: (g.applyAtom a).vars = ∅ :=
  by
    simp only [applyAtom, Atom.vars_empty_iff, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    intro x _
    simp only [applyTerm, Term.vars_eq_emptyset_iff]
    cases x <;> simp

  @[simp]
  lemma applyAtom_symbol {a : Atom τ} {g : Grounding τ} :
    (g.applyAtom a).symbol = a.symbol := by rfl

  @[simp]
  lemma applyAtom_terms {a : Atom τ} {g : Grounding τ} :
    (g.applyAtom a).atom_terms = a.atom_terms.map g.applyTerm := by rfl

  def applyTerm' (g: Grounding τ) : Term τ -> τ.constants
  | Term.constant c =>  c
  | Term.variableDL v => (g v)

  @[simp]
  lemma applyTerm'_const {c : τ.constants} {g : Grounding τ} :
    g.applyTerm' (Term.constant c) = c := by rfl

  @[simp]
  lemma applyTerm'_var {v : τ.vars} {g : Grounding τ} :
    g.applyTerm' (Term.variableDL v) = g v := by rfl

  lemma applyTerm'_preservesLength {g: Grounding τ} {a: Atom τ}: (List.map g.applyTerm' a.atom_terms ).length = τ.relationArity a.symbol :=
  by
    rw [List.length_map]
    apply a.term_length

  def applyAtom' (g: Grounding τ) (a: Atom τ): GroundAtom τ := {symbol := a.symbol, atom_terms := List.map g.applyTerm' a.atom_terms, term_length := applyTerm'_preservesLength}

  @[simp]
  lemma applyAtom'_symbol {a : Atom τ} {g : Grounding τ} :
    (g.applyAtom' a).symbol = a.symbol := by rfl

  @[simp]
  lemma applyAtom'_terms {a : Atom τ} {g : Grounding τ} :
    (g.applyAtom' a).atom_terms = a.atom_terms.map g.applyTerm' := by rfl

  lemma applyAtom'_on_GroundAtom_unchanged {g : Grounding τ} {ga : GroundAtom τ} : g.applyAtom' ga = ga := by
    unfold applyAtom'
    rw [GroundAtom.ext_iff]
    simp only [GroundAtom.toAtom, List.map_map, true_and]
    apply List.ext_get
    · rw [List.length_map]
    · intro _ _ _
      simp [List.get_eq_getElem, List.getElem_map, Function.comp_apply]

  lemma applyAtom'_on_Atom_without_vars_unchanged [DecidableEq τ.vars] {g : Grounding τ} {a : Atom τ} (noVars : a.vars = ∅) : g.applyAtom' a = a := by
    rw [a.toGroundAtom_isSelf noVars]
    rw [applyAtom'_on_GroundAtom_unchanged]

  def applyRule (r: Rule τ) (g: Grounding τ): Rule τ := {head := g.applyAtom r.head, body := List.map g.applyAtom r.body }

  @[simp]
  lemma applyRule_head {r : Rule τ} {g : Grounding τ} : (g.applyRule r).head = g.applyAtom r.head := by rfl

  @[simp]
  lemma applyRule_body {r : Rule τ} {g : Grounding τ} :
    (g.applyRule r).body = r.body.map g.applyAtom := by rfl

  lemma applyRule_removesVars [DecidableEq τ.vars] {r: Rule τ} {g: Grounding τ}: (g.applyRule r).vars = ∅ := by
    simp [Rule.vars_eq_empty_iff, applyRule, applyAtom_removesVars]

  def applyRule' (g: Grounding τ) (r: Rule τ) : GroundRule τ := {head := g.applyAtom' r.head, body:= List.map g.applyAtom' r.body }

  @[simp]
  lemma applyRule'_head {r : Rule τ} {g : Grounding τ} : (g.applyRule' r).head = g.applyAtom' r.head := by rfl

  @[simp]
  lemma applyRule'_body {r : Rule τ} {g : Grounding τ} :
    (g.applyRule' r).body = r.body.map g.applyAtom' := by rfl
end Grounding

def Program.groundProgram (p : Program τ) := {r : GroundRule τ | ∃ (r': Rule τ) (g: Grounding τ), r' ∈ p ∧ r = g.applyRule' r'}

@[simp]
lemma Program.mem_groundProgram_iff {gr : GroundRule τ} {p : Program τ} :
    gr ∈ p.groundProgram ↔ ∃ (r : Rule τ) (g : Grounding τ), r ∈ p ∧ gr = g.applyRule' r := by
  simp [groundProgram]
