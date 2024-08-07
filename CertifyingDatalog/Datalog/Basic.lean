import CertifyingDatalog.Basic

section Basic
  -- TODO: using different universes for constants and vars causes problems for some reason...
  structure Signature where
    (constants: Type u)
    (vars: Type u)
    (relationSymbols: Type w)
    (relationArity: relationSymbols → ℕ)

  inductive Term (τ: Signature) [DecidableEq τ.vars] [DecidableEq τ.relationSymbols] [DecidableEq τ.constants] [Hashable τ.constants] [Hashable τ.vars] [Hashable τ.relationSymbols] where
  | constant : τ.constants → Term τ
  | variableDL : τ.vars → Term τ
  deriving DecidableEq, Hashable

  variable (τ: Signature) [DecidableEq τ.vars] [DecidableEq τ.relationSymbols] [DecidableEq τ.constants] [Hashable τ.constants] [Hashable τ.vars] [Hashable τ.relationSymbols] [ToString τ.constants] [ToString τ.vars] [ToString τ.relationSymbols]

  instance : ToString (Term τ) where
    toString t := match t with
      | .constant c => ToString.toString c
      | .variableDL v => ToString.toString v

  instance: Coe (τ.constants) (Term τ) where
    coe := Term.constant

  @[ext]
  structure Atom where
    (symbol: τ.relationSymbols)
    (atom_terms: List (Term τ))
    (term_length: atom_terms.length = τ.relationArity symbol)
  deriving DecidableEq, Hashable

  instance : ToString (Atom τ) where
    toString a :=
      let terms :=
        match a.atom_terms with
        | [] => ""
        | hd::tl => List.foldl (fun x y => x ++ "," ++ (ToString.toString y)) (ToString.toString hd) tl
      (ToString.toString a.symbol) ++ "(" ++ terms ++ ")"

  @[ext]
  structure Rule where
    (head: Atom τ)
    (body: List (Atom τ))
  deriving DecidableEq

  instance : ToString (Rule τ) where
    toString r := match r.body with
      | [] => (ToString.toString r.head) ++ "."
      | hd::tl => (ToString.toString r.head) ++ ":-" ++ (List.foldl (fun x y => x ++ "," ++ (ToString.toString y) ) (ToString.toString hd) tl)

  abbrev Program := List (Rule τ)
end Basic

section Methods
  variable {τ: Signature} [DecidableEq τ.vars] [DecidableEq τ.relationSymbols] [DecidableEq τ.constants] [Hashable τ.constants] [Hashable τ.vars] [Hashable τ.relationSymbols] [ToString τ.constants] [ToString τ.vars] [ToString τ.relationSymbols]

  namespace Term
    def vars: Term τ → Finset τ.vars
    | Term.constant _ => ∅
    | Term.variableDL v => {v}

    def toConstant (t: Term τ) (h: t.vars = ∅) : τ.constants :=
      match t with
      | Term.constant c => c
      | Term.variableDL v => by simp [Term.vars] at h 
  end Term

  namespace Atom
    def vars (a: Atom τ) : Finset τ.vars := List.foldl_union Term.vars ∅ a.atom_terms

    lemma vars_subset_impl_term_vars_subset {a: Atom τ} {t: Term τ}{S: Set τ.vars}(mem: t ∈ a.atom_terms) (subs: ↑ a.vars ⊆ S): ↑ t.vars ⊆ S := by
      apply Set.Subset.trans (b:= a.vars)
      unfold Atom.vars
      apply List.subset_result_foldl_union
      exact mem
      exact subs

    lemma vars_empty_iff (a: Atom τ): a.vars = ∅ ↔ ∀ (t: Term τ), t ∈ a.atom_terms → t.vars = ∅ := by
      unfold Atom.vars
      rw [List.foldl_union_empty]
      simp
  end Atom

  namespace Rule
    def vars (r: Rule τ): Finset τ.vars := r.head.vars ∪ (List.foldl_union Atom.vars ∅ r.body)

    lemma vars_subset_impl_atom_vars_subset {r: Rule τ} {a: Atom τ} {S: Set τ.vars}(mem: a = r.head ∨ a ∈ r.body) (subs: ↑ r.vars ⊆ S): ↑ a.vars ⊆ S :=
    by
      apply Set.Subset.trans (b:= r.vars)
      unfold Rule.vars
      rw [Set.subset_def]
      intro x x_mem
      simp
      cases mem with
      | inl h =>
        rw [h] at x_mem
        left
        apply x_mem
      | inr h =>
        right
        rw [List.mem_foldl_union]
        right
        use a
        simp at x_mem
        constructor 
        · exact h 
        · exact x_mem
      apply subs

    def isSafe (r: Rule τ) : Prop := r.head.vars ⊆ List.foldl_union Atom.vars ∅ r.body

    def checkSafety (r: Rule τ) : Except String Unit :=
      if r.head.vars \ (List.foldl_union Atom.vars ∅ r.body) = ∅
      then Except.ok ()
      else Except.error ("Rule" ++ ToString.toString r ++ "is not safe ")

    lemma checkSafety_iff_isSafe (r: Rule τ) : r.checkSafety = Except.ok () ↔ r.isSafe := by
      unfold checkSafety
      unfold isSafe
      split <;> (simp at *; assumption)
  end Rule

  namespace Program
    def isSafe (p : Program τ) : Prop := ∀ r, r ∈ p -> r.isSafe

    def checkSafety (p : Program τ): Except String Unit :=
      List.mapExceptUnit p (fun r => r.checkSafety)

    lemma checkSafety_iff_isSafe (p: Program τ): p.checkSafety = Except.ok () ↔ p.isSafe := by
      unfold checkSafety
      unfold isSafe
      rw [List.mapExceptUnit_iff]
      simp [Rule.checkSafety_iff_isSafe]
  end Program
end Methods

