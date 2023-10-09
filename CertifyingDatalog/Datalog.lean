import Mathlib.Data.Finset.Basic

-- basic definitions
structure signature :=
  (constants: Type)
  (vars: Type)
  (relationSymbols: Type)
  (relationArity: relationSymbols → ℕ)


section basic
variable (τ: signature)

inductive term : Type
| constant : τ.constants → term
| variable : τ.vars → term

structure atom :=
  (symbol: τ.relationSymbols)
  (atom_terms: List (term τ ))
  (term_length: atom_terms.length = τ.relationArity symbol)

structure rule :=
  (head: atom τ)
  (body: List (atom τ))

def Program: Type := List (rule τ)

end basic
-- grounding

section grounding
variable (τ: signature) [DecidableEq τ.vars]

def termVariables: term τ → Finset τ.vars
| (term.constant _) => ∅
| (term.variable v) => {v}

def collectResultsToFinset {A: Type} (f: A → Finset τ.vars): List A → Finset τ.vars
| [] => ∅ 
| hd::tl => (f hd) ∪ (collectResultsToFinset f tl)

def atomVariables (a: atom τ) : Finset τ.vars := collectResultsToFinset τ (termVariables τ) a.atom_terms 

structure groundAtom :=
  (atom: atom τ)
  (grounded: atomVariables τ atom = ∅)

def groundAtom.toAtom (ga: groundAtom τ) := ga.atom

def ruleVariables (r: rule τ): Finset τ.vars := (atomVariables τ r.head) ∪ (collectResultsToFinset τ (atomVariables τ) r.body)

structure groundRule :=
  (rule: rule τ)
  (grounded: ruleVariables τ r = ∅)

def groundRule.toRule (gr: groundRule τ) := gr.rule

def grounding:= τ.vars → τ.constants

def applyGroundingTerm (g: grounding τ) (t: term τ): term τ :=
  match t with
  | term.constant c => term.constant c
  | term.variable v => term.constant (g v)

lemma applyGroundingTermPreservesLength (g:grounding τ) (a: atom τ): (List.map (applyGroundingTerm τ g) a.atom_terms ).length = τ.relationArity a.symbol := 
by
  rcases a with ⟨symbol, terms, term_length⟩
  simp
  rw [ term_length]


def applyGroundingAtom (a: atom τ) (g: grounding τ): atom τ := {symbol:= a.symbol, atom_terms:= List.map (applyGroundingTerm τ g) a.atom_terms, term_length := applyGroundingTermPreservesLength τ g a}

def substitution := τ.vars → Option τ.constants


end grounding
section semantics
variable (τ:signature) [DecidableEq τ.vars]

def interpretation := Set (groundAtom τ)

class database:=
  (contains: groundAtom τ → Prop)



end semantics