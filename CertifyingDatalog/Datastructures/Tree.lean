module

public import Mathlib.Data.Nat.Notation
import Aesop.BuiltinRules
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Subtype
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.SetLike

public section

inductive Tree (A: Type u)
| node: A → List (Tree A) → Tree A

namespace Tree
  variable {A: Type u}

  def root: Tree A → A
  | .node a _ => a

  @[simp, grind =]
  lemma root_def {a : A} {l : List (Tree A)} : root (.node a l) = a := by rfl

  def directSubtrees (t : Tree A) : List (Tree A) :=
    match t with
    | .node _ l => l

  @[simp, grind =]
  lemma directSubtrees_def {a : A} {l : List (Tree A)} : directSubtrees (.node a l) = l := by rfl

  def member (t1 t2: Tree A): Prop :=
    match t1 with
    | .node _ l => t2 ∈ l

  @[simp, grind =]
  lemma member_def {t2 : Tree A} {a : A} {l : List (Tree A)} :
    (Tree.node a l).member t2 ↔ t2 ∈ l := by rfl

  def elem [DecidableEq A] (a: A) (t: Tree A): Bool :=
    match t with
    | .node a' l => (a=a') ∨ List.any l.attach (fun ⟨x, _h⟩ => elem a x)

  @[simp, grind =]
  lemma elem_def [DecidableEq A] {a a' : A} {l : List (Tree A)} :
      elem a' (.node a l) ↔ a' = a ∨ ∃ t ∈ l, elem a' t := by
    simp [elem]

  def elements (t: Tree A): List A :=
    match t with
    | .node a l => List.foldl (fun x ⟨y,_h⟩ => x ++ elements y) [a] l.attach

  def children: Tree A → List A
  | .node _ l => List.map root l

  @[simp, grind =]
  lemma children_def {a : A} {l : List (Tree A)} :
    children (.node a l) = l.map root := by rfl

  def height (t : Tree A): ℕ :=
    match t with
    | .node a l => 1 + (l.attach.map (fun ⟨x, _h⟩ => height x)).max?.getD 0

  lemma height_def (a: A) (l: List (Tree A)): (Tree.node a l).height = 1 + (l.map height).max?.getD 0 :=
  by
    unfold height
    simp

  lemma heightOfMemberIsSmaller (t1 t2: Tree A) (mem: member t1 t2): height t2 < height t1 :=
  by
    cases t1 with
    | node a l =>
      unfold member at mem
      simp only at mem
      rw [height_def]

      cases eq : (l.map height).max? with
      | none => rw [List.max?_eq_none_iff] at eq; simp at eq; rw [eq] at mem; contradiction
      | some max =>
        simp only [Option.getD_some]
        rw [Nat.lt_one_add_iff]
        rw [List.max?_eq_some_iff] at eq
        apply eq.right
        apply List.mem_map_of_mem
        exact mem

  lemma elem_iff_memElements  [DecidableEq A] (t: Tree A) (a : A) : t.elem a = true ↔ a ∈ t.elements :=
  by
    fun_induction elem with
    | case1 a' l ih =>
      simp only [List.any_subtype, List.unattach_attach, List.any_eq_true, Bool.decide_or,
        Bool.or_eq_true, decide_eq_true_eq, elements, List.foldl_subtype,
        List.foldl_append_eq_append, List.cons_append, List.nil_append, List.mem_cons,
        List.mem_flatten, List.mem_map, exists_exists_and_eq_and]
      grind
end Tree
