import CertifyingDatalog.Datastructures.List

inductive Tree (A: Type u)
| node: A → List (Tree A) → Tree A

namespace Tree
  variable {A: Type u}

  def member (t1 t2: Tree A): Prop :=
    match t1 with
    | .node _ l => t2 ∈ l

  def elem  [DecidableEq A] (a: A) (t: Tree A): Bool  :=
    match t with
    | .node a' l => (a=a') ∨ List.any l.attach (fun ⟨x, _h⟩ => elem a x)

  def elements (t: Tree A): List A :=
    match t with
    | .node a l => List.foldl (fun x ⟨y,_h⟩ => x ++ elements y) [a] l.attach

  def root: Tree A → A
  | .node a _ => a

  def children: Tree A → List A
  | .node _ l => List.map root l

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
