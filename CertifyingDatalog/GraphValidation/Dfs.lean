import Mathlib.Data.Finset.Card
import CertifyingDatalog.GraphValidation.Basic
import CertifyingDatalog.GraphValidation.Walks
import CertifyingDatalog.Datastructures.Except

section FoldlExcept
  namespace List
    @[specialize]
    def foldl_except (l : List A) (f : B -> A -> Except Err B) (init : Except Err B): Except Err B :=
      match l with
      | nil => init
      | cons hd tl =>
        match init with
        | Except.error e => Except.error e
        | Except.ok init => foldl_except tl f (f init hd)

    lemma foldl_except_error_stays (l : List A) (f : B -> A -> Except Err B) (err : Err) : l.foldl_except f (Except.error err) = Except.error err := by
      cases l with
      | nil => unfold foldl_except; simp
      | cons _ _ => simp [foldl_except]

    lemma foldl_except_all_ok_of_ok (l : List A) (f : B -> A -> Except Err B) : ∀ init, (l.foldl_except f (Except.ok init)).isOk ->
      ∀ (i : (Fin l.length)), ∃ (res : B), ((l.take i).foldl_except f (Except.ok init)) = Except.ok res ∧ (f res (l.get i)).isOk := by
      induction l with
      | nil => simp
      | cons a as ih =>
        intro init ok i
        simp only [foldl_except] at ok
        cases eq : f init a with
        | error _ => have stays := as.foldl_except_error_stays f;  simp at stays; rw [eq] at ok; rw [stays] at ok; simp [Except.isOk, Except.toBool] at ok
        | ok b =>
          cases eq_i : i.val with
          | zero =>
            have : i = ⟨0, by simp⟩ := by simp [← eq_i]
            rw [this]
            simp only [foldl_except, take_zero, Except.ok.injEq, length_cons,
              Fin.zero_eta, get_eq_getElem, Fin.val_zero, getElem_cons_zero, exists_eq_left']
            rw [eq]
            simp [Except.isOk, Except.toBool]
          | succ j =>
            let j_fin : Fin as.length := ⟨j, by have isLt := i.isLt; rw [eq_i] at isLt; simp at isLt; exact isLt⟩
            simp only [foldl_except, take_succ_cons, get_eq_getElem, length_cons]
            cases eq : f init a with
            | error _ => have stays := as.foldl_except_error_stays f; simp at stays; rw [eq] at ok; rw [stays] at ok; simp [Except.isOk, Except.toBool] at ok
            | ok b =>
              rw [eq] at ok
              simp only [get_eq_getElem] at ih
              specialize ih b ok j_fin
              rcases ih with ⟨res, foldl_ok, f_ok⟩
              exists res
              constructor
              · exact foldl_ok
              · have : i = ⟨j+1, by simp; exact j_fin.isLt⟩ := by simp [← eq_i]
                rw [this]
                simp
                exact f_ok

    lemma foldl_except_preserves_prop
      {l : List A}
      {f : B -> A -> Except Err B}
      (init : Except Err B)
      (prop : B -> Prop)
      (f_preserves_prop : ∀ (b res : B) (a : A), prop b -> a ∈ l -> f b a = Except.ok res -> prop res)
      (init_has_prop : ∀ (init_unwrapped : B), init = Except.ok init_unwrapped -> prop init_unwrapped) :
        ∀ (res : B), l.foldl_except f init = Except.ok res -> prop res := by
        intro res
        induction l generalizing init with
        | nil => simp [foldl_except]; apply init_has_prop
        | cons a as ih =>
          simp [foldl_except]
          split
          · simp
          · apply ih
            · intro b res a prop_b a_in_as
              apply f_preserves_prop
              exact prop_b
              simp only [mem_cons]
              apply Or.inr
              exact a_in_as
            · intro s h
              rename_i init
              apply f_preserves_prop init _ _ (init_has_prop init (by rfl)) (by simp) h

    lemma foldl_except_preserves_prop'
      (l : List A)
      (f : B -> A -> Except Err B)
      (init : Except Err B)
      (prop : B -> Prop)
      (f_preserves_prop : ∀ (b res : B) (a : A), prop b -> a ∈ l -> f b a = Except.ok res -> prop res)
      (some_has_prop : ∃ i : Fin l.length, ∀ (b res : B), ((l.take i).foldl_except f init) = Except.ok b -> f b (l.get i) = Except.ok res -> prop res) :
        ∀ (res : B), l.foldl_except f init = Except.ok res -> prop res := by
        intro res
        induction l generalizing init with
        | nil => simp at some_has_prop
        | cons a as ih =>
          simp only [foldl_except]
          rcases some_has_prop with ⟨i, i_prop⟩
          cases eq : i.val with
          | zero =>
            intro eq_foldl
            cases init with
            | error _ =>
              simp at eq_foldl
            | ok b =>
              apply as.foldl_except_preserves_prop
              · intro b res a b_prop a_mem
                apply f_preserves_prop
                · exact b_prop
                · simp only [mem_cons]
                  apply Or.inr
                  exact a_mem
              · intro init_unwrapped init_unwrapped_eq
                apply i_prop
                · rw [eq]
                  simp only [foldl_except, take_zero, Except.ok.injEq]
                  rfl
                · have : i = ⟨0, by simp⟩ := by apply Fin.eq_of_val_eq; exact eq
                  rw [this]
                  simp only [length_cons, Fin.zero_eta, get_eq_getElem, Fin.val_zero,
                    getElem_cons_zero]
                  exact init_unwrapped_eq
              · simp only at eq_foldl
                exact eq_foldl
          | succ j =>
            cases init with
            | error e => simp
            | ok s =>
              apply ih
              · intro b res a prop_b a_in_as
                apply f_preserves_prop
                · exact prop_b
                · simp only [mem_cons]
                  apply Or.inr
                  exact a_in_as
              · exists ⟨j, by have isLt := i.isLt; rw [eq] at isLt; simp only [length_cons,
                Nat.add_lt_add_iff_right] at isLt; exact isLt⟩
                intro b res eq2 eq3
                apply i_prop
                · simp [eq, foldl_except]; simp only at eq2; exact eq2
                · have : i = ⟨j+1, by rw [← eq]; exact i.isLt⟩ := by apply Fin.eq_of_val_eq; exact eq
                  rw [this]
                  simp only [length_cons, get_eq_getElem, getElem_cons_succ]
                  exact eq3

    lemma foldl_except_is_ok_iff {l : List A} {f : B -> A -> Except Err B} {init : B} (prop : B → Prop)
      (f_preserves_prop : ∀ (b res : B) (a : A), prop b -> a ∈ l -> f b a = Except.ok res -> prop res)
      (init_prop : prop init)
      (f_congr : ∀ (a : A) (b b' : B), prop b → prop b' → (f b a).isOk = (f b' a).isOk)
       :
        (l.foldl_except f (Except.ok init)).isOk ↔ ∀ a ∈ l, (f init a).isOk := by
      induction l generalizing init with
      | nil => simp [Except.is_ok_of_ok, foldl_except]
      | cons hd tl ih =>
        simp [foldl_except]
        cases h : f init hd with
        | error e =>
          conv =>
            rhs
            simp [Except.isOk, Except.toBool]
          simp [foldl_except_error_stays, Except.isOk, Except.toBool]
        | ok s =>
          have s_prop : prop s := f_preserves_prop init s hd init_prop (by simp) h
          rw [ih (by grind) s_prop]
          grind [Except.is_ok_of_ok]

    variable {A: Type u} [DecidableEq A] {B: Type v} [DecidableEq B] [Hashable B]
    open Std

    omit [DecidableEq A] in lemma foldl_except_is_superset_of_f_is_superset
      (l : List A)
      (f : HashSet B -> A -> Except Err (HashSet B))
      (init : HashSet B)
      (f_is_superset : ∀ (set res : HashSet B) (a : A), a ∈ l -> f set a = Except.ok res -> set ⊆ res) :
        ∀ res, l.foldl_except f (Except.ok init) = Except.ok res -> init ⊆ res := by
          intro res eq
          apply l.foldl_except_preserves_prop (init := Except.ok init)
          · intro set res a init_sub_res a_mem f_eq
            apply HashSet.subset_trans
            · exact init_sub_res
            · apply f_is_superset
              · exact a_mem
              · exact f_eq
          · intro init_unwrapped init_unwrapped_eq
            injection init_unwrapped_eq with init_unwrapped_eq
            rw [← init_unwrapped_eq]
            apply HashSet.subset_refl
          · exact eq

    lemma foldl_except_contains_of_some_contains
      {l : List A}
      {f : HashSet B -> A -> Except Err (HashSet B)}
      {init : HashSet B}
      (f_is_superset : ∀ (set res : HashSet B) (a : A), a ∈ l -> f set a = Except.ok res -> set ⊆ res)
      {c : B}
      (some_contains : ∃ a ∈ l, ∀ (b res : HashSet B), f b a = Except.ok res -> res.contains c) :
        ∀ res, l.foldl_except f (Except.ok init) = Except.ok res -> res.contains c := by
          intro res eq
          rcases some_contains with ⟨a, a_in_l, a_prop⟩
          apply l.foldl_except_preserves_prop' f (Except.ok init) (fun b => b.contains c)
          · intro b res a c_in_b a_in_l f_ok
            apply HashSet.subset_iff.mp
            · apply f_is_superset
              · exact a_in_l
              · exact f_ok
            · exact c_in_b
          · exists ⟨l.idxOf a, by rw [List.idxOf_lt_length_iff]; exact a_in_l⟩
            intro b res _ f_ok
            simp only [get_eq_getElem, getElem_idxOf] at f_ok
            apply a_prop _ _ f_ok
          · exact eq
  end List
end FoldlExcept

section Dfs
  variable {A: Type u} [DecidableEq A] [Hashable A]
  open Std

  def NodeCondition (A : Type u) := A -> Except String Unit

  def NodeCondition.true (a : A) (cond : NodeCondition A) : Prop := cond a = Except.ok ()

  namespace Graph
    structure DFS_State {A : Type u} [DecidableEq A] [Hashable A] (G : Graph A) where
      (currNode : A)
      (cond : NodeCondition A)
      (stack : Walk G)
      (fastStack : HashSet A)
      (stacks_eq : ∀ (a : A), a ∈ stack ↔ a ∈ fastStack)
      (nonempty : stack.1 ≠ [])
      (is_front : stack.1.head nonempty = currNode)

    def initalize_DFS_State (a : A) (G : Graph A) (cond : NodeCondition A) (h : a ∈ G.vertices) : DFS_State G where
      currNode := a
      cond := cond
      stack := Walk.singleton G a h
      fastStack := HashSet.emptyWithCapacity.insert a
      stacks_eq := by simp; grind
      nonempty := by simp [Walk.singleton]
      is_front := by simp [Walk.singleton]

    def extend_DFS_State {G : Graph A} (state : DFS_State G) (a : A) (h : a ∈ G.predecessors state.currNode) : DFS_State G where
      currNode := a
      cond := state.cond
      stack := state.stack.prependPredecessor a (Walk.mem_predecessors_of_nonempty state.nonempty state.is_front h)
      fastStack := state.fastStack.insert a
      stacks_eq := by simp [Walk.prependPredecessor, Walk.mem_walk_iff, ←state.stacks_eq]; grind
      nonempty := Walk.nonempty_prependPredecessor (Walk.mem_predecessors_of_nonempty state.nonempty state.is_front h)
      is_front := by simp [Walk.prependPredecessor]

    lemma currNode_mem_of_DFS_State {G : Graph A} {state : DFS_State G} : state.currNode ∈ G.vertices := by
      have := state.stack.2
      simp [List.isWalk] at this
      apply this.1
      have := state.is_front
      rw [← this]
      simp

    def isContained {G : Graph A} (state : DFS_State G) (node : A) : Bool :=
      node ∈ state.fastStack

    lemma isContained_iff {G : Graph A} {state : DFS_State G} {node : A} : isContained state node ↔ node ∈ state.stack := by
      simp [isContained, state.stacks_eq]

    def cond_ok_on_all_canReach (G : Graph A) (b : A) (cond : NodeCondition A) : Prop := ∀ a, G.canReach a b -> cond.true a

    lemma cond_ok_on_all_canReach_iff {G : Graph A} {a : A} (mem : a ∈ G.vertices) {cond : NodeCondition A} : G.cond_ok_on_all_canReach a cond ↔ (∀ b, b ∈ G.predecessors a -> G.cond_ok_on_all_canReach b cond) ∧ cond.true a := by
      constructor
      · intro h
        unfold cond_ok_on_all_canReach at h
        constructor
        · intro b pred
          unfold cond_ok_on_all_canReach
          intro c reach
          apply h
          rw [canReach_iff]
          apply Or.inr
          exists b
        · apply h; apply canReach_refl; apply mem
      · intro h
        unfold cond_ok_on_all_canReach
        intro c canReach
        rw [canReach_iff] at canReach
        cases canReach with
        | inl canReach => rw [canReach.right]; exact h.right
        | inr canReach =>
          rcases canReach with ⟨b, pred, reach⟩
          apply h.left _ pred
          exact reach

    lemma cond_ok_on_all_iff_ok_on_all_canReach (G : Graph A) (cond : NodeCondition A) : (∀ a, a ∈ G.vertices -> cond.true a) ↔ (∀ a, a ∈ G.vertices → G.cond_ok_on_all_canReach a cond) := by
      constructor
      · intro h a _ b reach
        apply h
        unfold canReach at reach
        rcases reach with ⟨w, neq, head, _⟩
        apply w.prop.left; rw [← head]; apply List.head_mem
      · intro h a mem
        apply h a mem
        apply canReach_refl; apply mem

    lemma verify_via_dfs_step_termination_aux {b : A} {G : Graph A} {state : DFS_State G} (b_pred : b ∈ G.predecessors state.currNode) (b_not_in_walk : b ∉ state.stack) :
      (G.vertices.toFinset \ (extend_DFS_State state b b_pred).stack.1.toFinset).card < (G.vertices.toFinset \ state.stack.1.toFinset).card := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff]
        simp only [Finset.mem_sdiff, List.mem_toFinset, not_and, Decidable.not_not]
        exists b
        constructor
        · simp [extend_DFS_State, Walk.prependPredecessor]
        · rw [Finset.insert_subset_iff]
          constructor
          · simp only [Finset.mem_sdiff, List.mem_toFinset]
            constructor
            · apply mem_of_is_pred; apply b_pred
            · exact b_not_in_walk
          · apply Finset.sdiff_subset_sdiff
            · simp
            · rw [Finset.subset_iff]
              intro node mem_walk_a
              simp only [List.mem_toFinset] at mem_walk_a
              simp [extend_DFS_State, Walk.prependPredecessor, mem_walk_a]

    def verify_via_dfs_step {G : Graph A} (state : DFS_State G) (verifiedNodes : HashSet A) : Except String (HashSet A) :=
      if verifiedNodes.contains state.currNode then Except.ok verifiedNodes
      else (state.cond state.currNode).bind (fun _ =>
          if _pred_not_mem_walk : (G.predecessors state.currNode).any (isContained state)
          then Except.error "Cycle detected"
          else
            let verifiedAfterRecursion :=
              (G.predecessors state.currNode).attach.foldl_except (fun verified ⟨pred, mem⟩ =>
                verify_via_dfs_step (extend_DFS_State state pred mem) verified
              ) (Except.ok verifiedNodes)

            verifiedAfterRecursion.map (fun verified => verified.insert state.currNode))
    termination_by Finset.card (List.toFinset G.vertices \ List.toFinset state.stack.1)
    decreasing_by
      apply verify_via_dfs_step_termination_aux
      simp only [List.any_eq_true, isContained_iff, not_exists,
        not_and] at _pred_not_mem_walk
      apply _pred_not_mem_walk _ mem

    lemma verify_via_dfs_step_eq_ok_iff_mem {G : Graph A} {state : DFS_State G} {verifiedNodes : HashSet A} {s : HashSet A} (mem : verifiedNodes.contains state.currNode)
        (h : verify_via_dfs_step state verifiedNodes = Except.ok s) :
        s = verifiedNodes := by
      unfold verify_via_dfs_step at h
      simp only [mem, ↓reduceIte, Except.ok.injEq] at h
      rw [h]

    lemma verify_via_dfs_step_eq_ok_iff_not_mem {G : Graph A} {state : DFS_State G} {verifiedNodes : HashSet A} {s : HashSet A} (mem : ¬verifiedNodes.contains state.currNode = true) :
        verify_via_dfs_step state verifiedNodes = Except.ok s ↔
        ∃ (s' : HashSet A), (G.predecessors state.currNode).attach.foldl_except (fun verified ⟨pred, mem⟩ =>
                verify_via_dfs_step (extend_DFS_State state pred mem) verified
              ) (Except.ok verifiedNodes) = Except.ok s'
        ∧ s = s'.insert state.currNode
        ∧ (∀ (a : A), a ∈ G.predecessors state.currNode → a ∉ state.stack)
        ∧ state.cond state.currNode = Except.ok () := by
      conv =>
        lhs
        unfold verify_via_dfs_step
      simp only [mem, Bool.false_eq_true, ↓reduceIte, Except.bind, List.any_eq_true,
        isContained_iff, dite_eq_ite]
      constructor
      · intro h
        split at h
        · simp at h
        · split at h
          · simp at h
          · unfold Except.map at h
            split at h
            · simp at h
            · grind [isContained_iff]
      · intro s
        obtain ⟨s', h₁, h₂, h₃⟩ := s
        simp [h₃.2]
        split
        · rename_i h
          obtain ⟨x, hx⟩ := h
          have := h₃.1 x hx.1
          grind
        · simp [h₁, Except.map, h₂]

    lemma verify_via_dfs_step_isOk_iff_not_mem {G : Graph A} {state : DFS_State G} {verifiedNodes : HashSet A} (mem : ¬verifiedNodes.contains state.currNode = true) :
        (verify_via_dfs_step state verifiedNodes).isOk ↔
        ((G.predecessors state.currNode).attach.foldl_except (fun verified ⟨pred, mem⟩ =>
                verify_via_dfs_step (extend_DFS_State state pred mem) verified
              ) (Except.ok verifiedNodes)).isOk
        ∧ (∀ (a : A), a ∈ G.predecessors state.currNode → a ∉ state.stack)
        ∧ state.cond state.currNode = Except.ok () := by
      conv =>
        lhs
        unfold verify_via_dfs_step
      simp only [mem, Bool.false_eq_true, ↓reduceIte, Except.bind, List.any_eq_true,
        isContained_iff, dite_eq_ite]
      constructor
      · intro h
        split at h
        · simp [Except.isOk, Except.toBool] at h
        · split at h
          · simp [Except.isOk, Except.toBool] at h
          · unfold Except.map at h
            split at h
            · simp [Except.isOk, Except.toBool] at h
            · rename_i h'
              simp [h', Except.isOk, Except.toBool]
              grind
      · intro s
        obtain ⟨h₁, h₂, h₃⟩ := s
        simp [h₃]
        split
        · rename_i h
          obtain ⟨x, hx⟩ := h
          have := h₂ x hx.1
          grind
        · rw [← Except.is_ok_iff_exists] at h₁
          rcases h₁ with ⟨s, hs⟩
          simp [hs, Except.map, Except.isOk, Except.toBool]

    lemma dfs_step_result_contains_currNode {G : Graph A} {state : DFS_State G} {verifiedNodes : HashSet A} {verifiedAfter : HashSet A}
    (h : verify_via_dfs_step state verifiedNodes = Except.ok verifiedAfter) :
        verifiedAfter.contains state.currNode := by
      by_cases mem : verifiedNodes.contains state.currNode
      · simp [verify_via_dfs_step_eq_ok_iff_mem mem h, mem]
      · rw [verify_via_dfs_step_eq_ok_iff_not_mem mem] at h
        obtain ⟨s, _, h', _⟩ := h
        simp [h']

    lemma dfs_step_extends_verified {G : Graph A} {state : DFS_State G} {verifiedNodes : HashSet A} {verifiedAfter : HashSet A}
    (h : verify_via_dfs_step state verifiedNodes = Except.ok verifiedAfter) :
        verifiedNodes ⊆ verifiedAfter := by
      by_cases mem : verifiedNodes.contains state.currNode
      · simp [verify_via_dfs_step_eq_ok_iff_mem mem h, HashSet.subset_refl]
      · rw [verify_via_dfs_step_eq_ok_iff_not_mem mem] at h
        obtain ⟨s, h₁, h₂, _⟩ := h
        simp [h₂]
        refine HashSet.subset_trans ?_ HashSet.subset_insert
        apply List.foldl_except_is_superset_of_f_is_superset (G.predecessors state.currNode).attach _ _ (by intro _ _ _ _; apply dfs_step_extends_verified)
        simp at h₁
        apply h₁
    termination_by Finset.card (List.toFinset G.vertices \ List.toFinset state.stack.1)
    decreasing_by
      apply verify_via_dfs_step_termination_aux
      grind

    lemma dfs_step_result_valid {G : Graph A} {state : DFS_State G}
      (verifiedNodes : HashSet A) (verifiedAfter : HashSet A)
      (verifiedAfterIsResult : verify_via_dfs_step state verifiedNodes = Except.ok verifiedAfter)
      (verifiedNodesValid : ∀ node, verifiedNodes.contains node ->
        (¬ G.reachableFromCycle node ∧
          G.cond_ok_on_all_canReach node state.cond)
      ) : (∀ node, verifiedAfter.contains node ->
        (¬ G.reachableFromCycle node ∧
          G.cond_ok_on_all_canReach node state.cond)) := by
      by_cases mem : state.currNode ∈ verifiedNodes
      · simpa only [verify_via_dfs_step_eq_ok_iff_mem mem verifiedAfterIsResult]
      · rw [verify_via_dfs_step_eq_ok_iff_not_mem mem] at verifiedAfterIsResult
        obtain ⟨s, h₁, h₂, h₃, h₄⟩ := verifiedAfterIsResult
        simp [h₂]
        have : ∀ (node : A), node ∈ s → (¬ G.reachableFromCycle node ∧
          G.cond_ok_on_all_canReach node state.cond) := by
          apply List.foldl_except_preserves_prop (Except.ok verifiedNodes) (fun s => ∀ n ∈ s, (¬ G.reachableFromCycle n ∧
          G.cond_ok_on_all_canReach n state.cond)) ?_ (by grind) s h₁
          simp
          intro x y z a b c
          have := dfs_step_result_valid _ _ c b
          simp [extend_DFS_State] at this
          apply this
        intro a ha
        cases ha with
        | inl ha =>
          rw [notReachableFromCycleIffPredecessorsNotReachableFromCycle, cond_ok_on_all_canReach_iff (by grind [currNode_mem_of_DFS_State]), NodeCondition.true]
          have : ∀ n ∈ G.predecessors a, n ∈ s := by
            intro n hn
            apply List.foldl_except_contains_of_some_contains ?_ ?_ s h₁
            · grind [dfs_step_extends_verified]
            · simp [ha]
              use n, hn
              apply dfs_step_result_contains_currNode
          grind
        | inr ha => apply this a ha
    termination_by Finset.card (List.toFinset G.vertices \ List.toFinset state.stack.1)
    decreasing_by
      apply verify_via_dfs_step_termination_aux
      grind

    lemma cycle_construction {G : Graph A} {state : DFS_State G} {a : A} (ha : a ∈ G.predecessors state.currNode)
        (ha' : a ∈ state.stack) : reachableFromCycle G a := by
      apply reachableFromCycle_of_predecessesor_in_walk state.nonempty state.is_front ha ha'

    lemma verify_via_dfs_step_mem_stack {G : Graph A} {state : DFS_State G} {verifiedNodes : HashSet A} {a : A} (ha : a ∈ G.predecessors state.currNode)
        (ha' : a ∈ state.stack)
        (verifiedNodesValid : ∀ node, verifiedNodes.contains node ->
          (¬ G.reachableFromCycle node ∧
            G.cond_ok_on_all_canReach node state.cond)
        ) :
        (verify_via_dfs_step state verifiedNodes).isOk = false := by
      have : state.currNode ∉ verifiedNodes := by
        by_contra p
        apply (verifiedNodesValid state.currNode p).1
        obtain ⟨cyc, isCyc, b, hb, hb'⟩ := reachableFromCycle_of_predecessesor_in_walk state.nonempty state.is_front ha ha'
        use cyc, isCyc, b, hb
        apply canReach_trans hb'
        apply canReach_pred ha
      unfold verify_via_dfs_step
      simp [this, isContained_iff]
      cases state.cond state.currNode with
      | error e => rfl
      | ok _ =>
        simp [Except.bind]
        split
        · rfl
        · rename_i h
          simp at h
          specialize h a ha
          contradiction

    lemma dfs_step_semantics
        {G : Graph A} (state : DFS_State G)
        (verifiedNodes : HashSet A)
        (verifiedNodesValid : ∀ node, verifiedNodes.contains node ->
          (¬ G.reachableFromCycle node ∧
            G.cond_ok_on_all_canReach node state.cond)
        ) :
        (verify_via_dfs_step state verifiedNodes).isOk ↔ (¬ G.reachableFromCycle state.currNode ∧ G.cond_ok_on_all_canReach state.currNode state.cond) := by
      by_cases mem : state.currNode ∈ verifiedNodes
      · unfold verify_via_dfs_step
        simpa [mem, Except.isOk, Except.toBool] using verifiedNodesValid state.currNode mem
      · by_cases h' : ∀ (a : A), a ∈ G.predecessors state.currNode → a ∉ state.stack
        · rw [verify_via_dfs_step_isOk_iff_not_mem mem, List.foldl_except_is_ok_iff (fun s => ∀ a ∈ s, ¬ G.reachableFromCycle a ∧ G.cond_ok_on_all_canReach a state.cond) _ verifiedNodesValid]
          · simp
            have : ∀ (a : A) (b : a ∈ G.predecessors state.currNode),
            (verify_via_dfs_step (extend_DFS_State state a b) verifiedNodes).isOk = true ↔  ¬ G.reachableFromCycle a ∧ G.cond_ok_on_all_canReach a state.cond := by
              intro a ha
              · rw [dfs_step_semantics]
                · simp [extend_DFS_State]
                · simp only [HashSet.contains_iff_mem, extend_DFS_State]
                  apply verifiedNodesValid
            rw [cond_ok_on_all_canReach_iff currNode_mem_of_DFS_State]
            simp [this, NodeCondition.true]
            rw [notReachableFromCycleIffPredecessorsNotReachableFromCycle]
            constructor
            · grind
            · intro h
              by_contra p
              simp at p
              apply p
              · grind
              · by_contra q
                simp at q
                obtain ⟨x, hx, hx'⟩ := q
                have := h.1 x hx
                apply this
                apply reachableFromCycle_of_predecessesor_in_walk state.nonempty state.is_front hx hx'
              · grind
          · simp only [Subtype.forall]
            intro a ha s s' hs hs'
            have := dfs_step_semantics (extend_DFS_State state a ha) s hs
            have := dfs_step_semantics (extend_DFS_State state a ha) s' hs'
            grind
          · simp only [List.mem_attach, forall_const, Subtype.forall]
            intro s res a ha hs h
            apply dfs_step_result_valid s res h hs
        · simp at h'
          obtain ⟨x, hx, hx'⟩ := h'
          simp [verify_via_dfs_step_mem_stack hx hx' verifiedNodesValid]
          have := cycle_construction hx hx'
          have : G.reachableFromCycle state.currNode := by
            obtain ⟨cyc, isCyc, a, ha, ha'⟩ := this
            use cyc, isCyc, a, ha
            apply canReach_trans ha' (canReach_pred hx)
          grind
    termination_by Finset.card (List.toFinset G.vertices \ List.toFinset state.stack.val)
    decreasing_by
      all_goals
        simp [extend_DFS_State]
        apply verify_via_dfs_step_termination_aux ha (h' a ha)

    def verify_via_dfs (G : Graph A) (cond : NodeCondition A) : Except String Unit :=
      (G.vertices.attach.foldl_except
        (fun acc ⟨a, h⟩ => verify_via_dfs_step (initalize_DFS_State a G cond h) acc)
        (Except.ok HashSet.emptyWithCapacity)).map (fun _ => ())

    lemma dfs_semantics (G : Graph A) (cond : NodeCondition A) : G.verify_via_dfs cond = Except.ok () ↔ G.isAcyclic ∧ ∀ a ∈ G.vertices, cond.true a := by
      simp only [verify_via_dfs, Except.map_ok_unit, acyclicIffAllNotReachableFromCycle]
      rw [List.foldl_except_is_ok_iff (fun s => ∀ a ∈ s, ¬ G.reachableFromCycle a ∧
            G.cond_ok_on_all_canReach a cond)]
      · have : ∀ (a : A) (h : a ∈ G.vertices),
          (verify_via_dfs_step (initalize_DFS_State a G cond h) HashSet.emptyWithCapacity).isOk
          ↔ ¬ G.reachableFromCycle a ∧ G.cond_ok_on_all_canReach a cond := by
          intro a h
          rw [dfs_step_semantics]
          · simp [initalize_DFS_State]
          · simp [initalize_DFS_State]
        simp only [List.mem_attach, this, forall_const, Subtype.forall,
          cond_ok_on_all_iff_ok_on_all_canReach]
        grind
      · simp only [List.mem_attach, forall_const, Subtype.forall]
        intro s res a mem hs h
        have := dfs_step_result_valid s res h
        simp only [HashSet.contains_iff_mem, initalize_DFS_State] at this
        apply this hs
      · simp
      · intro x s s' hs hs'
        have h₁ := dfs_step_semantics (initalize_DFS_State x.1 G cond x.2) s
        have h₂ := dfs_step_semantics (initalize_DFS_State x.1 G cond x.2) s'
        simp only [HashSet.contains_iff_mem, initalize_DFS_State] at h₁ h₂ ⊢
        grind
  end Graph
end Dfs
