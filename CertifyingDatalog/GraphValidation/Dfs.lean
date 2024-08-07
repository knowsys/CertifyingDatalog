import Mathlib.Data.Finset.Card
import CertifyingDatalog.GraphValidation.Basic
import CertifyingDatalog.GraphValidation.Walks

section FoldlExcept
  namespace List
    def foldl_except (l : List A) (f : B -> A -> Except Err B) (init : Except Err B): Except Err B := 
      l.foldl 
        (fun acc a => match acc with 
        | Except.error msg => Except.error msg
        | Except.ok b => f b a
        ) 
        init 

    lemma foldl_except_error_stays (l : List A) (f : B -> A -> Except Err B) : ∀ err, l.foldl_except f (Except.error err) = Except.error err := by 
      induction l with 
      | nil => unfold foldl_except; simp
      | cons _ _ ih => apply ih

    lemma foldl_expect_some_error_of_error (l : List A) (f : B -> A -> Except Err B) : ∀ ok err, l.foldl_except f (Except.ok ok) = Except.error err -> 
      ∃ (i : (Fin l.length)) (res : B), ((l.take i).foldl_except f (Except.ok ok)) = Except.ok res ∧ f res (l.get i) = Except.error err := by
      induction l with 
      | nil => simp [foldl_except]
      | cons a as ih =>
        intro ok err foldl_except_err
        simp [foldl_except] at foldl_except_err
        cases eq : f ok a with 
        | error step_err =>
          exists ⟨0, by simp⟩ 
          exists ok
          constructor
          · simp [foldl_except]
          · rw [eq] at foldl_except_err
            rw [← foldl_except] at foldl_except_err
            rw [foldl_except_error_stays] at foldl_except_err
            rw [← foldl_except_err]
            exact eq
        | ok step_res =>
          specialize ih step_res err (by simp [foldl_except, ← eq]; exact foldl_except_err)
          rcases ih with ⟨i, res, foldl, cond⟩ 
          exists ⟨i.val + 1, by simp⟩
          exists res
          simp [foldl_except]
          simp [foldl_except] at foldl
          constructor
          · rw [eq]; exact foldl
          · exact cond 

    lemma foldl_except_all_ok_of_ok (l : List A) (f : B -> A -> Except Err B) : ∀ init, (l.foldl_except f (Except.ok init)).isOk -> 
      ∀ (i : (Fin l.length)), ∃ (res : B), ((l.take i).foldl_except f (Except.ok init)) = Except.ok res ∧ (f res (l.get i)).isOk := by
      induction l with 
      | nil => simp
      | cons a as ih =>
        intro init ok i
        simp [foldl_except] at ok
        cases eq : f init a with 
        | error _ => have stays := as.foldl_except_error_stays f; simp [foldl_except] at stays; rw [eq] at ok; rw [stays] at ok; simp [Except.isOk, Except.toBool] at ok
        | ok b => 
          cases eq_i : i.val with 
          | zero => 
            have : i = ⟨0, by simp⟩ := by simp [← eq_i]
            rw [this]
            simp [foldl_except]
            rw [eq]
            simp [Except.isOk, Except.toBool]
          | succ j => 
            let j_fin : Fin as.length := ⟨j, by have isLt := i.isLt; rw [eq_i] at isLt; simp at isLt; exact isLt⟩ 
            simp [foldl_except]
            cases eq : f init a with 
            | error _ => have stays := as.foldl_except_error_stays f; simp [foldl_except] at stays; rw [eq] at ok; rw [stays] at ok; simp [Except.isOk, Except.toBool] at ok
            | ok b => 
              rw [eq] at ok
              simp [foldl_except] at ih
              specialize ih b ok j_fin
              rcases ih with ⟨res, foldl_ok, f_ok⟩
              simp at foldl_ok
              exists res
              constructor
              · exact foldl_ok
              · have : i = ⟨j+1, by simp; exact j_fin.isLt⟩ := by simp [← eq_i] 
                rw [this]
                simp
                exact f_ok

    lemma foldl_except_preserves_prop 
      (l : List A) 
      (f : B -> A -> Except Err B) 
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
          apply ih
          · intro b res a prop_b a_in_as
            apply f_preserves_prop
            exact prop_b
            simp
            apply Or.inr
            exact a_in_as
          · split
            · simp
            · intro step_res
              apply f_preserves_prop
              apply init_has_prop
              rfl
              simp

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
          simp [foldl_except]
          rcases some_has_prop with ⟨i, i_prop⟩ 
          cases eq : i.val with 
          | zero => 
            intro eq_foldl
            cases init with 
            | error _ => 
              rw [← foldl_except] at eq_foldl
              simp at eq_foldl
              rw [foldl_except_error_stays] at eq_foldl
              contradiction
            | ok b => 
              apply as.foldl_except_preserves_prop f (f b a)
              · intro b res a b_prop a_mem
                apply f_preserves_prop
                exact b_prop
                simp
                apply Or.inr
                exact a_mem
              intro init_unwrapped init_unwrapped_eq
              apply i_prop
              rw [eq]
              simp [foldl_except]
              rfl
              have : i = ⟨0, by simp⟩ := by apply Fin.eq_of_val_eq; exact eq
              rw [this]
              simp
              exact init_unwrapped_eq
              rw [← foldl_except] at eq_foldl
              simp at eq_foldl
              exact eq_foldl
          | succ j => 
            apply ih
            · intro b res a prop_b a_in_as
              apply f_preserves_prop
              exact prop_b
              simp
              apply Or.inr
              exact a_in_as
            · exists ⟨j, by have isLt := i.isLt; rw [eq] at isLt; simp at isLt; exact isLt⟩
              intro b res eq2 eq3
              apply i_prop
              · simp [eq, foldl_except]; simp [foldl_except] at eq2; exact eq2
              · have : i = ⟨j+1, by rw [← eq]; exact i.isLt⟩ := by apply Fin.eq_of_val_eq; exact eq 
                rw [this]
                simp
                exact eq3
  
    variable {A: Type u} [DecidableEq A] {B: Type v} [DecidableEq B] [Hashable B]
    open Batteries

    lemma foldl_except_is_superset_of_f_is_superset 
      (l : List A) 
      (f : HashSet B -> A -> Except Err (HashSet B)) 
      (init : HashSet B)
      (f_is_superset : ∀ (set res : HashSet B) (a : A), a ∈ l -> f set a = Except.ok res -> set ⊆ res) :
        ∀ res, l.foldl_except f (Except.ok init) = Except.ok res -> init ⊆ res := by 
          intro res eq
          apply l.foldl_except_preserves_prop f (Except.ok init)
          intro set res a init_sub_res a_mem f_eq
          apply HashSet.subset_trans
          exact init_sub_res
          apply f_is_superset
          exact a_mem
          exact f_eq
          · intro init_unwrapped init_unwrapped_eq
            injection init_unwrapped_eq with init_unwrapped_eq
            rw [← init_unwrapped_eq]
            apply HashSet.subset_refl
          exact eq

    lemma foldl_except_contains_of_some_contains 
      (l : List A) 
      (f : HashSet B -> A -> Except Err (HashSet B)) 
      (init : HashSet B)
      (f_is_superset : ∀ (set res : HashSet B) (a : A), a ∈ l -> f set a = Except.ok res -> set ⊆ res)
      (c : B)
      (some_contains : ∃ a ∈ l, ∀ (b res : HashSet B), f b a = Except.ok res -> res.contains c) :
        ∀ res, l.foldl_except f (Except.ok init) = Except.ok res -> res.contains c := by 
          intro res eq
          rcases some_contains with ⟨a, a_in_l, a_prop⟩ 
          apply l.foldl_except_preserves_prop' f (Except.ok init) (fun b => b.contains c)
          · intro b res a c_in_b a_in_l f_ok
            apply HashSet.subset_iff.mp
            apply f_is_superset
            exact a_in_l
            exact f_ok
            exact c_in_b
          · exists ⟨l.indexOf a, by rw [List.indexOf_lt_length]; exact a_in_l⟩
            intro b res _ f_ok
            simp at f_ok
            apply a_prop
            exact f_ok
          · exact eq
  end List
end FoldlExcept

section Dfs
  variable {A: Type u} [DecidableEq A] [Hashable A]
  open Batteries

  def NodeSuccCondition (A : Type u) := A -> List A -> Except String Unit
  def NodeCondition (A : Type u) := A -> Except String Unit

  def NodeCondition.true (a : A) (cond : NodeCondition A) : Prop := cond a = Except.ok ()

  namespace Graph
    def node_succ_cond_to_node_cond (G : Graph A) (cond : NodeSuccCondition A) : NodeCondition A := fun a => cond a (G.successors a)
    
    def cond_ok_on_all_canReach (G : Graph A) (a : A) (cond : NodeCondition A) : Prop := ∀ b, G.canReach a b -> cond.true b

    lemma cond_ok_on_all_canReach_iff (G : Graph A) (a : A) (mem : a ∈ G.vertices) (cond : NodeCondition A) : G.cond_ok_on_all_canReach a cond ↔ (∀ b, b ∈ G.successors a -> G.cond_ok_on_all_canReach b cond) ∧ cond.true a := by
      constructor
      · intro h
        unfold cond_ok_on_all_canReach at h
        constructor
        · intro b succ
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
        | inl canReach => rw [← canReach.right]; exact h.right
        | inr canReach => 
          rcases canReach with ⟨b, succ, reach⟩ 
          apply h.left
          exact succ
          exact reach

    lemma cond_ok_on_all_iff_ok_on_all_canReach (G : Graph A) (cond : NodeCondition A) : (∀ a, a ∈ G.vertices -> cond.true a) ↔ (∀ a, G.cond_ok_on_all_canReach a cond) := by
      constructor
      · intro h a b reach
        apply h
        unfold canReach at reach
        rcases reach with ⟨w, neq, head, _⟩
        apply w.prop.left; rw [← head]; apply List.head_mem
      · intro h a mem
        apply h a
        apply canReach_refl; apply mem

    lemma verify_acyclicity_and_cond_via_dfs_step_termination_aux {a b : A} (G : Graph A) (walkToA : {w : Walk G // w.val.head? = some a}) (b_succ : b ∈ G.successors a) (b_not_in_walk : b ∉ walkToA.val.val) : 
      (G.vertices.toFinset \ (⟨walkToA.val.appendSuccessor b (by unfold Walk.successors; simp [walkToA.prop]; exact b_succ), by (unfold Walk.appendSuccessor; simp)⟩ : {w : Walk G // w.val.head? = some b}).val.val.toFinset).card < (G.vertices.toFinset \ walkToA.val.val.toFinset).card := by 
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff]
        simp
        exists b
        constructor
        · intro _
          unfold Walk.appendSuccessor
          simp
        · rw [Finset.insert_subset_iff]
          constructor
          · simp
            constructor
            · apply mem_of_is_succ; apply b_succ
            · exact b_not_in_walk 
          · apply Finset.sdiff_subset_sdiff
            · simp
            · rw [Finset.subset_iff]
              intro node mem_walk_a
              simp at mem_walk_a
              unfold Walk.appendSuccessor
              simp
              apply Or.inr; exact mem_walk_a

    def verify_acyclicity_and_cond_via_dfs_step {a : A} (G : Graph A) (cond : NodeCondition A) (walkToA : {w : Walk G // w.val.head? = some a}) (verifiedNodes : HashSet A) : Except String (HashSet A) := 
      if verifiedNodes.contains a then Except.ok verifiedNodes
      else match cond a with 
        | Except.error msg => Except.error msg
        | Except.ok _ => 
          if succ_not_mem_walk : (G.successors a).any (fun succ => succ ∈ walkToA.val.val)
          then Except.error "Cycle detected"
          else 
            let verifiedAfterRecursion := 
              (G.successors a).attach.foldl_except (fun verified ⟨succ, mem⟩ =>
                let walkToSucc : {w : Walk G // w.val.head? = some succ} := ⟨walkToA.val.appendSuccessor succ (by unfold Walk.successors; simp [walkToA.prop]; exact mem), by (unfold Walk.appendSuccessor; simp)⟩
                have _termination := G.verify_acyclicity_and_cond_via_dfs_step_termination_aux walkToA mem (by simp at succ_not_mem_walk; apply succ_not_mem_walk; exact mem)
                    
                G.verify_acyclicity_and_cond_via_dfs_step 
                  cond 
                  walkToSucc
                  verified 
              ) (Except.ok verifiedNodes)

            verifiedAfterRecursion.map (fun verified => verified.insert a)
    termination_by Finset.card (List.toFinset G.vertices \ List.toFinset walkToA.val.val)

    lemma dfs_step_result_contains_a {a : A} (G : Graph A) (cond : NodeCondition A) (walkToA : {w : Walk G // w.val.head? = some a}) (verifiedNodes : HashSet A) (verifiedAfter : HashSet A) : 
      verify_acyclicity_and_cond_via_dfs_step G cond walkToA verifiedNodes = Except.ok verifiedAfter -> verifiedAfter.contains a := by 
      intro h
      unfold verify_acyclicity_and_cond_via_dfs_step at h
      simp at h
      split at h
      · injection h with h; rw [← h]; assumption
      split at h 
      · contradiction
      split at h
      · contradiction
      unfold Except.map at h
      split at h
      · contradiction
      simp at h
      rw [← h]
      rw [HashSet.contains_insert]
      apply Or.inr
      rfl

    lemma dfs_step_extends_verified {a : A} (G : Graph A) (cond : NodeCondition A) (walkToA : {w : Walk G // w.val.head? = some a}) (verifiedNodes : HashSet A) (verifiedAfter : HashSet A) : 
      verify_acyclicity_and_cond_via_dfs_step G cond walkToA verifiedNodes = Except.ok verifiedAfter -> verifiedNodes ⊆ verifiedAfter := by 
      intro h
      unfold verify_acyclicity_and_cond_via_dfs_step at h
      simp at h
      split at h
      · injection h with h; rw [h]; apply HashSet.subset_refl
      split at h 
      · contradiction
      split at h
      · contradiction
      case isFalse succ_not_mem_walk =>
        unfold Except.map at h
        split at h
        · contradiction
        case h_2 eq =>
          injection h with h
          rw [← h]
          simp

          apply HashSet.subset_trans
          · apply (G.successors a).attach.foldl_except_is_superset_of_f_is_superset
              (fun b succ => 
                let walkToSucc : {w : Walk G // w.val.head? = some succ} := ⟨walkToA.val.appendSuccessor succ (by unfold Walk.successors; simp [walkToA.prop]; exact succ.prop), by (unfold Walk.appendSuccessor; simp)⟩
                verify_acyclicity_and_cond_via_dfs_step G cond walkToSucc b
              )
              verifiedNodes

            intro set res succ _ eq

            have _termination := G.verify_acyclicity_and_cond_via_dfs_step_termination_aux walkToA succ.prop (by simp at succ_not_mem_walk; apply succ_not_mem_walk; exact succ.prop)
            apply dfs_step_extends_verified
            exact eq
            exact eq
          · rw [HashSet.subset_iff]
            intro c c_contained
            rw [HashSet.contains_insert]
            apply Or.inl 
            exact c_contained
    termination_by Finset.card (List.toFinset G.vertices \ List.toFinset walkToA.val.val)

    lemma dfs_step_result_valid 
      {a : A} 
      (G : Graph A) 
      (cond : NodeCondition A) 
      (walkToA : {w : Walk G // w.val.head? = some a}) 
      (verifiedNodes : HashSet A) 
      (verifiedAfter : HashSet A) 
      (verifiedAfterIsResult : verify_acyclicity_and_cond_via_dfs_step G cond walkToA verifiedNodes = Except.ok verifiedAfter)
      (verifiedNodesValid : ∀ node, verifiedNodes.contains node -> 
        (¬ G.reachesCycle node ∧ 
          G.cond_ok_on_all_canReach node cond)
          --∀ reachableNode, G.canReach node reachableNode -> cond.true reachableNode)
      ) : (∀ node, verifiedAfter.contains node -> 
        (¬ G.reachesCycle node ∧ 
          G.cond_ok_on_all_canReach node cond)) := by
        --∀ reachableNode, G.canReach node reachableNode -> cond.true reachableNode)) := by 
      unfold verify_acyclicity_and_cond_via_dfs_step at verifiedAfterIsResult
      simp at verifiedAfterIsResult
      split at verifiedAfterIsResult
      · injection verifiedAfterIsResult with verifiedAfterIsResult; rw [← verifiedAfterIsResult]; assumption
      split at verifiedAfterIsResult
      · contradiction
      case h_2 cond_a =>
        split at verifiedAfterIsResult
        · contradiction
        case isFalse succ_not_mem_walk =>
          unfold Except.map at verifiedAfterIsResult
          split at verifiedAfterIsResult
          · contradiction
          case h_2 foldl_result eq =>
            simp at verifiedAfterIsResult

            intro node node_contained
            rw [← verifiedAfterIsResult] at node_contained
            rw [HashSet.contains_insert] at node_contained

            let extendWalkToA (c : A) (c_succ : c ∈ G.successors a) : {w : Walk G // w.val.head? = some c} := ⟨walkToA.val.appendSuccessor c (by unfold Walk.successors; simp [walkToA.prop]; exact c_succ), by (unfold Walk.appendSuccessor; simp)⟩

            let foldl_f : HashSet A -> {c : A // c ∈ G.successors a} -> Except String (HashSet A) := (fun b succ => 
                verify_acyclicity_and_cond_via_dfs_step G cond (extendWalkToA succ.val succ.prop) b
              )

            have foldl_preserves := (G.successors a).attach.foldl_except_preserves_prop foldl_f (Except.ok verifiedNodes)
              (fun set => ∀ node, set.contains node ->(¬ G.reachesCycle node ∧ G.cond_ok_on_all_canReach node cond))

            have prop_holds_after_foldl : ∀ {v}, foldl_result.contains v -> ¬ G.reachesCycle v ∧ G.cond_ok_on_all_canReach v cond := by 
              intro v contains
              apply foldl_preserves
              simp
              intro init_step res_step succ succ_is_succ prop_init_step f_preserves_prop
              have _termination := G.verify_acyclicity_and_cond_via_dfs_step_termination_aux walkToA succ_is_succ (by simp at succ_not_mem_walk; apply succ_not_mem_walk; exact succ_is_succ)
              apply dfs_step_result_valid
              exact f_preserves_prop
              exact prop_init_step
              intro init_unwrapped init_unwrapped_eq
              injection init_unwrapped_eq with init_unwrapped_eq
              rw [← init_unwrapped_eq]
              apply verifiedNodesValid
              exact eq
              exact contains

            cases node_contained with 
            | inl node_contained => apply prop_holds_after_foldl node_contained
            | inr node_contained =>
              rw [← node_contained]
              rw [notReachesCycleIffSuccessorsNotReachCycle]
              rw [cond_ok_on_all_canReach_iff]
              · unfold NodeCondition.true
                simp [cond_a]
                rw [← forall_and]
                intro c
                rw [← imp_and]
                intro c_succ
                apply prop_holds_after_foldl 
                apply (G.successors a).attach.foldl_except_contains_of_some_contains foldl_f verifiedNodes
                · intro set res succ _
                  apply dfs_step_extends_verified
                · exists ⟨c, c_succ⟩ 
                  constructor
                  · simp
                  · intro b res f_ok 
                    apply dfs_step_result_contains_a
                    simp only [foldl_f] at f_ok
                    exact f_ok
                · exact eq
              · apply walkToA.val.prop.left
                apply List.mem_of_mem_head?
                rw [walkToA.prop]
                simp
    termination_by Finset.card (List.toFinset G.vertices \ List.toFinset walkToA.val.val)

    lemma dfs_step_semantics
      {a : A} 
      (G : Graph A) 
      (cond : NodeCondition A) 
      (walkToA : {w : Walk G // w.val.head? = some a}) 
      (verifiedNodes : HashSet A) 
      (verifiedNodesValid : ∀ node, verifiedNodes.contains node -> 
        (¬ G.reachesCycle node ∧ 
          G.cond_ok_on_all_canReach node cond)
      ) : (G.verify_acyclicity_and_cond_via_dfs_step cond walkToA verifiedNodes).isOk ↔ (¬ G.reachesCycle a ∧ G.cond_ok_on_all_canReach a cond) := by 
      constructor
      · intro check_ok
        cases eq : G.verify_acyclicity_and_cond_via_dfs_step cond walkToA verifiedNodes with 
        | error _ => rw [eq] at check_ok; simp [Except.isOk, Except.toBool] at check_ok
        | ok verifiedAfter => 
          apply G.dfs_step_result_valid cond walkToA verifiedNodes verifiedAfter eq verifiedNodesValid 
          apply G.dfs_step_result_contains_a cond walkToA verifiedNodes verifiedAfter eq
      unfold verify_acyclicity_and_cond_via_dfs_step
      simp
      split
      · simp [Except.isOk, Except.toBool]
      split
      case h_1 heq => 
        simp [Except.isOk, Except.toBool]
        intro a_not_cycle cond_a
        rw [cond_ok_on_all_canReach_iff] at cond_a
        unfold NodeCondition.true at cond_a
        rw [cond_a.right] at heq
        contradiction
        apply walkToA.val.prop.left
        apply List.mem_of_mem_head?
        rw [walkToA.prop]
        simp
      case h_2 cond_a =>
        split
        case isTrue h => 
          simp [Except.isOk, Except.toBool]
          intro a_not_cycle _
          apply a_not_cycle
          unfold reachesCycle
          rcases h with ⟨succ, is_succ, in_walk⟩ 
            
          let walkToSucc : {w : Walk G // w.val.head? = some succ} := ⟨walkToA.val.appendSuccessor succ (by unfold Walk.successors; simp [walkToA.prop]; exact is_succ), by (unfold Walk.appendSuccessor; simp)⟩
          have neq : walkToSucc.val.val ≠ [] := by have prop := walkToSucc.prop; intro contra; rw [contra] at prop; simp at prop
          have h : walkToSucc.val.val.head neq ∈ (walkToSucc.val.tail).val := by 
            have prop := walkToSucc.prop
            injection prop
          let cycle : Walk G := ((walkToSucc.val.tail.takeUntil (walkToSucc.val.val.head neq)).appendSuccessor (walkToSucc.val.val.head neq) (by 
            rw [Walk.takeUntil_successors_same]
            apply Walk.head_in_tail_successors
            intro contra; unfold Walk.tail at h; simp [contra] at h
            intro contra; simp [contra] at h))

          exists cycle
          constructor
          · apply walkToSucc.val.isCycle_of_head_in_tail
            exact h
          · exists succ 
            constructor
            · apply List.mem_of_mem_head?
              simp [cycle]
              unfold Walk.appendSuccessor
              simp
            · apply canReach_succ
              exact is_succ
        case isFalse succ_not_mem_walk =>
          unfold Except.map
          split
          case h_1 err heq => 
            simp [Except.isOk, Except.toBool]
            rw [notReachesCycleIffSuccessorsNotReachCycle]
            rw [cond_ok_on_all_canReach_iff]


            unfold NodeCondition.true
            simp [cond_a]
            intro succ_not_reach_cycle

            have foldl_exists := List.foldl_expect_some_error_of_error 
              (G.successors a).attach 
              (fun b succ => 
                let walkToSucc : {w : Walk G // w.val.head? = some succ} := ⟨walkToA.val.appendSuccessor succ (by unfold Walk.successors; simp [walkToA.prop]; exact succ.prop), by (unfold Walk.appendSuccessor; simp)⟩
                verify_acyclicity_and_cond_via_dfs_step G cond walkToSucc b
              )
              verifiedNodes
              err
              heq

            rcases foldl_exists with ⟨i, res, foldl_eq, foldl_cond⟩

            let succ := (G.successors a).attach.get i
    
            exists succ
            constructor
            · simp [succ]; apply List.get_mem
            intro cond_succ
            let walkToSucc : {w : Walk G // w.val.head? = some succ } := ⟨walkToA.val.appendSuccessor succ (by unfold Walk.successors; simp [walkToA.prop]; simp [succ]; apply List.get_mem), by (unfold Walk.appendSuccessor; simp)⟩
            have : (G.verify_acyclicity_and_cond_via_dfs_step cond walkToSucc res).isOk := by
              have _termination := G.verify_acyclicity_and_cond_via_dfs_step_termination_aux walkToA (b := (G.successors a).get ⟨i, by have isLt := i.isLt; simp at isLt; exact isLt⟩) (by apply List.get_mem) (by simp at succ_not_mem_walk; apply succ_not_mem_walk; exact (by apply List.get_mem))
              rw [dfs_step_semantics]
              constructor
              · apply succ_not_reach_cycle; simp [succ]; apply List.get_mem
              · exact cond_succ

              have foldl_preserves := List.foldl_except_preserves_prop 
                ((G.successors a).attach.take i) 
                (fun b succ => 
                  let walkToSucc : {w : Walk G // w.val.head? = some succ} := ⟨walkToA.val.appendSuccessor succ (by unfold Walk.successors; simp [walkToA.prop]; exact succ.prop), by (unfold Walk.appendSuccessor; simp)⟩
                  verify_acyclicity_and_cond_via_dfs_step G cond walkToSucc b
                )
                (Except.ok verifiedNodes)
                (fun set => ∀ node, set.contains node -> (¬ G.reachesCycle node ∧ G.cond_ok_on_all_canReach node cond))
              apply foldl_preserves
              simp
              intro init_step res_step succ succ_is_succ prop_init_step _ eq
              apply dfs_step_result_valid
              exact eq
              exact prop_init_step
              intro init_unwrapped init_unwrapped_eq
              injection init_unwrapped_eq with init_unwrapped_eq
              rw [← init_unwrapped_eq]
              apply verifiedNodesValid
              rw [foldl_eq]
            simp [Except.isOk, Except.toBool] at this
            simp at foldl_cond
            split at this
            case h_1 heq => 
              simp [walkToSucc, succ] at heq; rw [heq] at foldl_cond; simp at foldl_cond
            · contradiction
            · apply walkToA.val.prop.left
              apply List.mem_of_mem_head?
              rw [walkToA.prop]
              simp
          · simp [Except.isOk, Except.toBool]
    termination_by Finset.card (List.toFinset G.vertices \ List.toFinset walkToA.val.val)

    def verify_acyclicity_and_cond_via_dfs (G : Graph A) (cond : NodeCondition A) : Except String Unit := 
      (G.vertices.attach.foldl_except 
        (fun acc ⟨a, h⟩ => G.verify_acyclicity_and_cond_via_dfs_step (a := a) cond ⟨Walk.singleton G a h, by unfold Walk.singleton; simp⟩ acc)
        (Except.ok HashSet.empty)).map (fun _ => ())

    lemma dfs_semantics (G : Graph A) (cond : NodeCondition A) : G.verify_acyclicity_and_cond_via_dfs cond = Except.ok () ↔ G.isAcyclic ∧ ∀ a ∈ G.vertices, cond.true a := by 
      let f := 
        (fun b (node : {a : A // a ∈ G.vertices}) => 
          let walkToSucc : {w : Walk G // w.val.head? = some node} := ⟨Walk.singleton G node node.prop, by unfold Walk.singleton; simp⟩
          verify_acyclicity_and_cond_via_dfs_step G cond walkToSucc b
        )

      unfold verify_acyclicity_and_cond_via_dfs
      unfold Except.map
      rw [acyclicIffAllNotReachCycle]
      simp
      split
      case h_1 err heq => 
        have foldl_exists := List.foldl_expect_some_error_of_error 
          G.vertices.attach 
          f
          HashSet.empty
          err
          heq
        rcases foldl_exists with ⟨i, res, foldl_eq, foldl_cond⟩
        have step_not_ok : ¬ (f res (G.vertices.attach.get i)).isOk := by rw [foldl_cond]; simp [Except.isOk, Except.toBool]
        simp only [f] at step_not_ok
        rw [dfs_step_semantics] at step_not_ok
        simp at step_not_ok
        rw [cond_ok_on_all_iff_ok_on_all_canReach]
        simp
        intro none_reach_cyc
        specialize none_reach_cyc (G.vertices.attach.get i)
        simp at none_reach_cyc
        specialize step_not_ok none_reach_cyc
        exists G.vertices.attach.get i
        simp
        exact step_not_ok

        have foldl_preserves := List.foldl_except_preserves_prop 
          (G.vertices.attach.take i) 
          f
          (Except.ok HashSet.empty)
          (fun set => ∀ node, set.contains node -> (¬ G.reachesCycle node ∧ G.cond_ok_on_all_canReach node cond))
        apply foldl_preserves
        simp
        intro init_step res_step succ succ_is_succ prop_init_step _ eq
        apply dfs_step_result_valid
        exact eq
        exact prop_init_step
        intro init_unwrapped init_unwrapped_eq
        injection init_unwrapped_eq with init_unwrapped_eq
        rw [← init_unwrapped_eq]
        intro node empty_contains_node; apply False.elim; apply HashSet.empty_contains node; exact empty_contains_node 
        rw [foldl_eq]
      case h_2 heq => 
        simp
        rw [cond_ok_on_all_iff_ok_on_all_canReach]
        rw [← forall_and]
        intro a
        cases Decidable.em (a ∈ G.vertices) with 
        | inr a_not_in_G => 
          constructor
          · unfold reachesCycle
            intro contra
            rcases contra with ⟨_, _, _, _, reach⟩
            unfold canReach at reach
            rcases reach with ⟨w, _, _, _, last⟩
            apply a_not_in_G
            apply w.prop.left
            rw [List.getLast_eq_get]
            apply List.get_mem
          · unfold cond_ok_on_all_canReach
            intro b h
            rw [canReach_iff] at h
            cases h with 
            | inl h => have left := h.left; contradiction
            | inr h => 
              apply False.elim 
              apply a_not_in_G
              rcases h with ⟨b, elem, _⟩
              apply mem_of_has_succ
              apply elem
        | inl a_in_G => 
          let i : Fin G.vertices.length := ⟨G.vertices.indexOf a, by rw [List.indexOf_lt_length]; apply a_in_G⟩ 
          let a' := G.vertices.attach.get ⟨i, by rw [List.length_attach]; exact i.isLt⟩
          have : a = a' := by simp [a', i]

          have foldl_ok := List.foldl_except_all_ok_of_ok 
            G.vertices.attach 
            f
            HashSet.empty

          rw [heq] at foldl_ok
          simp [Except.isOk, Except.toBool] at foldl_ok

          specialize foldl_ok ⟨i, by rw [List.length_attach]; exact i.isLt⟩ 
          rcases foldl_ok with ⟨res, take_ok, f_ok⟩ 

          let walkToA : {w : Walk G // w.val.head? = some a'} := ⟨Walk.singleton G a' a'.prop, by unfold Walk.singleton; simp⟩
          rw [this]
          rw [← G.dfs_step_semantics cond walkToA res]
          
          split at f_ok
          case h_1 heq => simp [f] at heq; simp [walkToA]; simp [← this]; rw [heq]; simp [Except.isOk, Except.toBool]
          · contradiction

          have foldl_preserves := List.foldl_except_preserves_prop 
            (G.vertices.attach.take i) 
            f
            (Except.ok HashSet.empty)
            (fun set => ∀ node, set.contains node -> (¬ G.reachesCycle node ∧ G.cond_ok_on_all_canReach node cond))
          apply foldl_preserves
          simp
          intro init_step res_step succ succ_is_succ prop_init_step _ eq
          apply dfs_step_result_valid
          exact eq
          exact prop_init_step
          intro init_unwrapped init_unwrapped_eq
          injection init_unwrapped_eq with init_unwrapped_eq
          rw [← init_unwrapped_eq]
          intro node empty_contains_node; apply False.elim; apply HashSet.empty_contains node; exact empty_contains_node 
          rw [take_ok]
  end Graph
end Dfs
