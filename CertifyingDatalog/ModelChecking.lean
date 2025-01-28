import CertifyingDatalog.Datalog
import CertifyingDatalog.Unification
import Mathlib.Data.Set.Basic
import CertifyingDatalog.Basic

structure PartialGroundRule (τ: Signature) where
  head: Atom τ
  groundedBody: List (GroundAtom τ)
  ungroundedBody: List (Atom τ)

abbrev CheckableModel (τ: Signature) := List (GroundAtom τ)

variable {τ: Signature}

namespace PartialGroundRule
  def isSafe [DecidableEq τ.vars] (pgr: PartialGroundRule τ): Prop :=
    pgr.head.vars ⊆ pgr.ungroundedBody.foldl_union Atom.vars ∅

  def isGround (pgr: PartialGroundRule τ): Prop :=
    pgr.ungroundedBody = []

  def fromRule (r: Rule τ) : PartialGroundRule τ :=
    {head := r.head, groundedBody := [], ungroundedBody := r.body}

  def toRule (pgr: PartialGroundRule τ) : Rule τ :=
    {head:= pgr.head, body := (pgr.groundedBody.map GroundAtom.toAtom) ++ pgr.ungroundedBody}

  lemma toRule_inv_fromRule {r: Rule τ}: (fromRule r).toRule = r := by
    unfold fromRule
    unfold toRule
    simp

  def isActive (pgr: PartialGroundRule τ) (i: Interpretation τ) : Prop := ∀ (ga: GroundAtom τ), ga ∈ pgr.groundedBody → ga ∈ i

  lemma fromRule_isActive {r: Rule τ} (i: Interpretation τ) : (fromRule r).isActive i := by
    unfold isActive
    unfold fromRule
    simp

  lemma fromRule_safe_iff_rule_safe [DecidableEq τ.vars] {r : Rule τ} : (fromRule r).isSafe ↔ r.isSafe := by
    unfold isSafe
    unfold Rule.isSafe
    unfold fromRule
    simp

  def isSatisfied [DecidableEq τ.constants] [DecidableEq τ.vars] [DecidableEq τ.relationSymbols] (pgr : PartialGroundRule τ) (i : Interpretation τ) : Prop := ∀ (g : Grounding τ), i.satisfiesRule (g.applyRule' pgr.toRule)

  lemma satisfied_iff_of_eq_toRule [DecidableEq τ.constants] [DecidableEq τ.vars] [DecidableEq τ.relationSymbols]
      (pgr1 pgr2: PartialGroundRule τ) (i: Interpretation τ) (h: pgr1.toRule = pgr2.toRule): pgr1.isSatisfied i ↔ pgr2.isSatisfied i := by
    unfold isSatisfied
    simp only [h]

  lemma head_noVars_of_safe_of_ground [DecidableEq τ.vars] (pgr : PartialGroundRule τ) : pgr.isSafe -> pgr.isGround -> pgr.head.vars = ∅ := by
    unfold isSafe
    unfold isGround
    intro safe ground
    rw [ground] at safe
    unfold List.foldl_union at safe
    simp only [List.foldl_nil, Finset.subset_empty] at safe
    apply Finset.Subset.antisymm
    · rw [safe]
    · simp

end PartialGroundRule

namespace Grounding
  def applyPartialGroundRule (g : Grounding τ) (pgr : PartialGroundRule τ) : GroundRule τ := g.applyRule' pgr.toRule

  lemma applyPartialGroundRule_eq_apply_only_ungrounded {g : Grounding τ} {pgr : PartialGroundRule τ} :
    g.applyPartialGroundRule pgr = { head := g.applyAtom' pgr.head, body := pgr.groundedBody ++ pgr.ungroundedBody.map g.applyAtom'} := by
    unfold applyPartialGroundRule
    unfold applyRule'
    simp only [PartialGroundRule.toRule, List.map_append, List.map_map, GroundRule.mk.injEq,
      List.append_cancel_right_eq, true_and]
    apply List.ext_getElem
    · rw [List.length_map]
    · intro _ _ _
      simp only [List.getElem_map, Function.comp_apply]
      rw [applyAtom'_on_GroundAtom_unchanged]
end Grounding

namespace PartialGroundRule
  variable [DecidableEq τ.constants] [DecidableEq τ.vars] [DecidableEq τ.relationSymbols]

  lemma satisfied_of_not_active {pgr: PartialGroundRule τ} {i: Interpretation τ} : ¬ pgr.isActive i -> pgr.isSatisfied i := by
    intro notActive
    unfold isSatisfied
    intro g
    unfold Interpretation.satisfiesRule
    intro h
    unfold isActive at notActive
    simp only [not_forall, Classical.not_imp] at notActive
    have apply_eq := @ g.applyPartialGroundRule_eq_apply_only_ungrounded τ pgr
    unfold Grounding.applyPartialGroundRule at apply_eq
    rw [apply_eq] at h
    unfold GroundRule.bodySet at h
    simp only [List.toFinset_append, Finset.coe_union, List.coe_toFinset, List.mem_map,
      Set.union_subset_iff] at h
    rcases notActive with ⟨a, a_mem_body, a_not_mem_i⟩
    apply False.elim
    apply a_not_mem_i
    apply h.left
    simp only [Set.mem_setOf_eq]
    exact a_mem_body
end PartialGroundRule

namespace CheckableModel
  variable [DecidableEq τ.constants] [DecidableEq τ.vars] [DecidableEq τ.relationSymbols]

  def substitutionsForAtom (m : CheckableModel τ) (a : Atom τ) : List (Substitution τ) := m.filterMap (fun ga => Substitution.empty.matchAtom a ga)

  lemma noVars_after_applying_substitutionsForAtom {m : CheckableModel τ} {a : Atom τ} : ∀ s ∈ m.substitutionsForAtom a, (s.applyAtom a).vars = ∅ := by
    unfold substitutionsForAtom
    intro s s_mem
    simp only [List.mem_filterMap] at s_mem
    rcases s_mem with ⟨ga, _, ga_eq⟩
    have : s = (Substitution.empty.matchAtom a ga).get (by simp [ga_eq]) := by simp [ga_eq]
    rw [this]
    rw [Substitution.matchAtomYieldsSubs]
    exact ga.vars_empty

  lemma substitutionsForAtom_application_in_model {m : CheckableModel τ} {a : Atom τ} : ∀ (h : s ∈ m.substitutionsForAtom a), (s.applyAtom a).toGroundAtom (m.noVars_after_applying_substitutionsForAtom s h) ∈ m := by
    intro h
    unfold substitutionsForAtom at h
    simp only [List.mem_filterMap] at h
    rcases h with ⟨ga, ga_mem, ga_eq⟩
    have : s = (Substitution.empty.matchAtom a ga).get (by simp [ga_eq]) := by simp [ga_eq]
    simp only [this]
    simp only [Substitution.matchAtomYieldsSubs]
    have : ga = ga.toAtom.toGroundAtom ga.vars_empty := by rw [GroundAtom.eq_iff_toAtom_eq]; rw [← ga.toAtom.toGroundAtom_isSelf]
    rw [← this]
    exact ga_mem

  lemma mem_substitutionsForAtom_iff {m : CheckableModel τ} {a : Atom τ} :
    ∀ (s : Substitution τ), s ∈ m.substitutionsForAtom a ↔ ∃ ga ∈ m, s.applyAtom a = ga ∧ ∀ (s': Substitution τ), s'.applyAtom a = ga → s ⊆ s' := by
    intro s
    constructor
    · intro h
      exists (s.applyAtom a).toGroundAtom (m.noVars_after_applying_substitutionsForAtom s h)
      constructor
      · apply substitutionsForAtom_application_in_model; exact h
      · rw [← Atom.toGroundAtom_isSelf]
        simp
        intro s' eq

        unfold substitutionsForAtom at h
        simp only [List.mem_filterMap] at h
        rcases h with ⟨ga, _, ga_eq⟩
        have : s = (Substitution.empty.matchAtom a ga).get (by simp [ga_eq]) := by simp [ga_eq]

        rw [this]
        apply Substitution.matchAtomIsMinimal
        constructor
        · apply Substitution.empty_isMinimal
        · rw [eq, this]; rw [Substitution.matchAtomYieldsSubs]
    · intro h
      rcases h with ⟨ga, mem, ga_eq, minimal⟩
      unfold substitutionsForAtom
      simp only [List.mem_filterMap]
      exists ga
      constructor
      · exact mem
      · cases eq : Substitution.empty.matchAtom a ga with
        | none =>
          simp
          apply @Substitution.matchAtomNoneThenNoSubs τ
          rw [eq]
          apply Substitution.empty_isMinimal
          apply ga_eq
        | some s' =>
          simp
          have : s' = (Substitution.empty.matchAtom a ga).get (by simp [eq]) := by simp [eq]
          apply Substitution.subset_antisymm
          · rw [this]
            apply Substitution.matchAtomIsMinimal
            constructor
            · apply Substitution.empty_isMinimal
            · exact ga_eq
          · apply minimal
            rw [this]
            apply Substitution.matchAtomYieldsSubs

  variable [ToString τ.constants] [ToString τ.vars] [ToString τ.relationSymbols]

  def checkPGR (m : CheckableModel τ) (pgr : PartialGroundRule τ) (safe : pgr.isSafe) : Except String Unit :=
    match eq : pgr.ungroundedBody with
    | .nil => if pgr.head.toGroundAtom (pgr.head_noVars_of_safe_of_ground safe eq) ∈ m
      then Except.ok ()
      else Except.error ("Unsatisfied rule: " ++ ToString.toString pgr.toRule)
    | .cons hd tl =>
      (m.substitutionsForAtom hd).attach.mapExceptUnit (fun ⟨s, s_mem⟩ =>
        let adjustedRule : PartialGroundRule τ := {
          head := s.applyAtom pgr.head
          groundedBody := pgr.groundedBody ++ [(s.applyAtom hd).toGroundAtom (by apply m.noVars_after_applying_substitutionsForAtom; exact s_mem)]
          ungroundedBody := tl.map s.applyAtom
        }

        have _termination : tl.length < pgr.ungroundedBody.length := by rw [eq]; simp
        m.checkPGR adjustedRule (by
          unfold PartialGroundRule.isSafe
          intro v v_in_adj_head
          rw [Substitution.applyAtom_remainingVarsNotInDomain] at v_in_adj_head
          rw [Finset.mem_filter_nc] at v_in_adj_head

          have : v ∈ pgr.ungroundedBody.foldl_union Atom.vars ∅ := by
            unfold PartialGroundRule.isSafe at safe
            apply safe
            exact v_in_adj_head.right

          rw [eq] at this
          simp only [List.foldl_union, List.foldl_cons, Finset.empty_union] at this
          have mem_foldl_union := @List.mem_foldl_union (Atom τ) τ.vars
          simp only [List.foldl_union] at mem_foldl_union
          rw [mem_foldl_union] at this
          cases this with
          | inl v_in_hd =>
            have noVars_in_hd := m.noVars_after_applying_substitutionsForAtom s s_mem
            have v_in_applied_hd : v ∈ (s.applyAtom hd).vars := by
              rw [Substitution.applyAtom_remainingVarsNotInDomain]
              rw [Finset.mem_filter_nc]
              constructor
              · exact v_in_adj_head.left
              · exact v_in_hd
            rw [noVars_in_hd] at v_in_applied_hd
            contradiction
          | inr v_in_tl =>
            rw [List.mem_foldl_union]
            apply Or.inr
            rcases v_in_tl with ⟨a, a_mem, v_in_a⟩
            exists s.applyAtom a
            constructor
            · simp only [adjustedRule, List.mem_map]
              exists a
            · rw [Substitution.applyAtom_remainingVarsNotInDomain]
              rw [Finset.mem_filter_nc]
              constructor
              · exact v_in_adj_head.left
              · exact v_in_a
        )
      )
  termination_by pgr.ungroundedBody.length

  lemma checkPGRIsOkIffRuleIsSatisfied [Inhabited τ.constants] {m : CheckableModel τ} {pgr : PartialGroundRule τ} (safe : pgr.isSafe) (active : pgr.isActive m.toSet) : m.checkPGR pgr safe = Except.ok () ↔ pgr.isSatisfied m.toSet := by
    unfold checkPGR
    split
    · case h_1 heq =>
        have : ∀ g : Grounding τ, g.applyAtom' pgr.head = pgr.head.toGroundAtom (pgr.head_noVars_of_safe_of_ground safe heq) := by
          intro g
          rw [GroundAtom.eq_iff_toAtom_eq]
          rw [g.applyAtom'_on_Atom_without_vars_unchanged (pgr.head_noVars_of_safe_of_ground safe heq)]
          rw [← Atom.toGroundAtom_isSelf]
        split
        case isTrue h =>
          simp
          unfold PartialGroundRule.isSatisfied
          unfold Interpretation.satisfiesRule
          intro g _
          unfold Grounding.applyRule'
          unfold PartialGroundRule.toRule
          simp only
          rw [this]
          unfold List.toSet
          simp only [List.coe_toFinset, Set.mem_setOf_eq]
          exact h
        case isFalse h =>
          simp
          unfold PartialGroundRule.isSatisfied
          unfold Interpretation.satisfiesRule
          unfold Grounding.applyRule'
          unfold PartialGroundRule.toRule
          rw [heq]
          simp only [List.append_nil, List.map_map, not_forall, Classical.not_imp]
          let g : Grounding τ := (fun _ => Inhabited.default (α := τ.constants))
          exists g
          unfold GroundRule.bodySet
          simp only [List.coe_toFinset, List.mem_map, Function.comp_apply]
          constructor
          · rw[this]
            unfold List.toSet
            simp only [List.coe_toFinset, Set.mem_setOf_eq]
            exact h
          · unfold PartialGroundRule.isActive at active
            intro a a_mem
            simp only [Set.mem_setOf_eq] at a_mem
            apply active
            rcases a_mem with ⟨a', a'_mem, a'_eq⟩
            rw [g.applyAtom'_on_GroundAtom_unchanged] at a'_eq
            rw [a'_eq] at a'_mem
            exact a'_mem
    · case h_2 hd tl heq =>
        rw [List.mapExceptUnit_iff]
        simp
        unfold PartialGroundRule.isSatisfied
        unfold Interpretation.satisfiesRule

        constructor
        · intro subs_works
          unfold Grounding.applyRule'
          unfold PartialGroundRule.toRule
          unfold GroundRule.bodySet
          simp only [List.map_append, List.map_map, List.toFinset_append, Finset.coe_union,
            List.coe_toFinset, List.mem_map, Function.comp_apply, Set.union_subset_iff, and_imp]
          intro g g_active_grounded g_active_ungrounded
          unfold List.toSet at g_active_grounded
          simp only [List.coe_toFinset, Set.setOf_subset_setOf, forall_exists_index, and_imp,
            forall_apply_eq_imp_iff₂] at g_active_grounded
          rw [heq] at g_active_ungrounded
          unfold List.toSet at g_active_ungrounded
          simp only [List.mem_cons, exists_eq_or_imp, List.coe_toFinset,
            Set.setOf_subset_setOf] at g_active_ungrounded

          let subs : Substitution τ := (fun v => if v ∈ hd.vars then g v else Option.none)

          have g_after_subs : ∀ a, g.applyAtom' (subs.applyAtom a) = g.applyAtom' a := by
            intro a
            unfold Substitution.applyAtom
            unfold Grounding.applyAtom'
            simp only [List.map_map, GroundAtom.mk.injEq, List.map_inj_left, Function.comp_apply,
              true_and]
            intro t t_mem
            unfold Substitution.applyTerm
            unfold Grounding.applyTerm'
            cases t with
            | constant c => simp
            | variableDL v =>
              simp only [subs]
              cases Decidable.em (v ∈ hd.vars) with
              | inl h => simp [h]
              | inr h => simp [h]

          have g_eq_subs_on_hd : subs.applyAtom hd = g.applyAtom' hd := by
            unfold Substitution.applyAtom
            unfold Grounding.applyAtom'
            unfold GroundAtom.toAtom
            simp only [List.map_map, Atom.mk.injEq, List.map_inj_left, Function.comp_apply,
              true_and, subs]
            intro t t_mem
            unfold Substitution.applyTerm
            unfold Grounding.applyTerm'
            cases t with
            | constant c => simp
            | variableDL v =>
              have : v ∈ hd.vars := by
                unfold Atom.vars
                rw [List.mem_foldl_union]
                apply Or.inr
                exists Term.variableDL v
                unfold Term.vars
                constructor
                · exact t_mem
                · simp only [Finset.mem_singleton, subs]
              simp [subs, this]

          have subs_domain : subs.domain = hd.vars := by
            unfold Substitution.domain
            apply Set.ext
            intro v
            simp only [Option.isSome_ite, Finset.setOf_mem, Finset.mem_coe, subs]

          specialize subs_works subs (by
            rw [mem_substitutionsForAtom_iff]
            exists g.applyAtom' hd
            constructor
            · apply g_active_ungrounded; apply Or.inl; rfl
            constructor
            · exact g_eq_subs_on_hd
            · intro s' s'_apply_also_ground
              rw [← g_eq_subs_on_hd] at s'_apply_also_ground
              intro v v_in_dom
              rw [subs_domain] at v_in_dom
              simp only [Finset.mem_coe, subs] at v_in_dom
              unfold Substitution.applyAtom at s'_apply_also_ground
              simp only [Atom.mk.injEq, List.map_inj_left, true_and, subs] at s'_apply_also_ground
              specialize s'_apply_also_ground (Term.variableDL v) (by
                unfold Atom.vars at v_in_dom
                rw [List.mem_foldl_union] at v_in_dom
                cases v_in_dom; contradiction;
                case inr h =>
                rcases h with ⟨t, t_mem, v_in_t⟩
                unfold Term.vars at v_in_t
                cases t <;> simp at v_in_t
                rw [v_in_t]
                exact t_mem
              )
              unfold Substitution.applyTerm at s'_apply_also_ground
              simp only [v_in_dom, ↓reduceIte, subs] at s'_apply_also_ground
              simp only [v_in_dom, ↓reduceIte, subs]
              cases eq : s' v with
              | none => simp [eq] at s'_apply_also_ground
              | some c =>
                simp only [eq, Term.constant.injEq, subs] at s'_apply_also_ground
                rw [s'_apply_also_ground]
          )
          have _termination : tl.length < pgr.ungroundedBody.length := by rw [heq]; simp
          rw [m.checkPGRIsOkIffRuleIsSatisfied _ (by
            unfold PartialGroundRule.isActive
            unfold List.toSet
            simp
            intro ga ga_eq
            cases ga_eq with
            | inl ga_eq =>
              specialize g_active_grounded ga
              rw [Grounding.applyAtom'_on_GroundAtom_unchanged] at g_active_grounded
              apply g_active_grounded
              exact ga_eq
            | inr ga_eq =>
              apply g_active_ungrounded
              apply Or.inl
              rw [ga_eq]
              rw [GroundAtom.eq_iff_toAtom_eq]
              rw [← Atom.toGroundAtom_isSelf]
              rw [g_eq_subs_on_hd]
          )] at subs_works
          unfold PartialGroundRule.isSatisfied at subs_works
          unfold Interpretation.satisfiesRule at subs_works
          unfold PartialGroundRule.toRule at subs_works
          unfold GroundRule.bodySet at subs_works
          unfold Grounding.applyRule' at subs_works
          simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
            List.singleton_append, List.map_map, List.toFinset_append, List.toFinset_cons,
            Finset.union_insert, Finset.coe_insert, Finset.coe_union, List.coe_toFinset,
            List.mem_map, Function.comp_apply, subs] at subs_works
          specialize subs_works g
          rw [g_after_subs] at subs_works
          apply subs_works
          unfold List.toSet
          rw [Set.subset_def]
          simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_setOf_eq, List.coe_toFinset,
            forall_eq_or_imp, subs]
          constructor
          · rw [← (subs.applyAtom hd).toGroundAtom_isSelf]; rw [g_after_subs]; apply g_active_ungrounded; apply Or.inl; rfl
          · intro a h
            cases h with
            | inl h =>
              rcases h with ⟨b, h⟩
              rw [← h.right]
              apply g_active_grounded
              exact h.left
            | inr h =>
              rcases h with ⟨b, h⟩
              rw [← h.right]
              apply g_active_ungrounded
              apply Or.inr
              exists b
              rw [g_after_subs]
              simp only [and_true, subs]
              exact h.left
        · intro grounding_works
          intro subs subs_mem
          have _termination : tl.length < pgr.ungroundedBody.length := by rw [heq]; simp
          rw [m.checkPGRIsOkIffRuleIsSatisfied _ (by
            unfold PartialGroundRule.isActive
            unfold List.toSet
            simp only [List.mem_append, List.mem_singleton, List.coe_toFinset, Set.mem_setOf_eq]
            intro ga h
            cases h with
            | inl h =>
              unfold PartialGroundRule.isActive at active
              unfold List.toSet at active
              simp only [List.coe_toFinset, Set.mem_setOf_eq] at active
              apply active
              exact h
            | inr h =>
              rw [h]
              apply substitutionsForAtom_application_in_model
              exact subs_mem
          )]
          unfold PartialGroundRule.isSatisfied
          unfold Interpretation.satisfiesRule
          unfold Grounding.applyRule'
          unfold PartialGroundRule.toRule
          unfold List.toSet
          unfold GroundRule.bodySet
          simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
            List.singleton_append, List.map_map, List.toFinset_append, List.toFinset_cons,
            Finset.union_insert, Finset.coe_insert, Finset.coe_union, List.coe_toFinset,
            List.mem_map, Function.comp_apply, Set.mem_setOf_eq]
          intro g h
          rw [Set.subset_def] at h
          simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_setOf_eq, forall_eq_or_imp] at h
          unfold List.toSet at grounding_works
          unfold PartialGroundRule.toRule at grounding_works
          unfold Grounding.applyRule' at grounding_works
          unfold GroundRule.bodySet at grounding_works
          simp only [List.map_append, List.map_map, List.toFinset_append, Finset.coe_union,
            List.coe_toFinset, List.mem_map, Function.comp_apply, Set.union_subset_iff,
            Set.setOf_subset_setOf, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
            Set.mem_setOf_eq] at grounding_works

          let grounding : Grounding τ := fun v => (subs v).getD (g v)

          have : ∀ a, grounding.applyAtom' a = g.applyAtom' (subs.applyAtom a) := by
            intro a
            simp only [grounding]
            unfold Grounding.applyAtom'
            unfold Substitution.applyAtom
            simp only [List.map_map, GroundAtom.mk.injEq, List.map_inj_left, Function.comp_apply,
              true_and, grounding]
            intro t t_mem
            unfold Substitution.applyTerm
            unfold Grounding.applyTerm'
            cases t with
            | constant _ => simp
            | variableDL v => simp; cases subs v <;> simp

          specialize grounding_works grounding
          rw [this] at grounding_works
          apply grounding_works
          · intro ga ga_mem
            rw [Grounding.applyAtom'_on_GroundAtom_unchanged]
            apply h.right
            apply Or.inl
            exists ga
            rw [Grounding.applyAtom'_on_GroundAtom_unchanged]
            simp only [and_true, grounding]
            exact ga_mem
          · rw [heq]
            rw [← Atom.toGroundAtom_isSelf] at h
            simp only [List.mem_cons, forall_eq_or_imp]
            constructor
            · rw [this]; exact h.left
            · intro a a_mem
              apply h.right
              apply Or.inr
              exists a
              rw [this]
              simp only [and_true]
              exact a_mem
  termination_by pgr.ungroundedBody.length

  def checkProgram (m : CheckableModel τ) (p : Program τ) (safe : p.isSafe) : Except String Unit :=
    p.attach.mapExceptUnit (fun ⟨r, r_mem⟩ => m.checkPGR (PartialGroundRule.fromRule r) (by
      rw [PartialGroundRule.fromRule_safe_iff_rule_safe]
      unfold Program.isSafe at safe
      apply safe
      exact r_mem
    ))

  theorem checkProgramIsOkIffAllRulesAreSatisfied [Inhabited τ.constants] {m : CheckableModel τ} {p : Program τ} (safe : p.isSafe) :
    m.checkProgram p safe = Except.ok () ↔ ∀ r ∈ p.groundProgram, Interpretation.satisfiesRule m.toSet r := by
      unfold checkProgram
      rw [List.mapExceptUnit_iff]
      unfold Program.groundProgram
      simp only [List.mem_attach, forall_const, Subtype.forall, exists_and_left, Set.mem_setOf_eq,
        forall_exists_index, and_imp]
      constructor
      · intro h gr r r_mem g eq
        specialize h r r_mem
        rw [m.checkPGRIsOkIffRuleIsSatisfied _ (by apply PartialGroundRule.fromRule_isActive)] at h
        unfold PartialGroundRule.isSatisfied at h
        rw [PartialGroundRule.toRule_inv_fromRule] at h
        rw [eq]
        apply h
      · intro h r r_mem
        rw [m.checkPGRIsOkIffRuleIsSatisfied _ (by apply PartialGroundRule.fromRule_isActive)]
        unfold PartialGroundRule.isSatisfied
        rw [PartialGroundRule.toRule_inv_fromRule]
        intro g
        apply h
        exact r_mem
        rfl
end CheckableModel
