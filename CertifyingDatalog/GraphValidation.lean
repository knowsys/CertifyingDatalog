import CertifyingDatalog.Basic
import CertifyingDatalog.Datalog
import CertifyingDatalog.TreeValidation
import Mathlib.Data.List.Card
import Mathlib.Data.Finset.Card


structure Graph (A: Type) where
  (vertices: List A)
  (predecessors: A → List A)
  (complete: ∀ (a:A), a ∈ vertices →  ∀ (a':A), a' ∈ predecessors a → a' ∈ vertices)

variable {A: Type}[DecidableEq A]

def isPath (l: List A) (G: Graph A): Prop :=
  match l with
  | [] => True
  | hd::tl =>
    match tl with
    | [] => hd ∈ G.vertices
    | hd'::tl' =>
      hd ∈ G.vertices ∧ hd ∈ (G.predecessors hd') ∧ isPath (hd'::tl') G

lemma singletonPath (a:A) (G: Graph A) (mem: a ∈ G.vertices): isPath [a] G :=
by
  unfold isPath
  simp
  apply mem

def List.getFirst (l: List A) (nonempty: l ≠ []): A :=
  match l with
  | [] => have f: False := by
            simp at nonempty
    False.elim f
  | hd::_ => hd

def List.getLast' (l: List A) (nonempty: l ≠ []): A :=
  match l with
  | [] => have f: False := by
            simp at nonempty
    False.elim f
  | hd::tl =>
    if h:tl = []
    then hd
    else List.getLast' tl h

def isCircle (l: List A) (G: Graph A): Prop :=
  if h:List.length l < 2
  then False
  else
    have l_nonempty: l ≠ [] :=
    by
      cases l with
      | nil =>
        simp at h
      | cons hd tl =>
        simp

    isPath l G ∧ List.getLast' l l_nonempty = List.getFirst l l_nonempty


def isAcyclic (G: Graph A) := ∀ (l: List A), ¬ isCircle l G

lemma isPath_of_cons {a: A} {l:List A} {G:Graph A} (path: isPath (a::l) G): isPath l G :=
by
  unfold isPath at path
  cases l with
  | nil =>
    unfold isPath
    apply True.intro
  | cons hd tl =>
    simp at path
    simp [path]


lemma removeFrontOfLtMin (a b c: ℕ) (hab: b ≤ a) (hac: c ≤ a) : a - b < a -c ↔ b > c :=
by
  induction a with
  | zero =>
    simp at *
    rw [hab, hac]
  | succ n ih =>
    cases hab with
    | refl =>
      cases hac with
      | refl =>
        simp
      | step hc =>
        simp
    | step hb =>
      cases hac with
      | refl =>
        simp
        apply Nat.le_succ_of_le hb
      | step hc =>
        specialize ih hb hc
        rw [← ih]
        rw [Nat.succ_sub hb, Nat.succ_sub hc]
        rw [Nat.succ_lt_succ_iff]


lemma isPath_front_member_graph{a: A} {l: List A} {G: Graph A} (path: isPath (a::l) G): a ∈ G.vertices :=
by
  cases l with
  | nil =>
    unfold isPath at path
    simp at path
    apply path
  | cons hd tl =>
    unfold isPath at path
    simp at path
    simp [path]

lemma isPath_member_graph {a: A} {l: List A} {G: Graph A} (path: isPath l G) (mem: a ∈ l): a ∈ G.vertices :=
by
  induction l with
  | nil =>
    simp at mem
  | cons hd tl ih =>
    simp at mem
    cases mem with
    | inl a_hd =>
      rw [← a_hd] at path
      apply isPath_front_member_graph path
    | inr a_tl =>
      apply ih
      apply isPath_of_cons path
      apply a_tl

lemma isPath_extends_predecessors {a: A} {l: List A} {G: Graph A} (path: isPath (a::l) G): ∀ (b:A), b ∈ (G.predecessors a) → isPath (b::a::l) G :=
by
  intro b b_mem
  unfold isPath
  simp
  constructor
  apply G.complete a
  apply isPath_front_member_graph path
  apply b_mem
  constructor
  apply b_mem
  apply path


lemma isPathImplSubset {l: List A} {G: Graph A} (path: isPath l G ): l.toFinset ⊆ G.vertices.toFinset :=
by
  rw [Finset.subset_iff]
  induction l with
  | nil =>
    simp
  | cons hd tl ih =>
    intro x x_mem
    simp at x_mem
    cases x_mem with
    | inl x_hd =>
      unfold isPath at path
      cases tl with
      | nil =>
        simp at *
        rw [x_hd]
        apply path
      | cons hd' tl' =>
        simp at path
        rw [List.mem_toFinset]
        simp [x_hd,path]
    | inr x_tl =>
      apply ih
      apply isPath_of_cons path
      simp [x_tl]


def extractTreeStep (a:A) (G:Graph A) (visited: List A) (path: isPath (a::visited) G): tree A :=
  if h: a ∈ visited
  then tree.node a []
  else
  tree.node a (List.map (fun ⟨x, _h⟩ => extractTreeStep x G (a::visited) (isPath_extends_predecessors path x _h)) (G.predecessors a).attach)
termination_by extractTreeStep a G visited path => ((List.toFinset G.vertices).card - (List.toFinset visited).card)
decreasing_by
  simp_wf
  rw [← List.mem_toFinset] at h
  rw [removeFrontOfLtMin]
  simp
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff]
  use a
  apply Finset.card_le_of_subset
  rw [Finset.subset_iff]
  intro x
  simp
  intro p
  rw [← List.mem_toFinset]
  apply isPathImplSubset path
  simp
  apply p

  apply Finset.card_le_of_subset
  apply isPathImplSubset
  apply isPath_of_cons path

lemma extractTreeStepHeight (a ga:A) (G:Graph A) (visited: List A) (path: isPath (a::visited) G) (neighbor: ga ∈ G.predecessors a) (a_vis: ¬ a ∈ visited): height (extractTreeStep a G visited path) > height (extractTreeStep ga G (a::visited) (isPath_extends_predecessors path ga neighbor)) :=
by
  simp
  apply heightOfMemberIsSmaller
  -- to avoid unnecessary unfolding
  generalize h:(extractTreeStep ga G (a :: visited) (_ : isPath (ga :: a :: visited) G)) = t
  unfold extractTreeStep
  simp [a_vis]
  unfold member
  simp
  use ga
  use neighbor

lemma rootOfExtractTreeStep (a:A) (G:Graph A) (visited: List A) (path: isPath (a::visited) G): root (extractTreeStep a G visited path) = a :=
by
  unfold extractTreeStep
  unfold root
  by_cases a_visited: a ∈ visited
  simp [a_visited]
  simp [a_visited]

def getSubListToMember (l: List A) (a: A) (mem: a ∈ l): List A :=
  match l with
  | [] =>
    have h: False :=
    by
      simp at mem

    False.elim h
  | hd::tl =>
    if p: a = hd
    then [hd]
    else
      have mem': a ∈ tl :=
      by
        simp[p] at mem
        apply mem
      hd::getSubListToMember tl a mem'

lemma getSubListToMemberPreservesFront (hd a hd': A) (tl tl': List A) (mem: a ∈ hd'::tl') (result: getSubListToMember (hd'::tl') a mem = hd::tl): hd' = hd :=
by
  unfold getSubListToMember at result
  by_cases a_hd: a = hd'
  all_goals{
  simp [a_hd] at result
  simp [result]
  }



lemma getSubListToMemberPreservesPath (l: List A) (a:A) (mem: a ∈ l) (G: Graph A) (path: isPath l G): isPath (getSubListToMember l a mem) G :=
by
  induction l with
  | nil =>
    simp at mem
  | cons hd tl ih =>
    unfold getSubListToMember
    by_cases a_hd: a = hd
    simp [a_hd]
    unfold isPath
    simp
    apply isPath_front_member_graph path


    simp[a_hd]
    unfold isPath
    cases tl with
    | nil =>
      simp [a_hd] at mem
    | cons hd' tl' =>
      unfold getSubListToMember
      by_cases a_hd': a = hd'
      simp [a_hd']
      unfold isPath
      simp
      constructor
      apply isPath_member_graph
      apply path
      simp

      unfold isPath at path
      simp at path
      simp [path]
      rcases path with ⟨_,_, path_hd'_tl'⟩
      apply isPath_member_graph path_hd'_tl'
      simp

      simp [a_hd']
      rw [List.mem_cons] at mem
      cases mem with
      | inl h =>
        exact absurd h a_hd
      | inr h =>
        specialize ih h
        unfold isPath at path
        simp at path
        rcases path with ⟨hd_G,hd_hd', path_hd'_tl'⟩
        specialize ih path_hd'_tl'
        constructor
        apply hd_G
        constructor
        apply hd_hd'
        unfold getSubListToMember  at ih
        simp [a_hd'] at ih
        apply ih


lemma getSubListToMemberIsNotEmpty (l: List A) (a:A) (mem: a ∈ l): getSubListToMember l a mem ≠ [] :=
by
  unfold getSubListToMember
  cases l with
  | nil =>
    simp at mem
  | cons hd tl =>
    simp
    by_cases a_hd: a=hd
    simp [a_hd]
    simp [a_hd]


lemma getSubListToMemberGetLastIsMember (l: List A) (a:A) (mem: a ∈ l): (getSubListToMember l a mem).getLast' (getSubListToMemberIsNotEmpty l a mem) = a :=
by
  induction l with
  | nil =>
    simp at mem
  | cons hd tl ih =>
    unfold getSubListToMember
    by_cases a_hd: a=hd
    simp [a_hd]
    unfold List.getLast'
    simp

    simp[a_hd]
    unfold List.getLast'
    simp[a_hd] at mem
    have h: getSubListToMember tl a mem ≠ []
    apply getSubListToMemberIsNotEmpty
    simp [h]
    apply ih

lemma frontRepetitionInPathImpliesCircle (a:A) (G:Graph A) (visited: List A) (path: isPath (a::visited) G) (mem: a ∈ visited): isCircle (a::(getSubListToMember visited a mem)) G :=
by
  unfold isCircle
  simp
  have not_p: ¬ getSubListToMember visited a mem = []
  apply getSubListToMemberIsNotEmpty
  have h: ¬ Nat.succ (List.length (getSubListToMember visited a mem)) < 2
  simp
  rw [Nat.two_le_iff]
  simp
  by_contra p
  rw [List.length_eq_zero] at p

  exact absurd p not_p

  simp [h]
  constructor
  unfold isPath
  cases p: getSubListToMember visited a mem with
  | nil =>
    exact absurd p not_p
  | cons hd tl =>
    simp
    unfold isPath at path
    cases q:visited with
    | nil =>
      simp[q] at mem
    | cons hd' tl' =>
      simp[q] at path
      simp [q] at p
      have hd_hd': hd' = hd
      apply getSubListToMemberPreservesFront
      apply p
      rw [← hd_hd']
      simp [path]
      rw [hd_hd', ← p]
      apply getSubListToMemberPreservesPath
      simp [path]

  unfold List.getFirst
  unfold List.getLast'
  simp [not_p]
  rw [getSubListToMemberGetLastIsMember]




variable {τ: signature} [DecidableEq τ.vars] [DecidableEq τ.constants] [DecidableEq τ.relationSymbols] [Inhabited τ.constants]

def locallyValid (P: program τ) (d: database τ) (v: groundAtom τ) (G: Graph (groundAtom τ)): Prop :=
 (∃(r: rule τ) (g:grounding τ), r ∈ P ∧ ruleGrounding r g = groundRuleFromAtoms v (G.predecessors v) ) ∨ ((G.predecessors v) = [] ∧ d.contains v)

lemma extractTreeStepValidProofTreeIffAllLocallyValidAndAcyclic (P: program τ) (d: database τ) (a: groundAtom τ) (G: Graph (groundAtom τ)) (acyclic: isAcyclic G) (visited: List (groundAtom τ)) (path: isPath (a::visited) G) (valid: ∀ (a: groundAtom τ), a ∈ G.vertices → locallyValid P d a G): isValid P d (extractTreeStep a G visited path) :=
by
  induction' h:(height (extractTreeStep a G visited path)) using Nat.strongInductionOn with n ih generalizing a visited
  unfold extractTreeStep

  have a_visited: ¬ a ∈ visited
  by_contra p
  have circle: isCircle (a::(getSubListToMember visited a p)) G
  apply frontRepetitionInPathImpliesCircle
  apply path
  unfold isAcyclic at acyclic
  specialize acyclic (a :: getSubListToMember visited a p)
  exact absurd circle acyclic

  simp [a_visited]
  unfold isValid
  simp
  have a_mem: a ∈ G.vertices
  apply isPath_front_member_graph path
  specialize valid a a_mem
  unfold locallyValid at valid
  cases valid with
  | inl valid =>
    rcases valid with ⟨r,g,rP, grounding_r⟩
    left
    use r
    constructor
    apply rP
    constructor
    use g
    rw [grounding_r, groundRuleEquality]
    unfold groundRuleFromAtoms
    simp

    apply List.ext_get
    rw [List.length_map, List.length_attach]
    intro n h1 h2
    rw [List.get_map]
    simp
    rw [rootOfExtractTreeStep]

    rw [List.all₂_iff_forall]
    simp
    intro t ga ga_mem extract
    rw [← extract]

    specialize ih (height t)
    have height_t_n: height t < n
    rw [← h, ← extract]
    apply extractTreeStepHeight
    apply ga_mem
    apply a_visited

    specialize ih height_t_n ga (a::visited)

    have path_ga: isPath (ga :: a :: visited) G
    unfold isPath
    simp
    constructor
    apply G.complete
    apply a_mem
    apply ga_mem
    constructor
    apply ga_mem
    apply path

    specialize ih path_ga
    rw [← extract] at ih
    simp at ih
    apply ih
  | inr dbCase =>
    right
    apply dbCase

lemma verticesOfLocallyValidAcyclicGraphAreInProofTheoreticSemantics (P: program τ) (d: database τ)  (G: Graph (groundAtom τ)) (acyclic: isAcyclic G)  (valid: ∀ (a: groundAtom τ), a ∈ G.vertices → locallyValid P d a G): List.toSet G.vertices ⊆ proofTheoreticSemantics P d :=
by
  rw [Set.subset_def]
  intro a a_mem
  rw [← List.toSet_mem] at a_mem
  unfold proofTheoreticSemantics
  simp
  use extractTreeStep a G [] (singletonPath a G a_mem)
  constructor
  apply rootOfExtractTreeStep
  apply extractTreeStepValidProofTreeIffAllLocallyValidAndAcyclic
  apply acyclic
  apply valid

def List.map_except_collect.go (f: A → Finset B → Except String (Finset B)) (l: List A) (S: Finset B): Except String (Finset B) :=
  match l with
  | [] => Except.ok S
  | hd::tl =>
    match f hd S with
    | Except.error e => Except.error e
    | Except.ok S' => List.map_except_collect.go f tl S'


def List.map_except_collect (f: A → Finset B → Except String (Finset B)) (l: List A): Except String (Finset B) := List.map_except_collect.go f l ∅

def dfsStepAndValidate (f: A → List A → Except String Unit) (a:A) (G:Graph A) (currPath: List A) (path: isPath (a::currPath) G): Except String (Finset A):=
  match f a (G.predecessors a) with
  | Except.error e => Except.error e
  | Except.ok _ =>
    if h: a ∈ currPath
    then Except.error "Circle detected"
    else
    match List.map_except_collect (fun ⟨x, _h⟩ b => dfsStepAndValidate f x G (a::currPath) (isPath_extends_predecessors path x _h)) (G.predecessors a).attach with
    | Except.error e => Except.error e
    | Except.ok S => Except.ok (S ∪ {a})
termination_by dfsStepAndValidate f a G currPath path => ((List.toFinset G.vertices).card - (List.toFinset currPath).card)
decreasing_by
  simp_wf
  rw [← List.mem_toFinset] at h
  rw [removeFrontOfLtMin]
  simp
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff]
  use a
  apply Finset.card_le_of_subset
  rw [Finset.subset_iff]
  intro x
  simp
  intro p
  rw [← List.mem_toFinset]
  apply isPathImplSubset path
  simp
  apply p

  apply Finset.card_le_of_subset
  apply isPathImplSubset
  apply isPath_of_cons path
