import CertifyingDatalog.Datalog
import CertifyingDatalog.Unification


variable {τ: signature} [DecidableEq τ.vars] [DecidableEq τ.constants] [DecidableEq τ.relationSymbols]

def checkRuleMatch (P: List (rule τ)) (gr: groundRule τ): Bool :=
  match P with
  | List.nil => false
  | List.cons hd tl =>
    if Option.isSome (matchRule hd gr)
    then true
    else checkRuleMatch tl gr


def treeValidatorHelper (P: List (rule τ)) (d: database τ) (t: proofTree τ): Bool :=
  match t with
  | proofTree.node a l =>
    if l.isEmpty
    then  if d.contains a
          then true
          else if checkRuleMatch P {head:= a, body := List.map root l}
                then true
                else false
    else
      if checkRuleMatch P {head:= a, body := List.map root l}
      then List.all l.attach (fun ⟨x, _h⟩ => treeValidatorHelper P d x)
      else false
termination_by treeValidatorHelper P d t => sizeOf t
decreasing_by
  simp_wf
  apply Nat.lt_trans (m:= sizeOf l)
  apply List.sizeOf_lt_of_mem _h
  simp


def treeValidator (P: List (rule τ)) (d: database τ) (a: groundAtom τ)(t: proofTree τ): Bool :=
  if root t = a
  then treeValidatorHelper P d t
  else false

theorem treeValidatorIff (P: List (rule τ)) (d: database τ) (a: groundAtom τ)(t: proofTree τ): treeValidator P d a t = true ↔ isValid (List.toFinset P) d t ∧ root t = a :=
by
  sorry
