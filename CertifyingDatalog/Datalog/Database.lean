import CertifyingDatalog.Basic
import CertifyingDatalog.Datalog.Basic
import CertifyingDatalog.Datalog.Grounding
import CertifyingDatalog.Datalog.Substitution

class Database (τ: Signature) [DecidableEq τ.vars] [DecidableEq τ.relationSymbols] [DecidableEq τ.constants] [Hashable τ.constants] [Hashable τ.vars] [Hashable τ.relationSymbols] where
  contains: GroundAtom τ → Bool

instance univDatabase (τ: Signature) [DecidableEq τ.vars] [DecidableEq τ.constants] [DecidableEq τ.relationSymbols] [Hashable τ.constants] [Hashable τ.vars] [Hashable τ.relationSymbols]
: Database τ where
  contains := fun _ => true

instance emptyDatabase (τ: Signature) [DecidableEq τ.vars] [DecidableEq τ.constants] [DecidableEq τ.relationSymbols] [Hashable τ.constants] [Hashable τ.vars] [Hashable τ.relationSymbols]
: Database τ where
  contains := fun _ => false

