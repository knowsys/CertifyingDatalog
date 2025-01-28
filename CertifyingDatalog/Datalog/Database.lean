import CertifyingDatalog.Basic
import CertifyingDatalog.Datalog.Basic
import CertifyingDatalog.Datalog.Grounding
import CertifyingDatalog.Datalog.Substitution

class Database (τ: Signature) where
  contains: GroundAtom τ → Bool

instance univDatabase (τ: Signature) : Database τ where
  contains := fun _ => true

instance emptyDatabase (τ: Signature) : Database τ where
  contains := fun _ => false
