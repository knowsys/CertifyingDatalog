module

public import CertifyingDatalog.Datalog.Grounding

public section

class Database (τ: Signature) where
  contains: GroundAtom τ → Bool

instance univDatabase (τ: Signature) : Database τ where
  contains := fun _ => true

instance emptyDatabase (τ: Signature) : Database τ where
  contains := fun _ => false
