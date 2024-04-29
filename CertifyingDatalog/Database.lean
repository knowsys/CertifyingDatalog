import CertifyingDatalog.Datalog

instance mockDatabase (τ: signature) [DecidableEq τ.vars] [DecidableEq τ.constants] [DecidableEq τ.predicateSymbols] [Hashable τ.constants] [Hashable τ.vars] [Hashable τ.predicateSymbols]
: database τ where
  contains:= fun _ => true

def mockDatabaseContainedInModel {τ: signature} [DecidableEq τ.vars] [DecidableEq τ.constants] [DecidableEq τ.predicateSymbols] [Hashable τ.constants] [Hashable τ.vars] [Hashable τ.predicateSymbols]
 (_d: database τ) (_i: Set (groundAtom τ)): Bool := true

axiom mockDatabaseContainedInModelTrue {τ: signature} [DecidableEq τ.vars] [DecidableEq τ.constants] [DecidableEq τ.predicateSymbols] [Hashable τ.constants] [Hashable τ.vars] [Hashable τ.predicateSymbols]
 (d: database τ) (i: Set (groundAtom τ)): mockDatabaseContainedInModel d i = true ↔ ∀ (ga: groundAtom τ), d.contains ga → ga ∈ i
