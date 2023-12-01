import CertifyingDatalog.Datalog

instance mockDatabase (τ: signature) [DecidableEq τ.vars] [DecidableEq τ.constants] [DecidableEq τ.relationSymbols]: database τ where
  contains:= fun _ => true
