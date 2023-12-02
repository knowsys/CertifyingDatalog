import «CertifyingDatalog»

structure parsingResult where
  (model: List String)
  (trees: List Tree)
deriving Lean.FromJson, Lean.ToJson, Repr

structure verificationProblem (relationList: List (String × Nat)) where
  model: List (atom (parsingSignature relationList))
  trees: List (proofTree (parsingSignature relationList))

def parsingResultToVerificationProblem (input: parsingResult )(relationList: List (String × Nat)): Except String (verificationProblem relationList) :=
  match List.map_except (fun x => parseGroundAtom relationList (tokenize x)) input.model with
  | Except.error msg => Except.error ("Error parsing model " ++ msg)
  | Except.ok model =>
    match List.map_except (fun x => proofTreeFromTree relationList x) input.trees with
    | Except.error msg => Except.error ("Error parsing trees " ++ msg )
    | Except.ok trees => Except.ok {model:=model, trees:=trees}

def main (args: List String): IO Unit := do
  if p:args.length < 2
  then
    IO.println "Too few arguments"
  else
    have zero_args: 0 < args.length := by
      simp at p
      by_contra h'
      simp at h'
      rw [h'] at p
      simp at p
    have one_args: 1 < args.length := by
      simp at p
      apply Nat.lt_of_succ_le
      simp [p]

    let programFileName := System.FilePath.mk (args.get (Fin.mk 0 zero_args))
    if ← programFileName.pathExists
    then
      match parseMockProgram (← IO.FS.lines programFileName).toList with
      | Except.error msg => IO.println ("Error parsing program to mockProgram-- " ++ msg )
      | Except.ok (mockProgram, relationList) =>
        match mockProgramToProgram mockProgram relationList with
        | Except.error msg => IO.println ("Error parsing programm -- " ++ msg )
        | Except.ok program =>
          let database := mockDatabase (parsingSignature relationList)

          let problemFileName := System.FilePath.mk (args.get (Fin.mk 1 one_args))
          if ← problemFileName.pathExists
          then
            match Lean.Json.parse (← IO.FS.readFile problemFileName) with
            | Except.error msg => IO.println ("Error parsing JSON " ++ msg)
            | Except.ok json =>
              match Lean.fromJson? (α:=parsingResult) json with
              | Except.error msg => IO.println ("Json does not match problem description" ++ msg)
              | Except.ok parsedProblem =>
                match parsingResultToVerificationProblem parsedProblem relationList with
                | Except.error msg => IO.println ("Error converting problem the program's signature. -- " ++ msg )
                | Except.ok problem => IO.println ("Success")
          else
            IO.println "Problem file does not exist."

    else
      IO.println (programFileName.toString ++ "is not an existing file")

#eval main ["Examples/join.rls", "Examples/ExampleProblem.json"]
