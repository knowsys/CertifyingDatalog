import «CertifyingDatalog»

structure parsingResult where
  (model: List String)
  (trees: List Tree)
deriving Lean.FromJson, Lean.ToJson, Repr

structure verificationProblem (relationList: List (String × Nat)) where
  model: List (groundAtom (parsingSignature relationList))
  trees: List (proofTree (parsingSignature relationList))

def parsingResultToVerificationProblem (input: parsingResult )(relationList: List (String × Nat)): Except String (verificationProblem relationList) :=
  match List.map_except (fun x => parseGroundAtom relationList (tokenize x)) input.model with
  | Except.error msg => Except.error ("Error parsing model " ++ msg)
  | Except.ok model =>
    match List.map_except (fun x => proofTreeFromTree relationList x) input.trees with
    | Except.error msg => Except.error ("Error parsing trees " ++ msg )
    | Except.ok trees => Except.ok {model:=model, trees:=trees}

def termParsingSignatureToString {relationList: List (String × Nat)} (t: term (parsingSignature relationList)): String :=
  match t with
  | term.constant c => c.val
  | term.variableDL v => v.val

def atomParsingSignatureToString {relationList: List (String × Nat)} (a: atom (parsingSignature relationList)): String :=
  let terms :=
    match a.atom_terms with
    | [] => ""
    | hd::tl => List.foldl (fun x y => x ++ "," ++ (termParsingSignatureToString y)) (termParsingSignatureToString hd) tl
  a.symbol.val ++ "(" ++ terms ++ ")"

def ruleParsingSignatureToString {relationList: List (String × Nat)} (r: rule (parsingSignature relationList)): String :=
  match r.body with
  | [] => atomParsingSignatureToString r.head ++ "."
  | hd::tl => atomParsingSignatureToString r.head ++ ":-" ++ (List.foldl (fun x y => x ++ "," ++ (atomParsingSignatureToString y) ) (atomParsingSignatureToString hd) tl)

def mainCheckMockDatabase (P: List (rule (parsingSignature relationList))) (problem: verificationProblem relationList) (safe: ∀ (r: rule (parsingSignature relationList) ), r ∈ P → r.isSafe): Except String Unit :=
  let d:= mockDatabase (parsingSignature (relationList))
  match validateTreeList P d problem.trees atomParsingSignatureToString ruleParsingSignatureToString problem.model with
  | Except.error e => Except.error e
  | Except.ok _ =>
    match modelChecker problem.model P safe with
    | Except.error e => Except.error e
    | Except.ok _ =>
      if mockDatabaseContainedInModel d (List.toSet problem.model) = true
      then Except.ok ()
      else Except.error "Model does not contain database"

theorem mainCheckMockDatabseUnitIffSolution (P: List (rule (parsingSignature relationList))) (problem: verificationProblem relationList) (safe: ∀ (r: rule (parsingSignature relationList) ), r ∈ P → r.isSafe) (mem: ∀ (ga: groundAtom (parsingSignature relationList)), ga ∈ problem.model → ∃ (t: proofTree (parsingSignature relationList)), t ∈ problem.trees ∧ elementMember ga t): mainCheckMockDatabase P problem safe = Except.ok () ↔ (List.toSet problem.model) = proofTheoreticSemantics P.toFinset (mockDatabase (parsingSignature relationList)) ∧ ∀ (t: proofTree (parsingSignature relationList)), t ∈ problem.trees → isValid P.toFinset (mockDatabase (parsingSignature relationList)) t:= by
  constructor
  unfold mainCheckMockDatabase
  intro h
  simp at h
  rw [subset_antisymm_iff]
  have treesValid: validateTreeList P (mockDatabase (parsingSignature relationList)) problem.trees atomParsingSignatureToString ruleParsingSignatureToString problem.model = Except.ok ()
  cases p: validateTreeList P (mockDatabase (parsingSignature relationList)) problem.trees atomParsingSignatureToString ruleParsingSignatureToString problem.model with
  | ok _ =>
    simp
  | error e =>
    simp [p] at h
  simp [treesValid] at h
  rw [validateTreeListUnitIffSubsetSemanticsAndAllElementsHaveValidTrees (mem:=mem)] at treesValid
  rcases treesValid with ⟨lt_model, treesValid⟩
  constructor
  constructor
  apply lt_model

  rw [SemanticsEquivalence]
  apply leastModel
  unfold model
  have modelCheck: modelChecker problem.model P safe = Except.ok ()
  cases p:modelChecker problem.model P safe with
  | ok _ =>
    simp
  | error e =>
    simp [p] at h
  simp [modelCheck] at h
  constructor
  rw [modelCheckerUnitIffAllRulesTrue] at modelCheck
  apply modelCheck

  rw [imp_false] at h
  simp at h
  rw [mockDatabaseContainedInModelTrue] at h
  apply h
  apply treesValid

  --back direction
  intro h
  rw [subset_antisymm_iff] at h
  rcases h with ⟨left, treesValid⟩
  unfold mainCheckMockDatabase
  have h': validateTreeList P (mockDatabase (parsingSignature relationList)) problem.trees atomParsingSignatureToString ruleParsingSignatureToString problem.model = Except.ok ()
  rw [validateTreeListUnitIffSubsetSemanticsAndAllElementsHaveValidTrees (mem:=mem)]
  constructor
  rcases left with ⟨lt_sem, _⟩
  apply lt_sem
  apply treesValid

  simp [h']
  rw [← subset_antisymm_iff] at left
  rw [SemanticsEquivalence] at left
  have model_problem: model P.toFinset (mockDatabase (parsingSignature relationList)) (List.toSet problem.model)
  rw [left]
  apply modelTheoreticSemanticsIsModel
  unfold model at model_problem
  rcases model_problem with ⟨model_problem, _⟩
  have p: modelChecker problem.model P safe = Except.ok ()
  rw [modelCheckerUnitIffAllRulesTrue]
  apply model_problem
  simp [p]
  rw [imp_false]
  simp
  unfold mockDatabaseContainedInModel
  rfl





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
                | Except.ok problem =>
                  match safe: safetyCheckProgram program ruleParsingSignatureToString (fun x => x.val) with
                  | Except.error msg => IO.println msg
                  | Except.ok _ =>
                    have safe': ∀ (r: rule (parsingSignature relationList)), r ∈ program → r.isSafe := by
                      rw [safetyCheckProgramUnitIffProgramSafe] at safe
                      apply safe

                    match mainCheckMockDatabase program problem safe' with
                    | Except.ok _ => IO.println "Valid result"
                    | Except.error msg => IO.println ("Invalid result due to " ++ msg )


          else
            IO.println "Problem file does not exist."

    else
      IO.println (programFileName.toString ++ "is not an existing file")

#eval main ["Examples/join.rls", "Examples/ExampleProblem.json"]
