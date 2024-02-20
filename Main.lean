import «CertifyingDatalog»

def termParsingSignatureToString {helper: parsingArityHelper} (t: term (parsingSignature helper)): String :=
  match t with
  | term.constant c => c
  | term.variableDL v => v

def atomParsingSignatureToString {helper: parsingArityHelper} (a: atom (parsingSignature helper)): String :=
 let terms :=
    match a.atom_terms with
    | [] => ""
    | hd::tl => List.foldl (fun x y => x ++ "," ++ (termParsingSignatureToString y)) (termParsingSignatureToString hd) tl
  a.symbol.val ++ "(" ++ terms ++ ")"

def ruleParsingSignatureToString {helper: parsingArityHelper} (r: rule (parsingSignature helper)): String :=
  match r.body with
  | [] => atomParsingSignatureToString r.head ++ "."
  | hd::tl => atomParsingSignatureToString r.head ++ ":-" ++ (List.foldl (fun x y => x ++ "," ++ (atomParsingSignatureToString y) ) (atomParsingSignatureToString hd) tl)

def mergeList {A: Type} [DecidableEq A] (l1 l2: List A): List A :=
  match l1 with
  | [] => l2
  | hd::tl => if hd ∈ l2
              then mergeList tl l2
              else mergeList tl (hd::l2)

lemma mergeList_mem {A: Type} [DecidableEq A] (l1 l2: List A) (a:A): a ∈ mergeList l1 l2 ↔ a ∈ l1 ∨ a ∈ l2 :=
by
  induction l1 generalizing l2 with
  | nil =>
    unfold mergeList
    simp
  | cons hd tl ih =>
    unfold mergeList
    by_cases hd_l2: hd ∈ l2
    simp[hd_l2]
    rw [ih]
    constructor
    intro h
    cases h with
    | inl h =>
      left
      right
      apply h
    | inr h =>
      right
      apply h

    intro h
    cases h with
    | inl h =>
      cases h with
      | inl h =>
        rw [← h] at hd_l2
        right
        apply hd_l2
      | inr h =>
        left
        apply h
    | inr h =>
      right
      apply h

    simp [hd_l2]
    rw [ih]
    simp
    tauto


def collectModel {helper: parsingArityHelper} (l: List (proofTree (parsingSignature helper))): List (groundAtom (parsingSignature helper)):=
  match l with
  | [] => []
  | hd::tl =>
    mergeList (proofTreeElements hd) (collectModel tl)

lemma collectModelHasTreeElements {helper: parsingArityHelper} (l: List (proofTree (parsingSignature helper))) (ga: groundAtom (parsingSignature helper)): ga ∈ collectModel l ↔ ∃ (t: proofTree (parsingSignature helper)), t ∈ l ∧ elementMember ga t = true := by
  induction l with
  | nil =>
    unfold collectModel
    simp
  | cons hd tl ih =>
    unfold collectModel
    rw [mergeList_mem, ih]
    simp
    rw [inProofTreeElementsIffelementMember]

lemma collectModelToSetIsSetOfValidTreesElements {helper: parsingArityHelper} (l: List (proofTree (parsingSignature helper))): List.toSet (collectModel l) = {ga: groundAtom (parsingSignature helper) | ∃ (t: proofTree (parsingSignature helper)), t ∈ l ∧ elementMember ga t = true} :=
by
  apply Set.ext
  intro ga
  rw [← List.toSet_mem, collectModelHasTreeElements]
  simp



def checkValidnessMockDatabase {helper: parsingArityHelper}  (problem: verificationProblem helper): Except String Unit :=
  let d:= mockDatabase (parsingSignature helper)
  match validateTreeList problem.program d problem.trees  ruleParsingSignatureToString with
  | Except.error e => Except.error e
  | Except.ok _ => Except.ok ()

lemma checkValidnessMockDatabaseUnitIffAllTreesAreValid {helper: parsingArityHelper}  (problem: verificationProblem helper): checkValidnessMockDatabase problem = Except.ok () ↔ ∀ (t: proofTree (parsingSignature helper)), t ∈ problem.trees → isValid (List.toFinset problem.program) (mockDatabase (parsingSignature helper)) t :=
by
  unfold checkValidnessMockDatabase
  simp
  rw [← validateTreeListUnitIffAllTreesValid (ruleToString:=ruleParsingSignatureToString)]
  cases validateTreeList problem.program (mockDatabase (parsingSignature helper)) problem.trees ruleParsingSignatureToString with
  | error e =>
    simp
  | ok u =>
    simp

def checkValidnessGraphMockDatabase {helper: parsingArityHelper} (problem: graphVerificationProblem helper):  Except String Unit :=
  let m:= parseProgramToSymbolSequenceMap problem.program (fun _ => [])
  let d:= mockDatabase (parsingSignature helper)
  dfs problem.graph (fun a l => locallyValidityChecker m d l a ruleParsingSignatureToString)

lemma checkValidnessGraphMockDatabaseIffAllValid {helper: parsingArityHelper}  (problem: graphVerificationProblem helper): checkValidnessGraphMockDatabase problem = Except.ok () ↔ isAcyclic problem.graph ∧ (∀ (a:groundAtom (parsingSignature helper) ), a ∈ problem.graph.vertices → locallyValid problem.program.toFinset (mockDatabase (parsingSignature helper)) a problem.graph) ∧ problem.graph.vertices.toSet ⊆ proofTheoreticSemantics problem.program.toFinset (mockDatabase (parsingSignature helper)) :=
by
  unfold checkValidnessGraphMockDatabase
  rw [dfs_semantics]
  constructor
  intro h
  rcases h with ⟨acyc, localValid⟩
  constructor
  apply acyc
  constructor
  intro a a_mem
  specialize localValid a a_mem
  rw [locallyValidityCheckerUnitIffLocallyValid (P:=problem.program) (G:=problem.graph)] at localValid
  apply localValid
  rfl
  rfl
  apply verticesOfLocallyValidAcyclicGraphAreInProofTheoreticSemantics (acyclic:=acyc)
  intro a a_mem
  specialize localValid a a_mem
  rw [locallyValidityCheckerUnitIffLocallyValid (P:=problem.program) (G:=problem.graph)] at localValid
  apply localValid
  rfl
  rfl

  intro h
  rcases h with ⟨acyclic, valid, _ ⟩
  constructor
  apply acyclic
  intro a a_mem
  rw [locallyValidityCheckerUnitIffLocallyValid (P:=problem.program) (G:=problem.graph)]
  apply valid a a_mem
  rfl
  rfl



def mainCheckMockDatabase {helper: parsingArityHelper} (problem: verificationProblem helper) (safe: ∀ (r: rule (parsingSignature helper) ), r ∈ problem.program → r.isSafe): Except String Unit :=
  let d:= mockDatabase (parsingSignature helper)
  let model:= collectModel problem.trees
  match validateTreeList problem.program d problem.trees  ruleParsingSignatureToString  with
  | Except.error e => Except.error e
  | Except.ok _ =>
    match modelChecker model problem.program safe with
    | Except.error e => Except.error e
    | Except.ok _ =>
      if mockDatabaseContainedInModel d (List.toSet model) = true
      then Except.ok ()
      else Except.error "Model does not contain database"

lemma mainCheckMockDatabaseUnitIffSolution {helper: parsingArityHelper}  (problem: verificationProblem helper) (safe: ∀ (r: rule (parsingSignature helper) ), r ∈ problem.program → r.isSafe): mainCheckMockDatabase problem safe = Except.ok () ↔ (List.toSet (collectModel problem.trees)) = proofTheoreticSemantics problem.program.toFinset (mockDatabase (parsingSignature helper)) ∧ ∀ (t: proofTree (parsingSignature helper)), t ∈ problem.trees → isValid problem.program.toFinset (mockDatabase (parsingSignature helper)) t:= by
  constructor
  unfold mainCheckMockDatabase
  simp
  intro h

  cases valid_trees: validateTreeList problem.program (mockDatabase (parsingSignature helper)) problem.trees
   ruleParsingSignatureToString with
  | error e => simp [valid_trees] at h
  | ok _ =>
    simp [valid_trees] at h
    cases model: modelChecker (collectModel problem.trees) problem.program safe with
    | error e => simp[model] at h
    | ok _ =>
      simp [model] at h
      rw [validateTreeListUnitIffSubsetSemanticsAndAllElementsHaveValidTrees] at valid_trees
      rcases valid_trees with ⟨left,right⟩
      rw [modelCheckerUnitIffAllRulesTrue] at model
      constructor
      apply Set.Subset.antisymm
      rw [collectModelToSetIsSetOfValidTreesElements]
      apply left
      rw [SemanticsEquivalence]
      apply leastModel
      unfold model
      constructor
      apply model
      rw [← mockDatabaseContainedInModelTrue]
      have db: mockDatabaseContainedInModel (mockDatabase (parsingSignature helper)) (List.toSet (collectModel problem.trees)) = true
      by_contra p
      simp at p
      specialize h p
      apply h
      apply db
      apply right

  intro h
  rcases h with ⟨sol_eq, valid_tree⟩
  unfold mainCheckMockDatabase
  simp
  have p: validateTreeList problem.program (mockDatabase (parsingSignature helper)) problem.trees ruleParsingSignatureToString = Except.ok ()
  rw [validateTreeListUnitIffSubsetSemanticsAndAllElementsHaveValidTrees]
  constructor
  rw [← collectModelToSetIsSetOfValidTreesElements]
  rw [sol_eq]
  apply valid_tree

  simp [p]
  have model: model (List.toFinset problem.program) (mockDatabase (parsingSignature helper)) (List.toSet (collectModel problem.trees))
  rw [sol_eq]
  apply proofTheoreticSemanticsIsModel
  unfold model at model
  rcases model with ⟨model,_⟩

  have q: modelChecker (collectModel problem.trees) problem.program safe = Except.ok ()
  rw [modelCheckerUnitIffAllRulesTrue]
  apply model

  simp[q]
  unfold mockDatabaseContainedInModel
  simp


def mainCheckGraphMockDatabase {helper: parsingArityHelper} (problem: graphVerificationProblem helper) (safe: ∀ (r: rule (parsingSignature helper) ), r ∈ problem.program → r.isSafe): Except String Unit :=
  let m:= parseProgramToSymbolSequenceMap problem.program (fun _ => [])
  let d:= mockDatabase (parsingSignature helper)
  match dfs problem.graph (fun a l => locallyValidityChecker m d l a ruleParsingSignatureToString)   with
  | Except.error e => Except.error e
  | Except.ok _ =>
    match modelChecker problem.graph.vertices problem.program safe with
    | Except.error e => Except.error e
    | Except.ok _ =>
      if mockDatabaseContainedInModel d (List.toSet problem.graph.vertices) = true
      then Except.ok ()
      else Except.error "Model does not contain database"

lemma mainCheckGraphMockDatabaseUnitIffSolution {helper: parsingArityHelper} (problem: graphVerificationProblem helper) (safe: ∀ (r: rule (parsingSignature helper) ), r ∈ problem.program → r.isSafe): mainCheckGraphMockDatabase problem safe = Except.ok () ↔ (List.toSet problem.graph.vertices) = proofTheoreticSemantics problem.program.toFinset (mockDatabase (parsingSignature helper)) ∧ isAcyclic problem.graph ∧ (∀ (a:groundAtom (parsingSignature helper) ), a ∈ problem.graph.vertices → locallyValid problem.program.toFinset (mockDatabase (parsingSignature helper)) a problem.graph):=
by
  unfold mainCheckGraphMockDatabase
  simp
  constructor
  intro h
  simp at h
  cases dfs_result: dfs problem.graph (fun a l => locallyValidityChecker (parseProgramToSymbolSequenceMap problem.program (fun _ => [])) (mockDatabase (parsingSignature helper)) l a ruleParsingSignatureToString )with
  | error e =>
    simp[dfs_result] at h
  | ok _ =>
    simp [dfs_result] at h
    cases modelCheck: modelChecker problem.graph.vertices problem.program safe with
    | error e =>
      simp [modelCheck] at h
    | ok _ =>
      simp only [modelCheck] at h
      have db: mockDatabaseContainedInModel (mockDatabase (parsingSignature helper)) (List.toSet problem.graph.vertices) = true
      by_contra p
      simp [p] at h

      rw [dfs_semantics] at dfs_result
      rcases dfs_result with ⟨acyclic,valid⟩
      rw [modelCheckerUnitIffAllRulesTrue] at modelCheck
      rw [mockDatabaseContainedInModelTrue] at db
      constructor
      apply Set.Subset.antisymm
      apply verticesOfLocallyValidAcyclicGraphAreInProofTheoreticSemantics _ _ _ acyclic
      intro a a_mem
      specialize valid a a_mem
      rw [locallyValidityCheckerUnitIffLocallyValid (P:=problem.program) (G:=problem.graph)] at valid
      apply valid
      rfl
      rfl

      rw [SemanticsEquivalence]
      apply leastModel
      unfold model
      constructor
      apply modelCheck
      apply db

      --end semantics
      constructor
      apply acyclic
      intro a a_mem
      specialize valid a a_mem
      rw [locallyValidityCheckerUnitIffLocallyValid (P:=problem.program) (G:=problem.graph)] at valid
      apply valid
      rfl
      rfl

  intro h
  rcases h with ⟨semantics, acyclic, valid⟩
  have dfs_result: dfs problem.graph (fun a l =>
      locallyValidityChecker (parseProgramToSymbolSequenceMap problem.program fun _ => [])
        (mockDatabase (parsingSignature helper)) l a ruleParsingSignatureToString) = Except.ok ()
  rw [dfs_semantics]
  constructor
  apply acyclic
  intro a a_mem
  rw [locallyValidityCheckerUnitIffLocallyValid (P:=problem.program) (G:=problem.graph)]
  apply valid a a_mem
  rfl
  rfl
  simp [dfs_result]

  have modelChecker: modelChecker problem.graph.vertices problem.program safe = Except.ok ()
  rw [modelCheckerUnitIffAllRulesTrue]
  intro r rP
  have ismodel: model problem.program.toFinset (mockDatabase (parsingSignature helper)) (List.toSet problem.graph.vertices)
  rw [semantics]
  apply proofTheoreticSemanticsIsModel
  unfold model at ismodel
  apply And.left ismodel r rP
  simp only [modelChecker]

  unfold mockDatabaseContainedInModel
  simp


structure argsParsed where
  (programFileName: String)
  (complete: Bool)
  (help: Bool)
  (graph: Bool)

def parseArgsHelper (args: List String) (curr: argsParsed) : Except String argsParsed  :=
  match args with
  | [] =>
    if curr.programFileName == ""
    then Except.error "No program file name provided"
    else Except.ok curr
  | hd::tl =>
    if hd ∈ ["-h", "--help"]
    then Except.ok {programFileName := "", complete := false, help := true, graph:= false}
    else  if hd ∈  ["-c", "-g"]
          then
            if hd == "-c"
            then parseArgsHelper tl {programFileName := "", complete := true, help := false, graph:= curr.graph}
            else
              if hd == "-g"
              then  parseArgsHelper tl {programFileName := "", complete := curr.complete , help := false, graph:= true}
              else Except.error ("Unknown argument " ++ hd)
          else
          if tl == []
          then Except.ok {programFileName := hd, complete := curr.complete, help := false, graph:= curr.graph}
          else Except.error "Too many arguments"

def parseArgs (args: List String): Except String argsParsed := parseArgsHelper args {programFileName := "", complete := false, help:= false, graph:= false}

def printHelp: IO Unit := do
  IO.println "Datalog results validity checker"
  IO.println "Input [Options] <problemFile>"
  IO.println "Arguments"
  IO.println "  <problemFile>: contains a json description of the program and the proof trees"
  IO.println "Options"
  IO.println "  -h --help Help (displayed right now)"
  IO.println "  -g        Use a graph instead of a list of trees as an input via a list of edges (start -- end)"
  IO.println "  -c        Completeness check: in addition to validating the trees check if result is also a model"

def getTreeProblemFromJson (fileName: String): IO (Except String (verificationProblemSignatureWrapper)) := do
  let filePath := System.FilePath.mk fileName
  if ← filePath.pathExists
      then
        match Lean.Json.parse (← IO.FS.readFile filePath) with
          | Except.error msg => pure (Except.error ("Error parsing JSON " ++ msg))
          | Except.ok json =>
            match Lean.fromJson? (α:=problemInput) json with
              | Except.error msg => pure (Except.error ("Json does not match problem description" ++ msg))
              | Except.ok parsedProblem =>
                pure (convertProblemInputToVerificationProblem parsedProblem)
  else pure (Except.error "File does not exist")

def main_trees (argsParsed: argsParsed): IO Unit := do
  match ← getTreeProblemFromJson argsParsed.programFileName with
  | Except.error e => IO.println e
  | Except.ok transformedInput =>
    let problem := transformedInput.problem
    if argsParsed.complete = true
    then
      IO.println "Completeness check"
      match safe: safetyCheckProgram problem.program ruleParsingSignatureToString (fun x => x) with
      | Except.error msg => IO.println msg
      | Except.ok _ =>
        have safe': ∀ (r: rule (parsingSignature transformedInput.helper)), r ∈ problem.program → r.isSafe := by
          rw [safetyCheckProgramUnitIffProgramSafe] at safe
          apply safe
        match mainCheckMockDatabase problem safe' with
        | Except.ok _ => IO.println "Valid result"
        | Except.error msg => IO.println ("Invalid result due to " ++ msg )
    else
      match checkValidnessMockDatabase problem with
      | Except.error msg => IO.println ("Invalid result due to " ++ msg )
      | Except.ok _ => IO.println "Valid result"

def getGraphProblemFromJson (fileName: String): IO (Except String (graphVerificationProblemSignatureWrapper)) := do
  let filePath := System.FilePath.mk fileName
  if ← filePath.pathExists
      then
        match Lean.Json.parse (← IO.FS.readFile filePath) with
          | Except.error msg => pure (Except.error ("Error parsing JSON " ++ msg))
          | Except.ok json =>
            match Lean.fromJson? (α:=graphInputProblem) json with
              | Except.error msg => pure (Except.error ("Json does not match problem description" ++ msg))
              | Except.ok parsedProblem =>
                pure (convertGraphProblemInputToGraphVerificationProblem parsedProblem)
  else pure (Except.error "File does not exist")


def main_graph (argsParsed: argsParsed): IO Unit := do
  match ← getGraphProblemFromJson argsParsed.programFileName with
  | Except.error e => IO.println e
  | Except.ok transformedInput =>
    let problem := transformedInput.problem
    if argsParsed.complete = true
    then
      IO.println "Completeness check"
      match safe: safetyCheckProgram problem.program ruleParsingSignatureToString (fun x => x) with
      | Except.error msg => IO.println msg
      | Except.ok _ =>
        have safe': ∀ (r: rule (parsingSignature transformedInput.helper)), r ∈ problem.program → r.isSafe := by
          rw [safetyCheckProgramUnitIffProgramSafe] at safe
          apply safe
        match mainCheckGraphMockDatabase problem safe' with
        | Except.ok _ => IO.println "Valid result"
        | Except.error msg => IO.println ("Invalid result due to " ++ msg )
    else
      match checkValidnessGraphMockDatabase problem with
      | Except.error msg => IO.println ("Invalid result due to " ++ msg )
      | Except.ok _ => IO.println "Valid result"


def main(args: List String): IO Unit := do
  match parseArgs args with
  | Except.error e => IO.println e
  | Except.ok argsParsed =>
    if argsParsed.help = true
    then printHelp
    else
      if argsParsed.graph = true
      then
        main_graph argsParsed
      else
        main_trees argsParsed
