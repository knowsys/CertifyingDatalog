import «CertifyingDatalog»

section CollectTreeModels
  def collectModel {helper: ParseArityHelper} (l: List (ProofTreeSkeleton helper.toSignature)): CheckableModel helper.toSignature :=
    match l with
    | [] => []
    | hd::tl => hd.elements ++ collectModel tl

  lemma collectModelHasTreeElements {helper: ParseArityHelper} (l: List (ProofTreeSkeleton helper.toSignature)) (ga: GroundAtom helper.toSignature): ga ∈ collectModel l ↔ ∃ (t: ProofTreeSkeleton helper.toSignature), t ∈ l ∧ t.elem ga := by
    induction l with
    | nil =>
      unfold collectModel
      simp
    | cons hd tl ih =>
      unfold collectModel
      simp
      rw [ih,Tree.elem_iff_memElements]

  lemma collectModelToSetIsSetOfTreesElements {helper: ParseArityHelper} (l: List (ProofTreeSkeleton helper.toSignature)): List.toSet (collectModel l) = {ga: GroundAtom helper.toSignature | ∃ t, t ∈ l ∧ t.elem ga} := by
    apply Set.ext
    intro ga
    rw [← List.toSet_mem, collectModelHasTreeElements]
    simp
end CollectTreeModels

section TreeListValidity
  def checkTreeListValidityWithUnivDatabase (problem: TreeVerificationProblem): Except String Unit :=
    let db := univDatabase problem.helper.toSignature
    let kb : KnowledgeBase problem.helper.toSignature := { prog := problem.program, db }
    ProofTreeSkeleton.checkValidityOfList problem.trees kb

  theorem checkTreeListValidityWithUnivDatabaseUnitIffAllTreesValid (problem: TreeVerificationProblem): checkTreeListValidityWithUnivDatabase problem = Except.ok () ↔ ((∀ t ∈ problem.trees, t.isValid {prog := problem.program, db := univDatabase problem.helper.toSignature})
    ∧ ((collectModel problem.trees).toSet ⊆ {prog := problem.program, db := univDatabase problem.helper.toSignature : KnowledgeBase problem.helper.toSignature}.proofTheoreticSemantics)) := by
    unfold checkTreeListValidityWithUnivDatabase
    simp only
    rw [collectModelToSetIsSetOfTreesElements]
    rw [← ProofTreeSkeleton.checkValidityOfListOkIffAllValidIffAllValidAndSubsetSemantics]

  def checkTreeListModelhood (problem: TreeVerificationProblem) (safe: problem.program.isSafe): Except String Unit :=
    let model := collectModel problem.trees
    model.checkProgram problem.program safe

  theorem checkTreeListModelHoodUnitIffModel (problem: TreeVerificationProblem) (safe: problem.program.isSafe) :
    checkTreeListModelhood problem safe = Except.ok () ↔ Interpretation.models (List.toSet (collectModel problem.trees)) {prog := problem.program, db := emptyDatabase problem.helper.toSignature} := by
    unfold checkTreeListModelhood
    simp only
    rw [CheckableModel.checkProgramIsOkIffAllRulesAreSatisfied]
    unfold Interpretation.models
    simp
end TreeListValidity

section DagValidity
  def checkDagValidityWithUnivDatabase (problem: GraphVerificationProblem): Except String Unit :=
    let m := problem.program.toSymbolSequenceMap
    let d:= univDatabase problem.helper.toSignature
    problem.graph.checkValidity m d

  theorem checkDagValidityWithUnivDatabaseUnitIffAcyclicAndAllValid (problem: GraphVerificationProblem) : checkDagValidityWithUnivDatabase problem = Except.ok () ↔ ((problem.graph.isAcyclic ∧ (∀ a ∈ problem.graph.vertices, problem.graph.locallyValid_for_kb {prog := problem.program, db := univDatabase problem.helper.toSignature} a))
    ∧ (problem.graph.vertices.toSet ⊆ {prog := problem.program, db := univDatabase problem.helper.toSignature : KnowledgeBase problem.helper.toSignature}.proofTheoreticSemantics)) := by
    unfold checkDagValidityWithUnivDatabase
    simp only
    rw [problem.graph.checkValidityIsOkIffAcyclicAndAllValid {prog := problem.program, db := univDatabase problem.helper.toSignature}]
    simp only [iff_self_and, and_imp]
    intro acyclic all_valid
    apply Graph.verticesOfLocallyValidAcyclicGraphAreInProofTheoreticSemantics
    · exact acyclic
    · exact all_valid

  def checkDagModelhood (problem: GraphVerificationProblem) (safe: problem.program.isSafe): Except String Unit :=
    let model : CheckableModel problem.helper.toSignature := problem.graph.vertices
    model.checkProgram problem.program safe

  theorem checkDagModelhoodUnitIffModel (problem: GraphVerificationProblem) (safe: problem.program.isSafe) :
    checkDagModelhood problem safe = Except.ok () ↔ Interpretation.models (List.toSet problem.graph.vertices) {prog := problem.program, db := emptyDatabase problem.helper.toSignature} := by
    unfold checkDagModelhood
    simp only
    rw [CheckableModel.checkProgramIsOkIffAllRulesAreSatisfied]
    unfold Interpretation.models
    simp
end DagValidity

section OrderedProofGraphValidity
  def checkOrderedGraphValidityWithUnivDatabase (problem: OrderedGraphVerificationProblem): Except String Unit :=
    let m := problem.program.toSymbolSequenceMap
    let d:= univDatabase problem.helper.toSignature
    problem.graph.checkValidity m d

  theorem checkOrderedGraphValidityWithUnivDatabaseUnitIffValid (problem: OrderedGraphVerificationProblem) : checkOrderedGraphValidityWithUnivDatabase problem = Except.ok () ↔ ((problem.graph.isValid {prog := problem.program, db := univDatabase problem.helper.toSignature})
    ∧ (problem.graph.labels.toSet ⊆ {prog := problem.program, db := univDatabase problem.helper.toSignature : KnowledgeBase problem.helper.toSignature}.proofTheoreticSemantics)) := by
    unfold checkOrderedGraphValidityWithUnivDatabase
    simp only
    rw [problem.graph.checkValidity_semantics {prog := problem.program, db := univDatabase problem.helper.toSignature}]
    simp only [iff_self_and]
    intro isValid
    apply OrderedProofGraph.verticesValidOrderedProofGraphAreInProofTheoreticSemantics
    exact isValid

  def checkOrderedGraphModelhood (problem: OrderedGraphVerificationProblem) (safe: problem.program.isSafe): Except String Unit :=
    let model : CheckableModel problem.helper.toSignature := problem.graph.labels
    model.checkProgram problem.program safe

  theorem checkOrderedGraphModelhoodUnitIffModel (problem: OrderedGraphVerificationProblem) (safe: problem.program.isSafe) :
    checkOrderedGraphModelhood problem safe = Except.ok () ↔ Interpretation.models (List.toSet problem.graph.labels) {prog := problem.program, db := emptyDatabase problem.helper.toSignature} := by
    unfold checkOrderedGraphModelhood
    simp only
    rw [CheckableModel.checkProgramIsOkIffAllRulesAreSatisfied]
    unfold Interpretation.models
    simp
end OrderedProofGraphValidity

inductive InputFormat where
| trees: InputFormat
| graph: InputFormat
| orderedGraph: InputFormat

structure ArgsParsed where
  (programFileName: String)
  (complete: Bool)
  (help: Bool)
  (format: InputFormat)

def parseArgsHelper (args: List String) (curr: ArgsParsed) : Except String ArgsParsed :=
  match args with
  | [] =>
    if curr.programFileName == ""
    then Except.error "No program file name provided"
    else Except.ok curr
  | hd::tl =>
    if hd ∈ ["-h", "--help"]
    then Except.ok {programFileName := "", complete := false, help := true, format:= InputFormat.trees}
    else  if hd ∈  ["-c", "-g", "-o"]
          then
            if hd == "-c"
            then parseArgsHelper tl {programFileName := "", complete := true, help := false, format:= curr.format}
            else
              if hd == "-g"
              then  parseArgsHelper tl {programFileName := "", complete := curr.complete , help := false, format:= InputFormat.graph}
              else
                if hd == "-o"
                then  parseArgsHelper tl {programFileName := "", complete := curr.complete , help := false, format:= InputFormat.orderedGraph}
                else
                Except.error ("Unknown argument " ++ hd)
          else
          if tl == []
          then Except.ok {programFileName := hd, complete := curr.complete, help := false, format:= curr.format}
          else Except.error "Too many arguments"

def parseArgs (args: List String): Except String ArgsParsed := parseArgsHelper args {programFileName := "", complete := false, help:= false, format:= InputFormat.trees}

def printHelp: IO Unit := do
  IO.println "Datalog results validity checker"
  IO.println "Input [Options] <problemFile>"
  IO.println "Arguments"
  IO.println "  <problemFile>: contains a json description of the program and the proof trees"
  IO.println "Options"
  IO.println "  -h --help Help (displayed right now)"
  IO.println "  -g        Use a graph instead of a list of trees as an input via a list of edges (start -- end)"
  IO.println "  -o        Use an topologically ordered graph instead of a list of trees as an input via a list atom and list of natural numbers of predecessors"

  IO.println "  -c        Completeness check: instead of validating the proof, check if the facts form a model. (Can be combined with -g or -o.)"

def parseTreeProblemFromJson (fileName: String): IO (Except String TreeVerificationProblem) := do
  let filePath := System.FilePath.mk fileName
  if ← filePath.pathExists
      then
        match Lean.Json.parse (← IO.FS.readFile filePath) with
          | Except.error msg => pure (Except.error ("Error parsing JSON " ++ msg))
          | Except.ok json =>
            match Lean.fromJson? (α:=TreeProblemInput) json with
              | Except.error msg => pure (Except.error ("Json does not match problem description" ++ msg))
              | Except.ok parsedProblem =>
                pure (TreeVerificationProblem.fromProblemInput parsedProblem)
  else pure (Except.error "File does not exist")

def main_trees (argsParsed: ArgsParsed): IO Unit := do
  match ← parseTreeProblemFromJson argsParsed.programFileName with
  | Except.error e => IO.println e
  | Except.ok problem =>
    if argsParsed.complete = true
    then
      IO.println "Checking Modelhood..."
      match safe: problem.program.checkSafety with
      | Except.error msg => IO.println msg
      | Except.ok _ =>
        have safe': ∀ (r: Rule problem.helper.toSignature), r ∈ problem.program → r.isSafe := by
          rw [Program.checkSafety_iff_isSafe] at safe
          apply safe
        match checkTreeListModelhood problem safe' with
        | Except.error msg => IO.println ("Invalid result due to: " ++ msg )
        | Except.ok _ => IO.println "Valid result"
    else
      IO.println "Checking Proof Validity..."
      match checkTreeListValidityWithUnivDatabase problem with
      | Except.error msg => IO.println ("Invalid result due to: " ++ msg )
      | Except.ok _ => IO.println "Valid result"

def parseDagProblemFromJson (fileName: String): IO (Except String GraphVerificationProblem) := do
  let filePath := System.FilePath.mk fileName
  if ← filePath.pathExists
      then
        match Lean.Json.parse (← IO.FS.readFile filePath) with
          | Except.error msg => pure (Except.error ("Error parsing JSON " ++ msg))
          | Except.ok json =>
            match Lean.fromJson? (α:=GraphProblemInput) json with
              | Except.error msg => pure (Except.error ("Json does not match problem description" ++ msg))
              | Except.ok parsedProblem =>
                pure (GraphVerificationProblem.fromProblemInput parsedProblem)
  else pure (Except.error "File does not exist")

def main_dag (argsParsed: ArgsParsed): IO Unit := do
  match ← parseDagProblemFromJson argsParsed.programFileName with
  | Except.error e => IO.println e
  | Except.ok problem =>
    if argsParsed.complete = true
    then
      IO.println "Checking Modelhood..."
      match safe: problem.program.checkSafety with
      | Except.error msg => IO.println msg
      | Except.ok _ =>
        have safe': ∀ (r: Rule problem.helper.toSignature), r ∈ problem.program → r.isSafe := by
          rw [Program.checkSafety_iff_isSafe] at safe
          apply safe
        match checkDagModelhood problem safe' with
        | Except.error msg => IO.println ("Invalid result due to: " ++ msg )
        | Except.ok _ => IO.println "Valid result"
    else
      IO.println "Checking Proof Validity..."
      match checkDagValidityWithUnivDatabase problem with
      | Except.error msg => IO.println ("Invalid result due to: " ++ msg )
      | Except.ok _ => IO.println "Valid result"

def parseOrderedDagProblemFromJson (fileName: String): IO (Except String OrderedGraphVerificationProblem) := do
  let filePath := System.FilePath.mk fileName
  if ← filePath.pathExists
      then
        match Lean.Json.parse (← IO.FS.readFile filePath) with
          | Except.error msg => pure (Except.error ("Error parsing JSON " ++ msg))
          | Except.ok json =>
            match Lean.fromJson? (α:=OrderedGraphProblemInput) json with
              | Except.error msg => pure (Except.error ("Json does not match problem description" ++ msg))
              | Except.ok parsedProblem =>
                pure (OrderedGraphVerificationProblem.fromProblemInput parsedProblem)
  else pure (Except.error "File does not exist")

def main_ordered_dag (argsParsed: ArgsParsed): IO Unit := do
  match ← parseOrderedDagProblemFromJson argsParsed.programFileName with
  | Except.error e => IO.println e
  | Except.ok problem =>
    if argsParsed.complete = true
    then
      IO.println "Checking Modelhood..."
      match safe: problem.program.checkSafety with
      | Except.error msg => IO.println msg
      | Except.ok _ =>
        have safe': ∀ (r: Rule problem.helper.toSignature), r ∈ problem.program → r.isSafe := by
          rw [Program.checkSafety_iff_isSafe] at safe
          apply safe
        match checkOrderedGraphModelhood problem safe' with
        | Except.error msg => IO.println ("Invalid result due to: " ++ msg )
        | Except.ok _ => IO.println "Valid result"
    else
      IO.println "Checking Proof Validity..."
      match checkOrderedGraphValidityWithUnivDatabase problem with
      | Except.error msg => IO.println ("Invalid result due to: " ++ msg )
      | Except.ok _ => IO.println "Valid result"

def main(args: List String): IO Unit := do
  match parseArgs args with
  | Except.error e => IO.println e
  | Except.ok argsParsed =>
    if argsParsed.help = true
    then printHelp
    else
      match argsParsed.format with
      | InputFormat.trees => main_trees argsParsed
      | InputFormat.graph => main_dag argsParsed
      | InputFormat.orderedGraph => main_ordered_dag argsParsed
