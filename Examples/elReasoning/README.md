# OWL EL Reasoning on preprocessed ontologies

This example shows how Nemo can be used to implement the core reasoning algorithm for the ontology language OWL EL,
based on preprocessed input files (in CSV format) that encode the ontology in a relational format.

The rules file `el-calc.rls` contains a small number of plain Datalog rules that do the work.
The ontology is read from the `data` directory, where a preprocessed version of the Galen EL ontology is found.
Other ontologies can also be used: suitable preprocessed files can also be created with Nemo, using the 
[logic program for EL reasoning from OWL/RDF](https://github.com/knowsys/nemo-examples/tree/main/examples/owl-el/from-owl-rdf).

The example has been taken from <https://github.com/knowsys/nemo-examples/tree/main/examples/owl-el/from-preprocessed-csv>.

## Usage

### Running the already generated input file 

- Build the Lean program in the root directory of this project using `lake build`. The binary is found here: `/build/bin/certifyingDatalog`

### Building input files from the datalog program 

- Build the `nmo` binary from the `tracing-playground` branch: <https://github.com/knowsys/nemo/tree/tracing-playground>; Run `cargo b -r`; The binary can be found in `/path/to/nemo/target/release/nmo`.
- Install Python3 alongside the `rfc3987` package.
- Adjust the path to the `nmo` binary in `inputCreatorNemo.py`
- Run `nmo -so transitiveClosureToyExample.rls` to create all reasoning ressult in the `result` directory.
- Run `python3 experiments.py`; This yields `tc.tree.json` and `tc.graph.json` based on 1000 randomly selected facts from the `result` directory. (The script also executes `/build/bin/certifyingDatalog` and measures execution times but this can be done manually afterwards or even based on the already provided `tc.tree.json` and `tc.graph.json` files to reproduce the results from the paper.)

