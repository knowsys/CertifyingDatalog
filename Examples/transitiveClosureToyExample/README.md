# Standalone Toy Example 

This directory contains a toy example for demonstration of the validation process. The "handcrafted" files alread contain inputs that can be passed to the lean program. The check will come out valid or invalid (as the names indicate).

These handcrafted examples are based on the datalog program `transitiveClosureToyExample.rls`. 

## Usage

### Running the already generated input file 

- Build the Lean program in the root directory of this project using `lake build`. The binary is found here: `/build/bin/certifyingDatalog`

### Building input files from the datalog program 

- Build the `nmo` binary from the `tracing-playground` branch: <https://github.com/knowsys/nemo/tree/tracing-playground>; Run `cargo b -r`; The binary can be found in `/path/to/nemo/target/release/nmo`.
- Install Python3 alongside the `rfc3987` package.
- Adjust the path to the `nmo` binary in `inputCreatorNemo.py`
- Run `python3 inputCreatorNemo.py`; This yields `transitiveClosureToyExample.tree.json` and `transitiveClosureToyExample.graph.json`. (These are the files that have been modified to obtain the handcrafted examples.)

### Note on `experiments.py`

The `experiments.py` script can in general be used to pick a number of facts from an initial reasoning result at random, create input files for them and execute the Lean program to verify them. We do not encourage usage of this file in the scope of this example but it should work nonetheless.

