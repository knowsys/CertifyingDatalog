## Usage

This folder contains the code and data used in the diploma thesis.

### Running the already generated input file 

- Build the Lean program in the root directory of this project using `lake build`. The binary is found here: `/.lake/build/bin/certifyingDatalog`
- In this directory, run `../../.lake/build/bin/certifyingDatalog [-g] <file>.(tree|graph).json`

### Building input files from the datalog program 

- Build the `nmo` binary from the `tracing-playground` branch: <https://github.com/knowsys/nemo/tree/tracing-playground>; Run `cargo b -r`; The binary can be found in `/path/to/nemo/target/release/nmo`.
- Install Python3 alongside the `rfc3987` package.
- Adjust the path to the `nmo` binary in `inputCreatorNemo.py`
- In `experiments.py`are the experiments used in the thesis. Scenario (1) is started by `graphExperiments` and uses `tc.rls`, scenario (2) is started by `exponentialExample` and uses `ExponentialTC.rls` and scenario (3) is started by `galenExperiments` and uses `el-calc.rls`. The data in scenarios (1) and (2) is generated in `experiments.py` and the data in scenario (3) is in `data.tar` and taken from  <https://github.com/knowsys/nemo-examples/tree/main/examples/owl-el/from-preprocessed-csv>. It uses `inputCreatorNemo.py` to create the input files and `evalLogs.py` is used to combine the data from the logs for evaluation.