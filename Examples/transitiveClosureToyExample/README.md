# Standalone Toy Example 

This directory contains a toy example for demonstration of the validation process. The "handcrafted" files alread contain inputs that can be passed to the Lean program.
The check will come out valid or invalid (as the file names indicate).

These handcrafted examples are based on the datalog program `transitiveClosureToyExample.rls`. 

## Usage

### Running the already generated input file 

- Build the Lean program in the root directory of this project using `lake build`. The binary is found here: `/.lake/build/bin/certifyingDatalog`
- In this directory, run `../../.lake/build/bin/certifyingDatalog [-g/-o] <file>.(tree|graph|ograph).json`, using `-g` with the "graph" variants, `-o` with the "ograph" variants, and omitting both with the "tree" variants.
- To run a completeness check, you can add the `-c` parameter (for each of the inputs). For example, the completeness check for `handcraftedToyExampleVariant.valid.tree.json` will fail, whereas the completeness check for `handcraftedToyExampleVariant.valid.ograph.json` is successful.

### Building input files from the Datalog program 

- Build the `nmo` binary from <https://github.com/knowsys/nemo>. For the latest experiments, we used <https://github.com/knowsys/nemo/releases/tag/v0.5.1>. Run `cargo b -r`. The binary can be found in `/path/to/nemo/target/release/nmo`.
- Install Python3 alongside the `rfc3987` package.
- Adjust the path to the `nmo` binary in `inputCreatorNemo.py`
- Run `nmo -e idb -o transitiveClosureToyExample.rls` to create all reasoning result in the `result` directory.
- Run `python3 inputCreatorNemo.py`; this yields `transitiveClosureToyExample.tree.json`, `transitiveClosureToyExample.graph.json` and `transitiveClosureToyExample.ograph.json`
  (these are the files that have been modified to obtain the handcrafted examples).

