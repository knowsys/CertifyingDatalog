# Transitive Closure Benchmark

This directory contains an example that computes the transitive closure along a long relational chain 
in three different ways; only expanding to the right, only expanding to the left, and expanding in both directions.
The example is inspired by <https://github.com/souffle-lang/benchmarks/tree/master/benchmarks/tc>.

## Usage

Note: The `tc.tree.json` file is gzipped. `gunzip` it before usage.

### Running the already generated input file 

- Build the Lean program in the root directory of this project using `lake build`. The binary is found here: `/build/bin/certifyingDatalog`
- In this directory, run `../../build/bin/certifyingDatalog [-g] <file>.(tree|graph).json`

### Generate Input Facts for Datalog Program 

- Install `ruby`
- Run `mkdir -p sources`
- Run `./gen_facts.rb > sources/R.csv`

### Building input files from the datalog program 

- Build the `nmo` binary from the `tracing-playground` branch: <https://github.com/knowsys/nemo/tree/tracing-playground>; Run `cargo b -r`; The binary can be found in `/path/to/nemo/target/release/nmo`.
- Install Python3 alongside the `rfc3987` package.
- Adjust the path to the `nmo` binary in `inputCreatorNemo.py`
- Run `nmo -so tc.rls` to create all reasoning ressult in the `result` directory.
- Run `python3 inputCreatorNemo.py`; This yields `tc.tree.json` and `tc.graph.json`.

