# Transitive Closure Benchmark

This directory contains an example that computes the transitive closure along a long relational chain 
in three different ways; only expanding to the right, only expanding to the left, and expanding in both directions.
The example is inspired by <https://github.com/souffle-lang/benchmarks/tree/master/benchmarks/tc>.

## Usage

### Running the already generated input file 

- Build the Lean program in the root directory of this project using `lake build`. The binary is found here: `/.lake/build/bin/certifyingDatalog`
- In this directory, run `../../.lake/build/bin/certifyingDatalog [-g/-o] <file>.(tree|graph|ograph).json`
- To run a completeness check, you can add the `-c` parameter. For the paper, we check completeness with the `ograph` input.

### Generate Input Facts for Datalog Program 

- Install `ruby`
- Run `mkdir -p sources`
- Run `./gen_facts.rb > sources/edge.csv`

### Building input files from the datalog program 

- Build the `nmo` binary from <https://github.com/knowsys/nemo>. For the latest experiments, we used <https://github.com/knowsys/nemo/releases/tag/v0.5.1>. Run `cargo b -r`. The binary can be found in `/path/to/nemo/target/release/nmo`.
- Install Python3 alongside the `rfc3987` package.
- Adjust the path to the `nmo` binary in `inputCreatorNemo.py`
- Run `python3 inputCreatorNemo.py`; This yields `tc.tree.json`, `tc.graph.json` and `tc.ograph.json`.

