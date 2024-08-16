# Certifying Datalog

This repo contains a checker for Datalog proof trees and proofs encoded as directed acyclic graphs.
The checker is implemented and formally verified in [Lean 4](https://github.com/leanprover/lean4).
For more details on the usage, take a look into the (subdirectories of the) `Examples` directory.

## Notes on Setup

Using [`elan`](https://github.com/leanprover/elan) / `lake`:  
```
lake build
```
This will download mathlib4 and build the project.  
To prevent building mathlib yourself, you can run the following to fetch precompiled dependencies.
```
lake exe cache get
```
(You still need to run `lake build` afterwards.)

The resulting executable is found here: `.lake/build/bin/certifyingDatalog`

## License

This project is licensed under either of

- Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or
  https://www.apache.org/licenses/LICENSE-2.0)
- MIT license ([LICENSE-MIT](LICENSE-MIT) or
  https://opensource.org/licenses/MIT)

at your option.

