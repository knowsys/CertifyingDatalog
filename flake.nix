{
  description = "A certified checker for Datalog entailments, written in Lean";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.05";
  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem
      (system:
        let pkgs = nixpkgs.legacyPackages.${system}; in
        {
          devShells.default = pkgs.mkShell {
            packages = [
              pkgs.elan
              pkgs.python3
              pkgs.python311Packages.rfc3987
              pkgs.ruby
            ];
          };
        }
      );
}
