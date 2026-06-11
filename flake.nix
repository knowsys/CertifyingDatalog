{
  description = "A certified checker for Datalog entailments, written in Lean";

  inputs.nixpkgs.url = "https://channels.nixos.org/nixos-26.05/nixexprs.tar.xz";

  outputs = { self, nixpkgs }:
    let
      forAllSystems = function:
        nixpkgs.lib.genAttrs ["x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin"] (system: function nixpkgs.legacyPackages.${system});
    in {
      devShells = forAllSystems (pkgs: {
        default = pkgs.mkShell {
          packages = [
            pkgs.elan
            (pkgs.python3.withPackages (python-pkgs: [
              python-pkgs.rfc3987
            ]))
            pkgs.ruby
          ];
        };
      });
    };
}
