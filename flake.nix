{
  description = "Machine-checked denotational semantics of double-entry accounting, with a bisimulation oracle for Ledger implementations";

  inputs = {
    # This nixpkgs revision provides lean4 4.30.0.  The pin must agree
    # with ./lean-toolchain (leanprover/lean4:v4.30.0) and with the
    # Mathlib revision in ./lake-manifest.json.  Change the three
    # together, then refresh the outputHash of `deps` below.
    nixpkgs.url = "github:NixOS/nixpkgs/ffb3c9b700e759be2ef13237c9d8f953b32a1e46";
  };

  outputs = { self, nixpkgs }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      forAllSystems = f: nixpkgs.lib.genAttrs systems (system: f system);
      pkgsFor = forAllSystems (system: import nixpkgs { inherit system; });
    in
    {
      packages = forAllSystems (system:
        let
          pkgs = pkgsFor.${system};

          # The full `.lake/packages` dependency tree as a fixed-output
          # derivation.  Lake clones each dependency at the revision in
          # lake-manifest.json and downloads the prebuilt Mathlib
          # artifact cache, so no build of Mathlib occurs.  The output
          # is normalized so that its hash is stable across builders
          # and platforms: git metadata and natively compiled artifacts
          # are removed, and absolute paths in the Lake replay logs are
          # rewritten to fixed tokens.  The paths are logs only; Lake
          # keys rebuilds on content hashes.  After a Lean or Mathlib
          # upgrade, run `nix build .#deps` and copy the new hash from
          # the mismatch report.
          deps = pkgs.stdenv.mkDerivation {
            pname = "ledger-semantics-deps";
            version = "mathlib-v4.30.0";

            src = self;

            nativeBuildInputs = [ pkgs.lean4 pkgs.git pkgs.curl pkgs.cacert ];

            outputHashAlgo = "sha256";
            outputHashMode = "recursive";
            outputHash = "sha256-qnUoEuhFVZk3BlEe3Jl85UDvvrNbUevifTVMyq7mnPU=";

            buildCommand = ''
              cp -r $src work
              chmod -R u+w work
              cd work
              export HOME=$TMPDIR
              export SSL_CERT_FILE=${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt
              export GIT_SSL_CAINFO=$SSL_CERT_FILE
              export NIX_SSL_CERT_FILE=$SSL_CERT_FILE

              lake exe cache get
              lake build

              find .lake/packages -name .git -prune -exec rm -rf {} +
              rm -rf .lake/packages/*/.lake/build/bin
              find .lake/packages \( -name '*.o' -o -name '*.dylib' \
                -o -name '*.so' \) -delete
              grep -rlI "$PWD" .lake/packages | while read -r f; do
                sed -i "s|$PWD|@ledger-semantics-work@|g" "$f"
              done
              grep -rlI '/nix/store/' .lake/packages | while read -r f; do
                sed -i 's|/nix/store/[a-z0-9]\{32\}-|/nix/store/@scrubbed@-|g' "$f"
              done

              mv .lake/packages $out
            '';
          };

          # The compiled oracle: this repository with its modules built
          # and dependencies linked from `deps`.  Building it checks
          # every proof (the lakefile turns warnings, and therefore
          # `sorry`, into errors).  The output is a read-only tree; run
          # the oracle in place with:
          #   lake env lean --run Ledger/Driver.lean FILE.dat ...
          oracle = pkgs.stdenv.mkDerivation {
            pname = "ledger-semantics-oracle";
            version = "0.1.0-${self.shortRev or "dirty"}";

            src = self;

            nativeBuildInputs = [ pkgs.lean4 ];

            buildCommand = ''
              cp -r $src $out
              chmod -R u+w $out
              mkdir -p $out/.lake
              ln -s ${deps} $out/.lake/packages
              cd $out
              export HOME=$TMPDIR
              lake build
            '';
          };
        in {
          inherit deps oracle;
          # The exact toolchain, for downstream flakes that run the
          # oracle (the C++ Ledger repository consumes this).
          lean = pkgs.lean4;
          default = oracle;
        });

      checks = forAllSystems (system: {
        oracle = self.packages.${system}.oracle;
      });

      devShells = forAllSystems (system:
        let
          pkgs = pkgsFor.${system};
        in {
          default = pkgs.mkShell {
            name = "ledger-semantics";
            buildInputs = [ pkgs.lean4 ];
          };
        });
    };
}
