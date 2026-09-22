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

      # The commit behind the release named in ./lean-toolchain
      # (leanprover/lean4:v4.30.0).  Lake keys every build trace on the
      # compiler's githash, and the Mathlib artifact cache was produced
      # by the official release, whose `lean --githash` is this commit;
      # nixpkgs' lean4 is built from the same source but reports the
      # literal tag ("v4.30.0") instead.  Without the override Lake
      # judges every fetched artifact stale and `lake build Mathlib`
      # recompiles all of Mathlib — four hours on a CI runner.  Lake
      # honours LEAN_GITHASH as the detected hash (Lake/Config/Env.lean),
      # so every lake invocation below sets it.  Move it together with
      # the other pins.
      leanGithash = "d024af099ca4bf2c86f649261ebf59565dc8c622";
    in
    {
      packages = forAllSystems (system:
        let
          pkgs = pkgsFor.${system};

          # The full `.lake/packages` dependency tree as a fixed-output
          # derivation.  Lake clones each dependency at the revision in
          # lake-manifest.json and downloads the prebuilt Mathlib
          # artifact cache; with LEAN_GITHASH set the `lake build
          # Mathlib` that follows replays those artifacts instead of
          # recompiling them, so the derivation is a download plus a
          # few minutes of validation.  The output is normalized so
          # that its hash is the same on every builder and platform:
          # git metadata and every natively compiled artifact are
          # removed, and absolute paths in the Lake replay logs are
          # rewritten to fixed tokens.  The paths are logs only; Lake
          # keys rebuilds on content hashes.  After a Lean or Mathlib
          # upgrade, run `nix build .#deps` and copy the new hash from
          # the mismatch report.
          deps = pkgs.stdenv.mkDerivation {
            pname = "ledger-semantics-deps";
            version = "mathlib-v4.30.0";

            src = self;

            nativeBuildInputs =
              [ pkgs.lean4 pkgs.git pkgs.curl pkgs.cacert pkgs.jq ];

            outputHashAlgo = "sha256";
            outputHashMode = "recursive";
            # One hash for every platform.  The normalized tree has
            # been measured byte-identical on x86_64-linux,
            # aarch64-linux and aarch64-darwin: the only files that
            # ever differed were the natively compiled products of
            # `lake exe cache`, which the cleanup below removes.
            outputHash = "sha256-NGu7QxR0rLAqWvdHMEXBiBjdNWTKP5a3lLW9fQnslic=";

            buildCommand = ''
              cp -r $src work
              chmod -R u+w work
              cd work
              export HOME=$TMPDIR
              export SSL_CERT_FILE=${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt
              export GIT_SSL_CAINFO=$SSL_CERT_FILE
              export NIX_SSL_CERT_FILE=$SSL_CERT_FILE
              export LEAN_GITHASH=${leanGithash}

              lake exe cache get
              # Validate EVERY Mathlib module while this tree is still
              # writable, rebuilding any whose fetched artifact fails
              # Lake's trace check.  With LEAN_GITHASH matching the
              # toolchain that produced the cache this is a replay;
              # without it every module failed the check, only the
              # import closure was rebuilt, and an added import
              # (Monoidal.Braided) then made Lake rebuild inside the
              # read-only store.  Validating all of Mathlib here keeps
              # the store tree valid for any future import.
              lake build Mathlib
              lake build

              find .lake/packages -name .git -prune -exec rm -rf {} +
              rm -rf .lake/packages/*/.lake/build/bin
              # Everything that differs between platforms is a product of
              # `lake exe cache get` compiling Mathlib's `cache`
              # executable natively: the `.c.o.export` objects (with
              # their .hash and .trace records) under build/ir, and the
              # `Cache.*` modules' own artifacts, whose traces embed the
              # native facet.  The interpreted oracle imports none of it,
              # so with these gone the tree, and hence the hash, is the
              # same on every platform.
              find .lake/packages \( -name '*.o' -o -name '*.o.*' \
                -o -name '*.dylib' -o -name '*.so' \) -delete
              rm -rf .lake/packages/mathlib/.lake/build/lib/lean/Cache \
                .lake/packages/mathlib/.lake/build/ir/Cache
              # A grep that matches nothing exits 1, which under the
              # builder's pipefail would fail the derivation; nothing
              # left to scrub is success.
              { grep -rlI "$PWD" .lake/packages || true; } | while read -r f; do
                sed -i "s|$PWD|@ledger-semantics-work@|g" "$f"
              done
              { grep -rlI '/nix/store/' .lake/packages || true; } | while read -r f; do
                sed -i 's|/nix/store/[a-z0-9]\{32\}-|/nix/store/@scrubbed@-|g' "$f"
              done

              # Lake validates a git-type dependency by reading the
              # checkout's .git (remote URL and HEAD revision) and
              # re-clones on any mismatch.  Real .git directories are
              # not reproducible, so each package instead receives a
              # minimal deterministic skeleton: a detached HEAD at the
              # manifest revision and a config naming the origin URL.
              # That satisfies the check; nothing else reads .git.
              jq -r '.packages[] | .name + " " + .rev + " " + .url' \
                  lake-manifest.json | while read -r name rev url; do
                d=".lake/packages/$name/.git"
                mkdir -p "$d/objects" "$d/refs"
                printf '%s\n' "$rev" > "$d/HEAD"
                printf '[core]\n\trepositoryformatversion = 0\n\tbare = false\n[remote "origin"]\n\turl = %s\n' \
                  "$url" > "$d/config"
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

            # Lake validates each dependency by querying its .git with
            # the git binary; the skeletons in `deps` answer the query,
            # and safe.directory quiets git's ownership check for
            # store-owned paths.  Without either, Lake concludes the
            # URL changed and attempts a re-clone.
            nativeBuildInputs = [ pkgs.lean4 pkgs.git ];

            buildCommand = ''
              cp -r $src $out
              chmod -R u+w $out
              mkdir -p $out/.lake
              ln -s ${deps} $out/.lake/packages
              cd $out
              export HOME=$TMPDIR
              export GIT_CONFIG_COUNT=1
              export GIT_CONFIG_KEY_0=safe.directory
              export GIT_CONFIG_VALUE_0="*"
              export LEAN_GITHASH=${leanGithash}
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
            buildInputs = [ pkgs.lean4 pkgs.git ];
            # Running the oracle from the Nix store (`lake env lean
            # --run` inside the built tree) needs git's ownership
            # check quieted; see the oracle derivation.
            shellHook = ''
              export GIT_CONFIG_COUNT=1
              export GIT_CONFIG_KEY_0=safe.directory
              export GIT_CONFIG_VALUE_0="*"
              export LEAN_GITHASH=${leanGithash}
            '';
          };
        });
    };
}
