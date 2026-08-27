# AGENTS.md

Operating instructions for AI agents, and for the people directing
them, when working in this repository. Read the README first for
what the mathematics says; this file is about how to change the code
without damaging what it proves.

## What you are holding

This repository is a machine-checked semantics for double-entry
accounting together with an executable oracle derived from it. The
C++ Ledger project pins this repository twice, as a git submodule
and as a Nix flake input, and replays its entire test suite through
the oracle in continuous integration. A change here therefore gates
another project's CI. Treat every edit as a change to a published
specification, because that is what it is.

## The two layers, and the rule between them

The specification layer defines meaning and proves laws:

    Basic → Accounts → Groupoid → Labels, Hierarchy, Valuation
          → Derivation, Prices → Theorems → Derived, Free, Trivial
          → TimedPrices, and Free → Pacioli

The executable layer reads journals and computes balances:

    Basic → Parse → Journal, and Pacioli → Oracle → Register, Driver

`Driver` is the only module that joins the two sides. The
specification layer never imports the executable layer, and that
direction must be preserved; it was verified by import scan and any
change that reverses an edge is wrong regardless of whether it
builds. `Journal.lean` is the largest file in the repository by
design: it records the observed conventions of the C++
implementation, while the theory above it stays small. Know which
layer you are editing. A change to `Groupoid` or `Theorems` is a
change to the mathematics and needs a proof. A change to `Parse` or
`Journal` is a claim about C++ behavior and needs a witness.

## Non-negotiables

The lakefile turns warnings into errors, so a `sorry` fails the
build, and `autoImplicit` is off, so a typo is an error instead of a
silently quantified variable. Never weaken either setting, and never
disable a lint to make a proof pass.

The proofs close with three axioms only: `propext`,
`Classical.choice`, `Quot.sound`. After changing the specification
layer, confirm the budget with `#print axioms <theorem>` on what you
touched. A proof that needs more axioms, `native_decide`, or an
`unsafe` escape is a redesign question, not a commit.

Every rule in the executable layer cites the regression test or the
C++ source location that forced it, in a comment beside the rule. A
convention without a witness does not merge. When the C++ project
changes a behavior, the bisimulation fails until the rule here is
updated together with the new witness; that failure is the system
working.

The oracle is interpreted. There is no `lean_exe`, and adding one is
forbidden twice over: it would compile C for all of Mathlib, and it
would put a compiler between the checked definitions and what
executes. `Gen` emits property-test journals and must never author
expected results. Do not commit `.lake/` or `result`.

## Building and testing

With Nix, from the repository root:

    nix build            # builds the oracle; a green build checks every proof
    nix develop          # shell with the pinned toolchain (lean, lake, git)

Without Nix, install Lean 4.30.0 through elan, then:

    lake exe cache get   # prebuilt Mathlib artifacts, once
    lake build           # compiles and checks everything, a few minutes warm

There is no separate test suite in this repository. The build is the
proof check, and CI adds one smoke test of the driver protocol. Run
the oracle against a journal like this:

    lake env lean --run Ledger/Driver.lean FILE.dat ...

Output: `== PATH` opens each file's section; rows are
`COMMODITY|AMOUNT|ACCOUNT`, sorted, amounts in canonical decimals;
`%% dc COMM` declares a learned decimal-comma style (`*` names the
null commodity); `!! ERROR reason` reports a rejected file and
nothing else. Flags before a path apply to that file alone:
`--decimal-comma`, `--recursive-aliases`, `--now DATE`,
`--input-date-format FORMAT`. This protocol is a compatibility
surface. The C++ harness and any third-party comparator parse it, so
changing it is a breaking change to be made deliberately and
announced, never as a side effect.

## The pins, and how to move them

Four things must agree at all times: `lean-toolchain`
(leanprover/lean4:v4.30.0), the Mathlib revision in
`lake-manifest.json`, the nixpkgs revision in `flake.nix` (chosen so
that its `lean4` matches the toolchain), and the `outputHash` values
of the `deps` fixed-output derivation. To upgrade Lean or Mathlib,
change the first three together, then refresh the hashes: set each
hash to a placeholder, run `nix build .#deps`, and copy the true
hash from the mismatch report. Nix registers the fetched output even
on mismatch, so the rebuild after pinning is instant. The hash is
declared per kernel because Darwin and Linux fetch measurably
different trees (the working hypothesis is case-insensitive
filesystems merging case-colliding paths); refresh both, each from a
machine of that kernel or from CI.

The downstream side of the same discipline: when this repository's
main moves, the C++ repository must bump its submodule and its
flake.lock in one commit. Never let the two pins drift apart.

## Traps that have already cost time

Lake validates a git-type dependency by querying its checkout with
the git binary, and it treats a failed query as a changed URL,
which triggers a re-clone that a read-only store path cannot
satisfy. The `deps` derivation therefore gives every package a
minimal deterministic `.git` skeleton, and anything that runs Lake
against a store-owned tree needs git on PATH plus the ownership
check quieted:

    export GIT_CONFIG_COUNT=1
    export GIT_CONFIG_KEY_0=safe.directory
    export GIT_CONFIG_VALUE_0="*"

Warnings that a package "has local changes" come from the index-less
skeletons and are noise. The built oracle tree is read-only and
`lake env lean --run` works there unmodified; nothing needs to be
copied out of the store. A doc-comment edit in a low module such as
`Groupoid` re-elaborates everything above it, which takes minutes
and is progress, not a hang. When editing prose programmatically,
never put backtick-quoted command names inside a double-quoted shell
string; the shell executes them.

## If you are basing your own testing regimen on this

The README describes the five-part bisimulation procedure that
brought the C++ implementation to exact agreement; it transfers to
any implementation. The short form of the contract: compare your
implementation's balances against the oracle over your entire test
corpus, classify non-comparable files into named bins before
comparing, treat everything the oracle cannot read as a visible skip
and never a pass, replay a planted defect on every run so the
comparator is proved able to fail, and record in every result the
revisions of both sides together with what the comparison does not
cover. Divergences are the product. One that exposes your defect you
fix; one that exposes an unrecorded convention belongs here as a
pull request adding the rule with its witness.

The oracle compares balances. Register rows, market valuation, and
lot matching are specified in the theory and not yet bisimulated, so
do not claim coverage of them on the strength of this oracle.

## Style for prose and commits

Documentation in this repository is written in a measured, formal
register: no contractions, no em-dashes, no marketing vocabulary,
sentences of ordinary varied length in flowing paragraphs, and
rationale stated before procedure. Commit messages explain what
forced the change, name the witnesses or measurements involved, and
claim only what was verified; where a claim rests on an exit code or
a log, say which.
