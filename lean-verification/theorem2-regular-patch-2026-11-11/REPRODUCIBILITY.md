# Lean 4 Reproducibility Record

## Spherical N-Series Area Law — Regular-Patch Theorem

Verification date: 2026-11-11

This directory contains the Lean 4 verification archive for
the fixed-parametrization, regular-patch fourth-order
spherical area law.

## Formalized mathematical result

Let F : R^2 -> R^3 be a C^5 parametrization whose
surface Jacobian is nonvanishing throughout the closed
unit parameter square.

Use a uniform N x N grid. Split each cell along its
lower-left to upper-right diagonal into two chordal
triangles, and let A_N be their total area.

The formalization establishes

    |A_N - (A + C2/N^2)| <= C/N^4

for sufficiently large N, where A is the integral of the
surface Jacobian and C2 is the coefficient formalized
in SphericalAreaLaw.lean.

It also proves the two-scale Richardson estimate

    |(4*A_(2N) - A_N)/3 - A| <= 5*C/(12*N^4).

The named Lean declarations are:

- BakerSpherical.AreaLaw.spherical_area_law
- BakerSpherical.AreaLaw.richardson_fourth_order

## Scope limitations

The present machine-checked result is restricted to
a fixed, regular parametrized patch.

It does not establish:

- Uniform asymptotics over a deformation parameter.
- The complete all-orders expansion in manuscript v2.4.
- Sixth-order or eighth-order Richardson results.
- Coordinate-singular polar-region cases.
- Arb-certified numerical constants.

The broader results in manuscript v2.4 remain written
mathematical arguments, not claims of Lean verification.

## Archived environment

Lean: leanprover/lean4:v4.36.0-rc2

Mathlib commit:
ccd6c8476363fc81f2e4bee2eeb1a62c99338549

The exact dependency pin is recorded in lake-manifest.json.
The project configuration and toolchain are included.

## Verification record

- 31 Lean source modules in the theorem's dependency closure.
- 31 corresponding release build logs.
- 126 declarations audited using #print axioms.
- Zero compiler errors in the release build logs.
- Zero sorryAx occurrences in those logs.
- Only propext, Classical.choice and Quot.sound
  appear in the recorded axiom dependencies.

The build of record was completed on the author's
Windows machine using the pinned Lean/Mathlib environment.

A separate fresh Linux clone verified that all 65 entries
in SHA256SUMS.txt matched their archived file bytes.
This independent checksum inspection does not, by itself,
constitute a fresh Lean compilation on Linux.

## Reproduction

Install the Lean toolchain through elan, using the
included lean-toolchain file.

From this directory, fetch the Mathlib dependencies
recorded in lake-manifest.json.

Compile the local Lean modules in dependency order
using the included lakefile.toml and the pinned Mathlib
revision. For each module, the basic invocation is:

    lake env lean ModuleName.lean

Local imports must be compiled before their dependents,
with their compiled .olean files available on Lean's
search path.

The original Windows release logs provide the reference
compilation and axiom-audit outputs.

Inspect the #print axioms declarations in the source
files to reproduce the dependency audit.

## Existing warnings

Lemma2Algebra.lean has two harmless linter warnings
concerning unused `cross` simp arguments at source
lines 43 and 52.

These are warnings, not compiler errors, and do not
invalidate the kernel-checked declarations.

The archived source and build logs have deliberately
not been modified to silence them.

## Archive integrity

SHA256SUMS.txt contains exactly 65 entries covering:

- 31 Lean source files.
- 31 release build logs.
- lakefile.toml
- lake-manifest.json
- lean-toolchain

REPRODUCIBILITY.md was added after the frozen verification
archive and is intentionally excluded from SHA256SUMS.txt.

Its contents and history are preserved by Git.

## Repository history

Original verification commit:
eecfc4cf9f5b4ebb29e648be0bc77379168e6fe3

Byte-preservation correction:
f02f10ea9244a7b8ed5bd063e5a57f0b27c5e09a

Repository:
https://github.com/CWBaker360/spherical-nseries-area-law

Branch: v2.4-draft
