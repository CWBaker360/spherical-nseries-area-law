# Spherical N-Series Area Law — v2.4 Draft

Date: 2026-11-10

Status: Research draft. Not independently referee-certified.

This branch contains the revised manuscript, its LaTeX source,
the uniformity-proof supplement, symbolic verification scripts,
numerical tests, and the reported Arb interval certificate.

## Verification

- The local q2 coefficient identity passed exact symbolic checks.
- Binary64 Gauss-Legendre quadrature corroborated the coefficient.
- The author executed the Arb certification on Windows.
- The reported Arb result was:
  C2'(0) enclosure: [-0.000680779112122198 +/- 1.96e-19]
  C2'(0) < 0 certified: True

These checks do not replace an independent mathematical review.

## Prior art

Even-power chordal-surface expansions and generalized Richardson
extrapolation are classical. The manuscript identifies the relevant
predecessors and restricts its potential novelty claims accordingly.

## Outstanding

- Independent human review of Theorem 2 and Lemma 2.
- Final bibliographic and scholarly novelty assessment.
- Verification of the complete release archive and checksums.

This draft does not supersede the existing public release.
