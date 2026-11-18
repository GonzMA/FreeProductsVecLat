# Proof progress

All 49 numbered results and all three numbered definitions in the current
vector-lattices draft have corresponding formalizations. The
[README correspondence tables](README.md#correspondence-with-the-paper) use the
current numbering, with separate Definitions 6.5 and 6.6 for relative injectivity
and universal disposition. The historical manual comparison of statements and
proof ideas is in [DraftCoverageAudit.txt](FreeProducts/DraftCoverageAudit.txt).
Compilation, source-gap counting, and transitive axiom checking are separate checks.

## Completed draft material

- Ordinary vector-lattice free products, quotients, pushouts, and preservation of injectivity.
- Closed-cone representation and categorical cone duality.
- Polyhedral cone criteria, projectivity, and Archimedean free-product obstructions.
- Archimedeanization, the generated join representation, and embeddings assembled from finite stages.
- Banach completion, order density, regularity, and preservation of injectivity.
- Concrete counterexamples, including the sphere/ball construction and scalar zero-set evaluations.
- Countable prime spectra, extension and injectivity results, transfinite constructions, and cardinal bounds.
- Concrete tensor products and the positive pairing used in the continuous-function arguments.

The separate [axiom audit](scripts/ProofAudit.lean) contains 97 public declarations.
Their dependencies must use only `propext`, `Classical.choice`, and `Quot.sound`.
Private helpers used by those declarations are checked transitively. The
mathematical library imports its modules directly; CI runs the audit after the
ordinary build with `lake env lean scripts/ProofAudit.lean`.

## Remaining ancillary obligations

Two unfinished ancillary statements have been temporarily removed from the Banach
free-product modules:

- `BanachLattice.complemented_l1_in_prod_imp`.
- `BanachLattice.FreeProduct.isOrderContinuousNorm_dual`.

The tensor constructions now live in the `TensorProducts/` modules. The old
interface file and its unfinished declarations have been removed.

The generated inventory in [FORMALIZATION.md](FORMALIZATION.md) recursively checks
the reorganized source folders and reports zero explicit proof placeholders.
The join representation now uses the explicit normalized-character homeomorphism
and the library's representation of complete principal ideals.

## Maintaining the checks

Preserve theorem hypotheses and the draft's proof ideas. After changing sources or
audit targets, run `python3 scripts/audit_source.py`, `lake build`,
`lake env lean scripts/ProofAudit.lean`, and `python3 scripts/audit_source.py --check`.

The manuscript, private reference library, and experimental files are not exported.
