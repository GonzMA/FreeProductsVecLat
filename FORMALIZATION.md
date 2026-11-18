# Formalization scope and source inventory

This repository contains the current formalization of the free-products draft.
The manuscript has 49 numbered results and three numbered definitions; see the
[current correspondence tables](README.md#correspondence-with-the-paper).
The manual statement and proof comparison is recorded in
[DraftCoverageAudit.txt](FreeProducts/DraftCoverageAudit.txt), whose numbering
predates the split of relative injectivity and universal disposition into
Definitions 6.5 and 6.6.

## Sources and dependency pins

The mathematical modules are exported from the reorganized `FreeProducts/` working
folder of the local BanLat checkout. The project pins public BanLat commit
`c3c5e1bfc4b2ae61d911aa63d331b9b05a5107d6` and Lean `v4.35.0`.
Mathlib and its transitive dependencies are locked in `lake-manifest.json`.

The tensor construction is developed in `TensorProducts/Bimorphisms.lean`,
`TensorProducts/Archimedean.lean`, and `TensorProducts/Banach.lean`. The generated
root `FreeProducts.lean` imports these and all other mathematical modules directly.
The former standalone interface and the import-only compatibility files have
been removed.

## Correspondence with the draft

| Directory | Scope |
|---|---|
| `VectorLattice/` | Ordinary vector-lattice free products, quotients, prime ideals, amalgamation, and embeddings |
| `BanachLattice/` | Banach-lattice free products, the join representation, and stability |
| `AVLvsVL/` | Closed-cone representation, duality, polyhedral covering, projectivity, and Archimedean criteria |
| `Archimedean/` | Archimedeanization, join sublattices, colimits, and embeddings |
| `TensorProducts/` | Concrete tensor construction, norm, completion, and positive extension |
| `Consequences/` | Continuous-function embeddings, Banach completion, principal-ideal localization, order density, regularity, and injectivity |
| `CountableSpectra/` | Countable prime spectra, extension, and transfinite constructions |
| `Counterexamples/` | Counterexamples and their concrete constructions |

## What the checks establish

1. `lake build` compiles the mathematical library. Its generated root module,
   `FreeProducts.lean`, imports all mathematical modules directly.
2. After the build, `lake env lean scripts/ProofAudit.lean` separately checks
   97 public declarations transitively and rejects all axioms except `propext`,
   `Classical.choice`, and `Quot.sound`. CI runs this audit after compilation.
3. `python3 scripts/audit_source.py --check` verifies the generated root imports,
   inventory, and audit module. Source counting excludes comments and strings.
4. The correspondence report is a manual mathematical comparison, not a
   machine-checked translation of the PDF.

The inventory recursively includes all mathematical modules in the subject folders. It excludes dependency
packages, generated Lean declarations, and audit machinery.

<!-- BEGIN SOURCE INVENTORY -->
## Source inventory

**0 explicit proof placeholders** across 50 mathematical modules.
Comments and strings are excluded. A gap-free source body does not certify its
dependencies; only registered strict targets are checked transitively by Lean.

| Module | Declarations | Explicit placeholders |
|---|---:|---:|
| [AVLvsVL/Classical/ConeRepresentation](FreeProducts/AVLvsVL/Classical/ConeRepresentation.lean) | 30 | 0 |
| [AVLvsVL/Classical/Duality](FreeProducts/AVLvsVL/Classical/Duality.lean) | 14 | 0 |
| [AVLvsVL/Classical/FreeFunctions](FreeProducts/AVLvsVL/Classical/FreeFunctions.lean) | 25 | 0 |
| [AVLvsVL/Classical/PolyhedralGeometry](FreeProducts/AVLvsVL/Classical/PolyhedralGeometry.lean) | 23 | 0 |
| [AVLvsVL/Classical/Projectivity](FreeProducts/AVLvsVL/Classical/Projectivity.lean) | 22 | 0 |
| [AVLvsVL/Classical/Retractions](FreeProducts/AVLvsVL/Classical/Retractions.lean) | 7 | 0 |
| [AVLvsVL/Coproducts/CoveringCriterion](FreeProducts/AVLvsVL/Coproducts/CoveringCriterion.lean) | 16 | 0 |
| [AVLvsVL/Coproducts/Equivalences](FreeProducts/AVLvsVL/Coproducts/Equivalences.lean) | 11 | 0 |
| [AVLvsVL/Coproducts/Models](FreeProducts/AVLvsVL/Coproducts/Models.lean) | 28 | 0 |
| [AVLvsVL/Coproducts/NonPolyhedralPartner](FreeProducts/AVLvsVL/Coproducts/NonPolyhedralPartner.lean) | 8 | 0 |
| [Archimedean/Archimedeanization](FreeProducts/Archimedean/Archimedeanization.lean) | 11 | 0 |
| [Archimedean/Basic](FreeProducts/Archimedean/Basic.lean) | 32 | 0 |
| [Archimedean/DirectedLimits](FreeProducts/Archimedean/DirectedLimits.lean) | 13 | 0 |
| [Archimedean/Embeddings](FreeProducts/Archimedean/Embeddings.lean) | 23 | 0 |
| [BanachLattice/Basic](FreeProducts/BanachLattice/Basic.lean) | 28 | 0 |
| [BanachLattice/Join](FreeProducts/BanachLattice/Join.lean) | 43 | 0 |
| [BanachLattice/Stability](FreeProducts/BanachLattice/Stability.lean) | 14 | 0 |
| [Consequences/BinaryOrder](FreeProducts/Consequences/BinaryOrder.lean) | 15 | 0 |
| [Consequences/ContinuousFunctionEmbeddings](FreeProducts/Consequences/ContinuousFunctionEmbeddings.lean) | 18 | 0 |
| [Consequences/ContinuousFunctionOrder](FreeProducts/Consequences/ContinuousFunctionOrder.lean) | 13 | 0 |
| [Consequences/Families](FreeProducts/Consequences/Families.lean) | 20 | 0 |
| [Consequences/NormAndCompletion](FreeProducts/Consequences/NormAndCompletion.lean) | 35 | 0 |
| [Consequences/PrincipalLocalization](FreeProducts/Consequences/PrincipalLocalization.lean) | 16 | 0 |
| [CountableSpectra/Basic](FreeProducts/CountableSpectra/Basic.lean) | 43 | 0 |
| [CountableSpectra/Colexicographic](FreeProducts/CountableSpectra/Colexicographic.lean) | 39 | 0 |
| [CountableSpectra/Existence](FreeProducts/CountableSpectra/Existence.lean) | 19 | 0 |
| [CountableSpectra/InjectiveProperties](FreeProducts/CountableSpectra/InjectiveProperties.lean) | 37 | 0 |
| [CountableSpectra/OrderedExtension](FreeProducts/CountableSpectra/OrderedExtension.lean) | 32 | 0 |
| [CountableSpectra/TransfiniteConstruction](FreeProducts/CountableSpectra/TransfiniteConstruction.lean) | 27 | 0 |
| [CountableSpectra/Ultrapowers](FreeProducts/CountableSpectra/Ultrapowers.lean) | 16 | 0 |
| [Counterexamples/ArchimedeanDisposition](FreeProducts/Counterexamples/ArchimedeanDisposition.lean) | 9 | 0 |
| [Counterexamples/Auxiliary](FreeProducts/Counterexamples/Auxiliary.lean) | 3 | 0 |
| [Counterexamples/CountableSpectrumPushout](FreeProducts/Counterexamples/CountableSpectrumPushout.lean) | 3 | 0 |
| [Counterexamples/FreeBanachComparison](FreeProducts/Counterexamples/FreeBanachComparison.lean) | 54 | 0 |
| [Counterexamples/FreeProductSpectrum](FreeProducts/Counterexamples/FreeProductSpectrum.lean) | 2 | 0 |
| [Counterexamples/HyperrealDisposition](FreeProducts/Counterexamples/HyperrealDisposition.lean) | 2 | 0 |
| [Counterexamples/IncreasingUnionSpectrum](FreeProducts/Counterexamples/IncreasingUnionSpectrum.lean) | 4 | 0 |
| [Counterexamples/LexicographicSpectrum](FreeProducts/Counterexamples/LexicographicSpectrum.lean) | 6 | 0 |
| [Counterexamples/LocalProjectivity](FreeProducts/Counterexamples/LocalProjectivity.lean) | 19 | 0 |
| [Counterexamples/NonArchimedeanPushout](FreeProducts/Counterexamples/NonArchimedeanPushout.lean) | 3 | 0 |
| [Counterexamples/NonextendibleHom](FreeProducts/Counterexamples/NonextendibleHom.lean) | 2 | 0 |
| [Counterexamples/OrderDensity](FreeProducts/Counterexamples/OrderDensity.lean) | 12 | 0 |
| [Counterexamples/SequenceLattices](FreeProducts/Counterexamples/SequenceLattices.lean) | 39 | 0 |
| [TensorProducts/Archimedean](FreeProducts/TensorProducts/Archimedean.lean) | 34 | 0 |
| [TensorProducts/Banach](FreeProducts/TensorProducts/Banach.lean) | 56 | 0 |
| [TensorProducts/Bimorphisms](FreeProducts/TensorProducts/Bimorphisms.lean) | 35 | 0 |
| [VectorLattice/Amalgamation](FreeProducts/VectorLattice/Amalgamation.lean) | 12 | 0 |
| [VectorLattice/Basic](FreeProducts/VectorLattice/Basic.lean) | 20 | 0 |
| [VectorLattice/PrimeIdeals](FreeProducts/VectorLattice/PrimeIdeals.lean) | 15 | 0 |
| [VectorLattice/TotalAmalgamation](FreeProducts/VectorLattice/TotalAmalgamation.lean) | 12 | 0 |

### Open source declarations

| Declaration | File | Placeholders |
|---|---|---:|

<!-- END SOURCE INVENTORY -->
