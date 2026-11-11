# torus-velocity-tether (private)

[![certify.yml](https://github.com/BenFrohman/torus-velocity-tether/actions/workflows/certify.yml/badge.svg?branch=main)](https://github.com/BenFrohman/torus-velocity-tether/actions/workflows/certify.yml)

Lean 4 + Mathlib rebuild of the velocity-tether model on the 3-torus T³, in Fourier variables.
It depends on `BenFrohman/torus-fourier-ns-lemmas` @ `66c3d7ae9dc81363e07c488edb0e373e2c689697` (the pre-rewrite pin `a241bf4` has the same Lean tree as `d413b14`; later commits only add modules)
(it uses `streamFunctionRepresentative_T3`, `fieldCurl_functionalDerivative_eq` and `fieldGateauxRep_unique`).
ℝ³ is **never** identified with T³. **This repository does not solve, and does not claim to solve, the Clay Navier–Stokes problem.**

Build with `lake build`. Run the audit with `lake env lean AxiomAudit.lean`. The audit result was PASS: the only axioms are propext, Classical.choice and Quot.sound. There is no `sorry` and there are no custom axioms.

## What is proved unconditionally
- `kineticEnergyCurlIdentity`: `KineticEnergyCurlIdentity` holds for every L² divergence-free mean-zero state. It is discharged, not assumed.
- `tetherKernelT_comm` (symmetry). `tetherKernelT_diag_nonpos` and `tetherKernelT_C3` (sign / controllable negative feedback). `tetherKernelT_feedbackAtMost`.
- `tetherKernelT_C2` and `tetherKernelT_energy_conservation`: degeneracy with respect to kinetic energy, via `Pi_u`.
- `tetherKernelT_C1`: invariance under **unimodular Fourier phases**, which include every translation of T³.
- `step2_degree_T`, `step5_higher_order_vanishes` and `step5_tetherKernelT`.
- `young_absorption` (P3T) and `comparison_ode_ceiling` (P4T).
- `torus_velocity_tether_product_theorem (hκ : 0 < kappa) : P1T ∧ P2T ∧ P3T ∧ P4T`. Its only hypothesis is κ > 0, and κ is otherwise a general parameter.

## What is conditional (named `Prop`s, passed explicitly)
- `VelocityFieldSlotAdditive s F G` and `VelocityFieldSlotSummable s F G` are needed by `tetherKernelT_polarizes`, which proves `TetherTwoFormPolarizesT (TetherKernelT κ)`.
- The uniqueness conjunct of `P1T` (`uniqueness_T`) takes `TetherTwoFormPolarizesT B` and `TetherTwoFormPolarizesT (TetherKernelT κ)` as explicit premises.
- `TetherKernelNontrivial κ` is needed by `c1_c3_not_unique_T`, which says C1–C3 alone do not determine the tether.

## Honest model changes vs. the original `VelocityTether.lean`
- The tether weight is the **mode-diagonal** |ω̂ₙ|², not the physical-space weight |ω(x)|².
- C1 covers the phase group only. The original C1 was vacuous because the coadjoint action was the identity. The KKS skew/Jacobi structure and the classical bracket were **not** rebuilt.
- P3T is only the algebraic Young-absorption step. P4T is a scalar ODE ceiling. Neither is a PDE regularity statement.

## Copyright, license and scope

Copyright 2026 Benjamin Stanley Frohman (ORCID [0009-0006-7068-3718](https://orcid.org/0009-0006-7068-3718)). Licensed under the Apache License, Version 2.0; see `LICENSE` and `NOTICE`.

What is proved vs. conditional: See "What is proved unconditionally" and "What is conditional (named `Prop`s, passed explicitly)" above. Every hypothesis is a named `Prop` passed as an explicit argument. Nothing in this repository claims to solve the Clay Millennium problem or global regularity for unmodified 3D Navier–Stokes.

## Citation

Cite this work with [`CITATION.cff`](CITATION.cff) (GitHub's "Cite this repository" button).
