# Kernel certificate: torus-velocity-tether

This file records a reproducible machine check of the Lean 4 development in this repository. Lean does not issue a signed "official" certificate. What is recorded here is the exact commit and toolchain, the complete `lake build` log, a scan for `sorry`/`admit`/`native_decide`/`axiom`, the `#print axioms` result for every theorem the build produces, and a replay of every module through Lean's kernel with the toolchain's `leanchecker`. Each check can be rerun with the command at the end.

| Item | Value |
|---|---|
| Repository | https://github.com/BenFrohman/torus-velocity-tether |
| Certified commit | `94b766a461b984c1c94a7fbf6c778d529748ed7e` (branch `chore/kernel-certificate`) |
| Lean sources | identical to `main` at `fa9bfb0e1b1cbfff8bf64b46ea10f750d4bcbcfd`: no `.lean`, lakefile, manifest or toolchain file differs; the certified commit only adds CI and the scripts in `certificates/tools/` |
| lean-toolchain | `leanprover/lean4:v4.30.0-rc1` |
| Lean | Lean (version 4.30.0-rc1, x86_64-unknown-linux-gnu, commit 714601baf118066cbf3f282361339c6d06665b2a, Release) |
| Mathlib | `0c154d67103f74be3a0f2c509f72ccbf5be9f2a7` (lake-manifest.json; inputRev `v4.30.0-rc1`) |
| Date (UTC) | 2026-11-16T19:18:09Z |
| CI run | https://github.com/BenFrohman/torus-velocity-tether/actions/runs/43937836399 |
| `lake build` | `Build completed successfully (8271 jobs).` ([build.log](build.log)) |
| sorry / admit / native_decide / axiom scan | `RESULT: 0 hits` ([sorry-scan.txt](sorry-scan.txt)) |
| `#print axioms` | `AUDIT PASS: 69 theorems in 1 modules depend only on propext, Classical.choice, Quot.sound (or on no axioms)` ([axioms.txt](axioms.txt)) |
| Kernel replay (leanchecker) | `RESULT: 2 of 2 modules replayed through the kernel, 0 failures` ([leanchecker.txt](leanchecker.txt)) |

## What each check means

- **Build.** `lake build` of the default targets with the pinned toolchain. Mathlib comes from `lake exe cache get` (it is never rebuilt from source). The build elaborates every proof and sends each declaration to Lean's kernel.
- **Scan.** `certificates/tools/sorry_scan.py` strips comments and strings from every tracked `.lean` file and reports any `sorry`, `admit`, `native_decide` or `axiom` declaration. Result: RESULT: 0 hits.
- **Axioms.** `certificates/tools/gen_audit.py` imports all 2 built modules ([modules.txt](modules.txt)) and calls `Lean.collectAxioms`, the function behind `#print axioms`, on every theorem declared in them (69 theorems, auto-generated internal names excluded). `check_audit.py` fails unless each depends only on `propext`, `Classical.choice` and `Quot.sound`, or on no axioms. Raw output: [axioms.raw.txt](axioms.raw.txt); generated Lean file: [KernelCertificateAudit.lean.txt](KernelCertificateAudit.lean.txt).
- **Kernel replay.** checker: leanchecker source shipped with v4.30.0-rc1 (src/lean/LeanChecker.lean), prefix match -> exact match, run with lean --run. For each module, the checker loads the module's imports from their `.olean` files and replays every declaration of that module through the kernel. The stock checker treats its argument as a module-name prefix and replays all matching modules in parallel, which runs out of memory on a root module, so it is run once per module with exact matching (the one-line patch is printed in [leanchecker.txt](leanchecker.txt)). The checker's own documentation describes it as a tool to detect environment hacking, not an independent external verifier; imported Mathlib and core declarations are trusted from their `.olean` files.

## Scope

The axiom result says the listed theorems are proved from Lean's standard axioms. It does not by itself say what the theorems mean; read the statements in the sources. Conditional theorems remain conditional on their hypotheses.

Full `#print axioms` output (verbatim from `axioms.txt`):

```
'TorusVelocityTether.IsPhase.conj' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.Pi_u.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.Pi_u_act' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.Pi_u_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.Pi_u_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.Pi_u_smul_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.TorusState.mk.inj' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.TorusState.mk.injEq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.TorusState.mk.sizeOf_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.TorusState.prop' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.act.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.actFun.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.actFun_conj_actFun' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.actState.congr_simp' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.actState_ω' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.act_act_conj' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.act_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.act_add_smul_conj' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.act_conj_act' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.act_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.act_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.c1_c3_not_unique_T' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.comparison_ode_ceiling' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.conj_mul_self_of_norm_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.cubic_field_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.eq_zero_of_fieldPairing_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.fd_act' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.fieldCurl_act' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.fieldCurl_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.fieldPairing_act' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.fieldPairing_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.fieldPairing_smul_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.fieldPairing_smul_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.finEnergy_act' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.isL2_act' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.isRep_act' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.kineticEnergyCurlIdentity' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.modeDensity_strict_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.modeE_act' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.modePairing_act_conj_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.modePairing_add_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.modePairing_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.modePairing_phase' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.modePairing_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.modePairing_self_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.modePairing_self_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.modePairing_smul_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.modePairing_smul_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.scaleState_ω' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.step2_degree_T' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.step5_higher_order_vanishes' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.step5_tetherKernelT' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.tetherKernelT_C1' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.tetherKernelT_C2' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.tetherKernelT_C3' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.tetherKernelT_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.tetherKernelT_diag_nonpos' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.tetherKernelT_energy_conservation' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.tetherKernelT_feedbackAtMost' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.tetherKernelT_polarizes' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.tetherKernelT_polarizes_at' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.tetherKernelT_quadratic_form' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.torus_velocity_tether_product_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.uniqueness_T' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.velSlot_act' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.velSlot_energy' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.velSlot_scale' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.wt_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TorusVelocityTether.young_absorption' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Rebuild

```
git clone https://github.com/BenFrohman/torus-velocity-tether.git && cd torus-velocity-tether && git checkout 94b766a461b984c1c94a7fbf6c778d529748ed7e && lake exe cache get && lake build && python3 certificates/tools/sorry_scan.py && python3 certificates/tools/gen_audit.py /tmp/KernelCertificateAudit.lean /tmp/modules.txt && lake env lean /tmp/KernelCertificateAudit.lean > /tmp/axioms.raw.txt && python3 certificates/tools/check_audit.py /tmp/axioms.raw.txt | tail -n 1
```
