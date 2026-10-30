/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import TorusFourierNS.FieldBiotSavart

/-!
# The velocity-slot tether on the torus `T³ = UnitAddTorus (Fin 3)`

Everything is on the Fourier side of the real torus: a field is `v : ℤ³ → ℂ³`
(`TorusFourierNS.FField`). A state is a divergence-free, mean-zero velocity
`u ∈ L²(T³)` (`IsL2DivFreeMeanZero u`), its vorticity is `ω = curl u`, and the kinetic energy
is `H = fieldEnergy` (`H(curl u) = ½‖u‖²`). No identification of `ℝ³` with `T³` is made.

The tether kernel is

  `TetherKernelT κ s F G = -κ ∑ₙ |ω̂ₙ|² ⟨(Π_u curl δF)̂ₙ, (Π_u curl δG)̂ₙ⟩`,

where `Π_u v = v - (⟨u,v⟩/⟨u,u⟩) u` is the `L²` projection off `u`. The weight is the
mode-diagonal `|ω̂ₙ|²`; it is not the physical-space weight `|ω(x)|²` of the `ℝ³` model.
-/

noncomputable section

open Complex

namespace TorusVelocityTether

open TorusFourierNS

/-! ## States, functionals, derivative -/

/-- A state: a divergence-free, mean-zero `L²` velocity field on `T³` (Fourier side). -/
structure TorusState where
  u : FField
  prop : IsL2DivFreeMeanZero u

/-- Vorticity `ω = curl u`. -/
def TorusState.ω (s : TorusState) : FField := fieldCurl s.u

/-- Functionals of the vorticity. -/
abbrev Functional := FField → ℝ

/-- Kinetic energy `H(ω) = ∑ₙ |ω̂ₙ|²/(8π²|n|²)`. -/
def KineticEnergy : Functional := fieldEnergy

/-- Functional derivative `δF/δω` at the state's vorticity (choice-based, unique when it exists). -/
def fd (F : Functional) (s : TorusState) : FField := fieldFunctionalDerivative F s.ω

/-- The stream-function identity `curl(δH/δω) = u`. -/
def KineticEnergyCurlIdentity (s : TorusState) : Prop := fieldCurl (fd KineticEnergy s) = s.u

/-- **`KineticEnergyCurlIdentity` holds for every state, unconditionally** (from the torus
Biot–Savart theorem `fieldCurl_functionalDerivative_eq`). -/
theorem kineticEnergyCurlIdentity (s : TorusState) : KineticEnergyCurlIdentity s :=
  fieldCurl_functionalDerivative_eq s.prop

/-! ## Mode pairing facts -/

lemma modePairing_comm (a b : Fin 3 → ℂ) : modePairing a b = modePairing b a := by
  unfold modePairing
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (starRingEnd ℂ) (b i) * a i = (starRingEnd ℂ) ((starRingEnd ℂ) (a i) * b i) := by
    simp [mul_comm]
  rw [this, Complex.conj_re]

lemma modePairing_self (a : Fin 3 → ℂ) : modePairing a a = ∑ i, ‖a i‖ ^ 2 := by
  unfold modePairing
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.conj_mul']; norm_cast

lemma modePairing_self_nonneg (a : Fin 3 → ℂ) : 0 ≤ modePairing a a := by
  rw [modePairing_self]; positivity

lemma modePairing_self_pos {a : Fin 3 → ℂ} (ha : a ≠ 0) : 0 < modePairing a a := by
  rw [modePairing_self]
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h; push_neg at h; exact ha (funext h)
  have : 0 < ‖a i‖ ^ 2 := by positivity
  exact lt_of_lt_of_le this
    (Finset.single_le_sum (f := fun j => ‖a j‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i))

lemma modePairing_add_add (a b : Fin 3 → ℂ) :
    modePairing (a + b) (a + b) = modePairing a a + modePairing b b + 2 * modePairing a b := by
  have hc := modePairing_comm b a
  unfold modePairing at *
  simp only [Pi.add_apply, map_add, add_mul, mul_add, Complex.add_re, Finset.sum_add_distrib] at *
  rw [hc]; ring

lemma modePairing_smul_left (c : ℝ) (a b : Fin 3 → ℂ) :
    modePairing (c • a) b = c * modePairing a b := by
  unfold modePairing
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.mul_re]; ring

lemma modePairing_smul_right (c : ℝ) (a b : Fin 3 → ℂ) :
    modePairing a (c • b) = c * modePairing a b := by
  rw [modePairing_comm, modePairing_smul_left, modePairing_comm]

/-! ## Projection `Π_u` -/

/-- `L²` projection off `u`: `Π_u v = v - (⟨u,v⟩/⟨u,u⟩) u`. -/
def Pi_u (u v : FField) : FField := v - (fieldPairing u v / fieldPairing u u) • u

lemma fieldPairing_self (u : FField) : fieldPairing u u = ∑' n, ∑ i, ‖u n i‖ ^ 2 := by
  unfold fieldPairing; simp only [modePairing_self]

/-- An `L²` field with `⟨u,u⟩ = 0` is zero. -/
lemma eq_zero_of_fieldPairing_self {u : FField} (hs : Summable fun n => ∑ i, ‖u n i‖ ^ 2)
    (h : fieldPairing u u = 0) : u = 0 := by
  rw [fieldPairing_self] at h
  have hnn : ∀ n, 0 ≤ ∑ i, ‖u n i‖ ^ 2 := fun n => by positivity
  have h0 := (hasSum_zero_iff_of_nonneg hnn).mp (h ▸ hs.hasSum)
  funext n i
  have := congrFun h0 n
  simp only [Pi.zero_apply] at this
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).mp this i
    (Finset.mem_univ i)
  simpa using this

/-- `Π_u u = 0` for every `L²` field `u`. -/
theorem Pi_u_self {u : FField} (hs : Summable fun n => ∑ i, ‖u n i‖ ^ 2) : Pi_u u u = 0 := by
  by_cases h : fieldPairing u u = 0
  · have := eq_zero_of_fieldPairing_self hs h; subst this; funext n i; simp [Pi_u]
  · funext n i; simp [Pi_u, div_self h]

/-- Beltrami / collinear directions are annihilated: `Π_u (λu) = 0` when `⟨u,u⟩ ≠ 0`. -/
theorem Pi_u_smul_self (u : FField) (lam : ℝ) (h : fieldPairing u u ≠ 0) :
    Pi_u u (lam • u) = 0 := by
  have : fieldPairing u (lam • u) = lam * fieldPairing u u := by
    unfold fieldPairing
    simp only [Pi.smul_apply, modePairing_smul_right]; exact tsum_mul_left
  simp [Pi_u, this, mul_div_assoc, div_self h]

/-! ## The tether kernel -/

/-- Mode weight `|ω̂ₙ|²`. -/
def wt (ω : FField) (n : Mode) : ℝ := modePairing (ω n) (ω n)

lemma wt_nonneg (ω : FField) (n : Mode) : 0 ≤ wt ω n := modePairing_self_nonneg _

/-- Projected velocity slot `Π_u curl(δF/δω)`. -/
def velSlot (F : Functional) (s : TorusState) : FField := Pi_u s.u (fieldCurl (fd F s))

/-- The velocity-slot tether kernel on `T³`. -/
def TetherKernelT (kappa : ℝ) (s : TorusState) (F G : Functional) : ℝ :=
  -kappa * ∑' n, wt s.ω n * modePairing (velSlot F s n) (velSlot G s n)

theorem tetherKernelT_comm (kappa : ℝ) (s : TorusState) (F G : Functional) :
    TetherKernelT kappa s F G = TetherKernelT kappa s G F := by
  unfold TetherKernelT; simp only [modePairing_comm (velSlot F s _)]

theorem tetherKernelT_quadratic_form (kappa : ℝ) (s : TorusState) (F : Functional) :
    TetherKernelT kappa s F F =
      -kappa * ∑' n, wt s.ω n * ∑ i, ‖velSlot F s n i‖ ^ 2 := by
  unfold TetherKernelT; simp only [modePairing_self]

theorem tetherKernelT_diag_nonpos {kappa : ℝ} (hκ : 0 ≤ kappa) (s : TorusState) (F : Functional) :
    TetherKernelT kappa s F F ≤ 0 := by
  unfold TetherKernelT
  have : 0 ≤ ∑' n, wt s.ω n * modePairing (velSlot F s n) (velSlot F s n) :=
    tsum_nonneg fun n => mul_nonneg (wt_nonneg _ _) (modePairing_self_nonneg _)
  nlinarith

/-- Mode density `-κ |ω̂ₙ|² |(Π_u curl δF)̂ₙ|²`. -/
def modeDensity (kappa : ℝ) (s : TorusState) (F : Functional) (n : Mode) : ℝ :=
  -kappa * (wt s.ω n * modePairing (velSlot F s n) (velSlot F s n))

/-- Strict damping on every mode where `ω̂ₙ ≠ 0` and the projected slot is nonzero. -/
theorem modeDensity_strict_neg {kappa : ℝ} (hκ : 0 < kappa) (s : TorusState) (F : Functional)
    (n : Mode) (hω : s.ω n ≠ 0) (hP : velSlot F s n ≠ 0) : modeDensity kappa s F n < 0 := by
  unfold modeDensity
  have := mul_pos (modePairing_self_pos hω) (modePairing_self_pos hP)
  unfold wt; nlinarith

/-- C3 (controllable negative feedback). -/
def ProducesControllableNegativeFeedbackT (kappa : ℝ)
    (B : TorusState → Functional → Functional → ℝ) : Prop :=
  ∀ F s, B s F F ≤ -kappa * ∑' n, wt s.ω n * ∑ i, ‖velSlot F s n i‖ ^ 2

/-- Minimality bound. -/
def FeedbackAtMostT (kappa : ℝ) (B : TorusState → Functional → Functional → ℝ) : Prop :=
  ∀ F s, -kappa * ∑' n, wt s.ω n * ∑ i, ‖velSlot F s n i‖ ^ 2 ≤ B s F F

theorem tetherKernelT_C3 (kappa : ℝ) :
    ProducesControllableNegativeFeedbackT kappa (TetherKernelT kappa) :=
  fun F s => le_of_eq (tetherKernelT_quadratic_form kappa s F)

theorem tetherKernelT_feedbackAtMost (kappa : ℝ) : FeedbackAtMostT kappa (TetherKernelT kappa) :=
  fun F s => le_of_eq (tetherKernelT_quadratic_form kappa s F).symm

/-! ## C2 and energy conservation (unconditional) -/

/-- C2 predicate: degeneracy with respect to the kinetic energy. -/
def DegenerateWRTKineticEnergyT (B : TorusState → Functional → Functional → ℝ) : Prop :=
  ∀ F s, B s F KineticEnergy = 0

/-- The energy slot vanishes: `Π_u curl(δH/δω) = Π_u u = 0`. -/
theorem velSlot_energy (s : TorusState) : velSlot KineticEnergy s = 0 := by
  unfold velSlot; rw [kineticEnergyCurlIdentity s]; exact Pi_u_self s.prop.summable

/-- **C2, unconditional on `T³`.** -/
theorem tetherKernelT_C2 (kappa : ℝ) : DegenerateWRTKineticEnergyT (TetherKernelT kappa) := by
  intro F s
  unfold TetherKernelT; rw [velSlot_energy]
  simp [modePairing]

/-- **Energy conservation:** the tether never moves the kinetic energy,
`B(H,F) = B(F,H) = B(H,H) = 0` for every state and functional. -/
theorem tetherKernelT_energy_conservation (kappa : ℝ) (s : TorusState) (F : Functional) :
    TetherKernelT kappa s KineticEnergy F = 0 ∧ TetherKernelT kappa s F KineticEnergy = 0 ∧
      TetherKernelT kappa s KineticEnergy KineticEnergy = 0 :=
  ⟨by rw [tetherKernelT_comm]; exact tetherKernelT_C2 kappa F s, tetherKernelT_C2 kappa F s,
    tetherKernelT_C2 kappa _ s⟩

/-! ## C1: invariance under unimodular Fourier phases (includes all translations of `T³`) -/

/-- A unimodular phase on modes, e.g. `θₙ = e^{2πi n·a}` (translation by `a ∈ T³`). -/
def IsPhase (θ : Mode → ℂ) : Prop := ∀ n, ‖θ n‖ = 1

/-- Action of a phase on fields. -/
def act (θ : Mode → ℂ) (v : FField) : FField := fun n i => θ n * v n i

lemma conj_mul_self_of_norm_one {z : ℂ} (h : ‖z‖ = 1) : (starRingEnd ℂ) z * z = 1 := by
  rw [Complex.conj_mul', h]; simp

lemma IsPhase.conj {θ : Mode → ℂ} (h : IsPhase θ) : IsPhase fun n => (starRingEnd ℂ) (θ n) :=
  fun n => by simpa using h n

lemma act_conj_act {θ : Mode → ℂ} (h : IsPhase θ) (v : FField) :
    act (fun n => (starRingEnd ℂ) (θ n)) (act θ v) = v := by
  funext n i; simp only [act, ← mul_assoc, conj_mul_self_of_norm_one (h n), one_mul]

lemma act_act_conj {θ : Mode → ℂ} (h : IsPhase θ) (v : FField) :
    act θ (act (fun n => (starRingEnd ℂ) (θ n)) v) = v := by
  have := act_conj_act h.conj v; simpa using this

lemma modePairing_phase {z : ℂ} (h : ‖z‖ = 1) (a b : Fin 3 → ℂ) :
    modePairing (fun i => z * a i) (fun i => z * b i) = modePairing a b := by
  unfold modePairing
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (starRingEnd ℂ) (z * a i) * (z * b i) =
      ((starRingEnd ℂ) z * z) * ((starRingEnd ℂ) (a i) * b i) := by simp; ring
  rw [this, conj_mul_self_of_norm_one h, one_mul]

lemma modePairing_act_conj_right {z : ℂ} (h : ‖z‖ = 1) (a b : Fin 3 → ℂ) :
    modePairing a (fun i => (starRingEnd ℂ) z * b i) = modePairing (fun i => z * a i) b := by
  unfold modePairing
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1; simp; ring

lemma fieldPairing_act {θ : Mode → ℂ} (h : IsPhase θ) (a b : FField) :
    fieldPairing (act θ a) (act θ b) = fieldPairing a b := by
  unfold fieldPairing act; exact tsum_congr fun n => modePairing_phase (h n) _ _

lemma act_add (θ : Mode → ℂ) (a b : FField) : act θ (a + b) = act θ a + act θ b := by
  funext n i; simp [act, mul_add]

lemma act_sub (θ : Mode → ℂ) (a b : FField) : act θ (a - b) = act θ a - act θ b := by
  funext n i; simp [act, mul_sub]

lemma act_smul (θ : Mode → ℂ) (c : ℝ) (a : FField) : act θ (c • a) = c • act θ a := by
  funext n i; simp [act]; ring

lemma fieldCurl_act (θ : Mode → ℂ) (v : FField) :
    fieldCurl (act θ v) = act θ (fieldCurl v) := by
  funext n i; fin_cases i <;> simp [fieldCurl, act, curlSym, cross] <;> ring

lemma modeE_act {θ : Mode → ℂ} (h : IsPhase θ) (v : FField) (n : Mode) :
    modeE n (act θ v n) = modeE n (v n) := by
  simp [modeE, modeEnergy, act, h n]

lemma finEnergy_act {θ : Mode → ℂ} (h : IsPhase θ) {v : FField} (hv : FinEnergy v) :
    FinEnergy (act θ v) := by
  unfold FinEnergy; simp only [modeE_act h]; exact hv

lemma isL2_act {θ : Mode → ℂ} (h : IsPhase θ) {u : FField} (hu : IsL2DivFreeMeanZero u) :
    IsL2DivFreeMeanZero (act θ u) where
  summable := by simpa [act, h _] using hu.summable
  div_free := fun n => by
    have := hu.div_free n
    simp only [dot, act, Fin.sum_univ_three] at *
    linear_combination θ n * this
  mean_zero := by funext i; simp [act, hu.mean_zero]

/-- Phase action on states. -/
def actState {θ : Mode → ℂ} (h : IsPhase θ) (s : TorusState) : TorusState :=
  ⟨act θ s.u, isL2_act h s.prop⟩

/-- Transported functional `F^θ(ω) = F(θ̄ ω)`. -/
def actFun (θ : Mode → ℂ) (F : Functional) : Functional :=
  fun ω => F (act (fun n => (starRingEnd ℂ) (θ n)) ω)

lemma act_add_smul_conj {θ : Mode → ℂ} (h : IsPhase θ) (ω η : FField) (ε : ℝ) :
    act (fun n => (starRingEnd ℂ) (θ n)) (act θ ω + ε • η) =
      ω + ε • act (fun n => (starRingEnd ℂ) (θ n)) η := by
  rw [act_add, act_conj_act h, act_smul]

/-- Gateaux representatives transport along phases. -/
lemma isRep_act {θ : Mode → ℂ} (h : IsPhase θ) {F : Functional} {ω δ : FField}
    (hr : IsFieldGateauxRep F ω δ) : IsFieldGateauxRep (actFun θ F) (act θ ω) (act θ δ) := by
  intro η hη
  have hη' := finEnergy_act h.conj hη
  have hd := hr _ hη'
  have hfun : (fun ε : ℝ => actFun θ F (act θ ω + ε • η)) =
      fun ε : ℝ => F (ω + ε • act (fun n => (starRingEnd ℂ) (θ n)) η) := by
    funext ε; simp only [actFun, act_add_smul_conj h]
  rw [hfun]
  have hp : fieldPairing δ (act (fun n => (starRingEnd ℂ) (θ n)) η) =
      fieldPairing (act θ δ) η := by
    unfold fieldPairing act
    exact tsum_congr fun n => modePairing_act_conj_right (h n) _ _
  rw [← hp]; exact hd

lemma actFun_conj_actFun {θ : Mode → ℂ} (h : IsPhase θ) (F : Functional) :
    actFun (fun n => (starRingEnd ℂ) (θ n)) (actFun θ F) = F := by
  funext ω; simp only [actFun]
  have := act_conj_act h ω
  simp only [Complex.conj_conj] at *
  rw [this]

/-- `δ(F^θ)(θω) = θ δF(ω)`. -/
theorem fd_act {θ : Mode → ℂ} (h : IsPhase θ) (F : Functional) (ω : FField) :
    fieldFunctionalDerivative (actFun θ F) (act θ ω) = act θ (fieldFunctionalDerivative F ω) := by
  by_cases hex : ∃ δ, IsFieldGateauxRep F ω δ
  · obtain ⟨δ, hδ⟩ := hex
    rw [fieldFunctionalDerivative_eq hδ, fieldFunctionalDerivative_eq (isRep_act h hδ)]
  · have hex' : ¬ ∃ δ, IsFieldGateauxRep (actFun θ F) (act θ ω) δ := by
      rintro ⟨δ, hδ⟩
      apply hex
      refine ⟨act (fun n => (starRingEnd ℂ) (θ n)) δ, ?_⟩
      have := isRep_act h.conj hδ
      rwa [actFun_conj_actFun h, act_conj_act h] at this
    rw [fieldFunctionalDerivative, dif_neg hex', fieldFunctionalDerivative, dif_neg hex]
    funext n i; simp [act]

lemma actState_ω {θ : Mode → ℂ} (h : IsPhase θ) (s : TorusState) :
    (actState h s).ω = act θ s.ω := fieldCurl_act θ s.u

lemma Pi_u_act {θ : Mode → ℂ} (h : IsPhase θ) (u v : FField) :
    Pi_u (act θ u) (act θ v) = act θ (Pi_u u v) := by
  unfold Pi_u; rw [fieldPairing_act h, fieldPairing_act h, act_sub, act_smul]

lemma velSlot_act {θ : Mode → ℂ} (h : IsPhase θ) (F : Functional) (s : TorusState) :
    velSlot (actFun θ F) (actState h s) = act θ (velSlot F s) := by
  unfold velSlot fd
  rw [actState_ω, fd_act h, fieldCurl_act, ← Pi_u_act h]; rfl

/-- C1 predicate: covariance under every unimodular phase (functionals transported). -/
def PhaseInvariant (B : TorusState → Functional → Functional → ℝ) : Prop :=
  ∀ (θ : Mode → ℂ) (h : IsPhase θ) (s : TorusState) (F G : Functional),
    B (actState h s) (actFun θ F) (actFun θ G) = B s F G

/-- **C1 on `T³`:** the tether is invariant under all unimodular Fourier phases, in particular
under every translation of the torus. -/
theorem tetherKernelT_C1 (kappa : ℝ) : PhaseInvariant (TetherKernelT kappa) := by
  intro θ h s F G
  unfold TetherKernelT
  rw [velSlot_act h, velSlot_act h, actState_ω h]
  congr 1
  refine tsum_congr fun n => ?_
  unfold wt
  show modePairing (fun i => θ n * s.ω n i) (fun i => θ n * s.ω n i) * modePairing (fun i => θ n * velSlot F s n i) (fun i => θ n * velSlot G s n i) = _
  rw [modePairing_phase (h n), modePairing_phase (h n)]

/-! ## Polarization and uniqueness -/

/-- Polarization predicate. -/
def PolarizesT (B : TorusState → Functional → Functional → ℝ) : Prop :=
  ∀ s F G, 2 * B s F G = B s (fun ω => F ω + G ω) (fun ω => F ω + G ω) - B s F F - B s G G

/-- Named hypothesis: the projected slot is additive in the functional at `s`. -/
def VelSlotAdditive (s : TorusState) (F G : Functional) : Prop :=
  velSlot (fun ω => F ω + G ω) s = velSlot F s + velSlot G s

/-- Named hypothesis: the weighted slot series for `(F,F)`, `(G,G)`, `(F,G)` are summable. -/
def WeightedSlotSummable (s : TorusState) (F G : Functional) : Prop :=
  Summable (fun n => wt s.ω n * modePairing (velSlot F s n) (velSlot F s n)) ∧
  Summable (fun n => wt s.ω n * modePairing (velSlot G s n) (velSlot G s n)) ∧
  Summable (fun n => wt s.ω n * modePairing (velSlot F s n) (velSlot G s n))

theorem tetherKernelT_polarizes_at (kappa : ℝ) (s : TorusState) (F G : Functional)
    (hadd : VelSlotAdditive s F G) (hsum : WeightedSlotSummable s F G) :
    2 * TetherKernelT kappa s F G =
      TetherKernelT kappa s (fun ω => F ω + G ω) (fun ω => F ω + G ω) -
        TetherKernelT kappa s F F - TetherKernelT kappa s G G := by
  obtain ⟨hFF, hGG, hFG⟩ := hsum
  unfold TetherKernelT
  rw [hadd]
  have hpt : (fun n => wt s.ω n * modePairing ((velSlot F s + velSlot G s) n)
      ((velSlot F s + velSlot G s) n)) = fun n =>
      (wt s.ω n * modePairing (velSlot F s n) (velSlot F s n) +
        wt s.ω n * modePairing (velSlot G s n) (velSlot G s n)) +
        2 * (wt s.ω n * modePairing (velSlot F s n) (velSlot G s n)) := by
    funext n; simp only [Pi.add_apply, modePairing_add_add]; ring
  rw [hpt, Summable.tsum_add (hFF.add hGG) (hFG.mul_left 2), Summable.tsum_add hFF hGG,
    tsum_mul_left]
  ring

theorem tetherKernelT_polarizes (kappa : ℝ)
    (hadd : ∀ s F G, VelSlotAdditive s F G) (hsum : ∀ s F G, WeightedSlotSummable s F G) :
    PolarizesT (TetherKernelT kappa) := fun s F G =>
  tetherKernelT_polarizes_at kappa s F G (hadd s F G) (hsum s F G)

/-- **Uniqueness.** C3, the minimality bound and polarization force `B = TetherKernelT`. -/
theorem uniqueness_T (kappa : ℝ) (B : TorusState → Functional → Functional → ℝ)
    (hC3 : ProducesControllableNegativeFeedbackT kappa B) (hmin : FeedbackAtMostT kappa B)
    (hPB : PolarizesT B) (hPT : PolarizesT (TetherKernelT kappa)) :
    ∀ s F G, B s F G = TetherKernelT kappa s F G := by
  have hs : ∀ F s, B s F F = TetherKernelT kappa s F F := fun F s => by
    rw [tetherKernelT_quadratic_form]; exact le_antisymm (hC3 F s) (hmin F s)
  intro s F G
  have := hPB s F G; have := hPT s F G
  have := hs F s; have := hs G s; have := hs (fun ω => F ω + G ω) s
  linarith

/-- Named hypothesis: the tether is not identically zero on the diagonal. -/
def TetherNontrivial (kappa : ℝ) : Prop := ∃ s F, TetherKernelT kappa s F F ≠ 0

/-- **C1–C3 alone do not determine the tether** (C1, C2, C3 all proved; `2·TetherKernelT`). -/
theorem c1_c3_not_unique_T {kappa : ℝ} (hκ : 0 ≤ kappa) (hne : TetherNontrivial kappa) :
    ∃ B : TorusState → Functional → Functional → ℝ,
      (∀ s F G, B s F G = B s G F) ∧ PhaseInvariant B ∧ DegenerateWRTKineticEnergyT B ∧
      ProducesControllableNegativeFeedbackT kappa B ∧
      ∃ s F G, B s F G ≠ TetherKernelT kappa s F G := by
  obtain ⟨s₀, F₀, hF₀⟩ := hne
  refine ⟨fun s F G => 2 * TetherKernelT kappa s F G,
    fun s F G => by simp only [tetherKernelT_comm kappa s F G],
    fun θ h s F G => by simp only [tetherKernelT_C1 kappa θ h s F G],
    fun F s => by simp only [tetherKernelT_C2 kappa F s, mul_zero],
    fun F s => ?_, s₀, F₀, F₀, fun h => hF₀ (by linarith)⟩
  have h := tetherKernelT_diag_nonpos hκ s F
  have := tetherKernelT_quadratic_form kappa s F
  show 2 * _ ≤ _
  linarith

/-! ## Degree 2 and Step 5 -/

/-- Scaling `u ↦ c u` (so `ω ↦ c ω`). -/
def scaleState (c : ℝ) (s : TorusState) : TorusState :=
  ⟨c • s.u, {
    summable := by
      have : (fun n => ∑ i, ‖(c • s.u) n i‖ ^ 2) = fun n => c ^ 2 * ∑ i, ‖s.u n i‖ ^ 2 := by
        funext n; rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [norm_smul, mul_pow]
      rw [this]; exact s.prop.summable.mul_left _
    div_free := fun n => by
      have := s.prop.div_free n
      simp only [dot, Pi.smul_apply, Fin.sum_univ_three, Complex.real_smul] at *
      linear_combination (c : ℂ) * this
    mean_zero := by funext i; simp [s.prop.mean_zero] }⟩

lemma fieldCurl_smul (c : ℝ) (v : FField) : fieldCurl (c • v) = c • fieldCurl v := by
  funext n i; fin_cases i <;> simp [fieldCurl, curlSym, cross, Complex.real_smul] <;> ring

lemma scaleState_ω (c : ℝ) (s : TorusState) : (scaleState c s).ω = c • s.ω :=
  fieldCurl_smul c s.u

lemma fieldPairing_smul_left (c : ℝ) (a b : FField) :
    fieldPairing (c • a) b = c * fieldPairing a b := by
  unfold fieldPairing; simp only [Pi.smul_apply, modePairing_smul_left]; exact tsum_mul_left

lemma fieldPairing_smul_right (c : ℝ) (a b : FField) :
    fieldPairing a (c • b) = c * fieldPairing a b := by
  unfold fieldPairing; simp only [Pi.smul_apply, modePairing_smul_right]; exact tsum_mul_left

lemma Pi_u_smul {c : ℝ} (hc : c ≠ 0) (u v : FField) : Pi_u (c • u) v = Pi_u u v := by
  unfold Pi_u
  rw [fieldPairing_smul_left, fieldPairing_smul_left, fieldPairing_smul_right]
  by_cases h : fieldPairing u u = 0
  · funext n i; simp [h]
  · funext n i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    congr 1
    rw [← mul_assoc]; congr 1
    have hc' : (c:ℂ) ≠ 0 := by exact_mod_cast hc
    have h' : ((fieldPairing u u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h
    field_simp
    try (rw [← Complex.ofReal_mul]; congr 1; field_simp)

theorem velSlot_scale {c : ℝ} (hc : c ≠ 0) (F : Functional) (s : TorusState)
    (hF : fd F (scaleState c s) = fd F s) : velSlot F (scaleState c s) = velSlot F s := by
  unfold velSlot; rw [hF]; exact Pi_u_smul hc _ _

/-- **Degree 2** under `ω ↦ cω` when `δF, δG` are scale invariant. -/
theorem step2_degree_T (kappa : ℝ) (F G : Functional) (s : TorusState) (c : ℝ) (hc : c ≠ 0)
    (hF : fd F (scaleState c s) = fd F s) (hG : fd G (scaleState c s) = fd G s) :
    TetherKernelT kappa (scaleState c s) F G = c ^ 2 * TetherKernelT kappa s F G := by
  unfold TetherKernelT
  rw [velSlot_scale hc F s hF, velSlot_scale hc G s hG, scaleState_ω]
  have : ∀ n, wt (c • s.ω) n = c ^ 2 * wt s.ω n := fun n => by
    unfold wt; simp only [Pi.smul_apply, modePairing_smul_left, modePairing_smul_right]; ring
  simp only [this, mul_assoc]
  rw [tsum_mul_left]; ring

/-- Step 5 (abstract): degree-2 sum with a degree-`n ≥ 3` remainder forces the remainder to 0. -/
theorem step5_higher_order_vanishes {X : Type*} (scale : X → X) (c : ℝ) (hc : 1 < |c|)
    (B Q R : X → ℝ) (n : ℕ) (hn : 3 ≤ n)
    (hsum : ∀ x, B x = Q x + R x)
    (hB : ∀ x, B (scale x) = c ^ 2 * B x) (hQ : ∀ x, Q (scale x) = c ^ 2 * Q x)
    (hR : ∀ x, R (scale x) = c ^ n * R x) :
    ∀ x, R x = 0 := by
  intro x
  have h1 := hsum (scale x)
  rw [hB, hQ, hR, hsum x] at h1
  have hne : c ^ n ≠ c ^ 2 := by
    intro h
    have h' : |c| ^ n = |c| ^ 2 := by rw [← abs_pow, ← abs_pow, h]
    have : |c| ^ 2 < |c| ^ n := pow_lt_pow_right₀ hc (by omega)
    linarith
  have : (c ^ n - c ^ 2) * R x = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · exact h

/-- **Step 5 on `T³`.** -/
theorem step5_tetherKernelT (kappa : ℝ) (F G : Functional) (c : ℝ) (hc : 1 < |c|)
    (hF : ∀ s, fd F (scaleState c s) = fd F s) (hG : ∀ s, fd G (scaleState c s) = fd G s)
    (B R : TorusState → ℝ) (n : ℕ) (hn : 3 ≤ n)
    (hsum : ∀ s, B s = TetherKernelT kappa s F G + R s)
    (hB : ∀ s, B (scaleState c s) = c ^ 2 * B s)
    (hR : ∀ s, R (scaleState c s) = c ^ n * R s) :
    ∀ s, B s = TetherKernelT kappa s F G := by
  have hc0 : c ≠ 0 := by intro h; rw [h, abs_zero] at hc; linarith
  have hR0 := step5_higher_order_vanishes (scaleState c) c hc B
    (fun s => TetherKernelT kappa s F G) R n hn hsum hB
    (fun s => step2_degree_T kappa F G s c hc0 (hF s) (hG s)) hR
  intro s; rw [hsum, hR0, add_zero]

/-! ## P3 (algebraic absorption) and P4 (scalar ODE ceiling) -/

/-- Young absorption with `ε = κ/4` (pure algebra; `C` is a free constant). -/
theorem young_absorption (kappa C M I₄ I₆ phi C_abs : ℝ)
    (h : 4 * C * M * I₄ ≤ (kappa / 4) * I₆ + C_abs * (M ^ 3 * phi ^ ((3 : ℝ) / 2))) :
    4 * C * M * I₄ - kappa * I₆ ≤ C_abs * (M ^ 3 * phi ^ ((3 : ℝ) / 2)) - (3 / 4) * kappa * I₆ := by
  linarith

lemma cubic_field_neg {C κ'' z : ℝ} (hC : 0 < C) (hκ : 0 < κ'') (hz : C / κ'' < z) :
    C * z ^ 2 - κ'' * z ^ 3 < 0 := by
  have hzpos : 0 < z := lt_trans (div_pos hC hκ) hz
  have hlin : C - κ'' * z < 0 := by
    have hmul : κ'' * (C / κ'') < κ'' * z := mul_lt_mul_of_pos_left hz hκ
    rw [mul_div_cancel₀ C (ne_of_gt hκ)] at hmul
    linarith
  have : C * z ^ 2 - κ'' * z ^ 3 = z ^ 2 * (C - κ'' * z) := by ring
  rw [this]; exact mul_neg_of_pos_of_neg (by positivity) hlin

/-- Scalar comparison: `y' ≤ C y² − κ'' y³` on `[0,∞)` gives `y(t) ≤ max(y 0, C/κ'')`. -/
theorem comparison_ode_ceiling (C κ'' : ℝ) (hC : 0 < C) (hκ : 0 < κ'') (y : ℝ → ℝ)
    (hdiff : ∀ s ≥ (0 : ℝ), DifferentiableAt ℝ y s)
    (hy : ∀ s ≥ (0 : ℝ), deriv y s ≤ C * (y s) ^ 2 - κ'' * (y s) ^ 3)
    (t : ℝ) (ht : 0 ≤ t) : y t ≤ max (y 0) (C / κ'') := by
  set Y := max (y 0) (C / κ'')
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hbar : C / κ'' < Y + ε :=
    lt_of_le_of_lt (le_max_right (y 0) (C / κ'')) (lt_add_of_pos_right _ hε)
  have hy0 : y 0 ≤ Y + ε := (le_max_left (y 0) (C / κ'')).trans (le_add_of_nonneg_right hε.le)
  have hyC : ContinuousOn y (Set.Icc (0 : ℝ) t) := fun x hx =>
    (hdiff x hx.1).continuousAt.continuousWithinAt
  have hyW : ∀ x ∈ Set.Ico (0 : ℝ) t, HasDerivWithinAt y (deriv y x) (Set.Ici x) x :=
    fun x hx => (hdiff x hx.1).hasDerivAt.hasDerivWithinAt
  have hB : ∀ x, HasDerivAt (fun _ : ℝ => Y + ε) (0 : ℝ) x := fun x => hasDerivAt_const x _
  have hcontact : ∀ x ∈ Set.Ico (0 : ℝ) t, y x = Y + ε → deriv y x < 0 := by
    intro x hx hxeq
    have hneg := cubic_field_neg hC hκ hbar
    have := hy x hx.1
    rw [hxeq] at this; linarith
  exact image_le_of_deriv_right_lt_deriv_boundary (f := y) (f' := deriv y) (a := 0) (b := t)
    (B := fun _ => Y + ε) (B' := fun _ => (0 : ℝ)) hyC hyW hy0 hB hcontact ⟨ht, le_rfl⟩

/-! ## Product theorem -/

/-- `P1T`: uniqueness, degree 2, Step 5. -/
def P1T (kappa : ℝ) : Prop :=
  (∀ B : TorusState → Functional → Functional → ℝ,
    ProducesControllableNegativeFeedbackT kappa B → FeedbackAtMostT kappa B →
    PolarizesT B → PolarizesT (TetherKernelT kappa) →
    ∀ s F G, B s F G = TetherKernelT kappa s F G) ∧
  (∀ (F G : Functional) (s : TorusState) (c : ℝ), c ≠ 0 →
    fd F (scaleState c s) = fd F s → fd G (scaleState c s) = fd G s →
    TetherKernelT kappa (scaleState c s) F G = c ^ 2 * TetherKernelT kappa s F G) ∧
  (∀ (F G : Functional) (c : ℝ), 1 < |c| →
    (∀ s, fd F (scaleState c s) = fd F s) → (∀ s, fd G (scaleState c s) = fd G s) →
    ∀ (B R : TorusState → ℝ) (n : ℕ), 3 ≤ n →
    (∀ s, B s = TetherKernelT kappa s F G + R s) →
    (∀ s, B (scaleState c s) = c ^ 2 * B s) →
    (∀ s, R (scaleState c s) = c ^ n * R s) →
    ∀ s, B s = TetherKernelT kappa s F G)

/-- `P2T`: curl identity, symmetry, C1, C2, C3, energy conservation, sign, Beltrami
projection, strict mode-wise damping. -/
def P2T (kappa : ℝ) : Prop :=
  (∀ s, KineticEnergyCurlIdentity s) ∧
  (∀ s F G, TetherKernelT kappa s F G = TetherKernelT kappa s G F) ∧
  PhaseInvariant (TetherKernelT kappa) ∧
  DegenerateWRTKineticEnergyT (TetherKernelT kappa) ∧
  ProducesControllableNegativeFeedbackT kappa (TetherKernelT kappa) ∧
  (∀ s F, TetherKernelT kappa s KineticEnergy F = 0 ∧
    TetherKernelT kappa s KineticEnergy KineticEnergy = 0) ∧
  (∀ s F, TetherKernelT kappa s F F ≤ 0) ∧
  (∀ (u : FField) (lam : ℝ), fieldPairing u u ≠ 0 → Pi_u u (lam • u) = 0) ∧
  (∀ s F n, s.ω n ≠ 0 → velSlot F s n ≠ 0 → modeDensity kappa s F n < 0)

/-- `P3T`: Young absorption at `ε = κ/4` (algebra). -/
def P3T (kappa : ℝ) : Prop :=
  ∀ C M I₄ I₆ phi C_abs : ℝ,
    4 * C * M * I₄ ≤ (kappa / 4) * I₆ + C_abs * (M ^ 3 * phi ^ ((3 : ℝ) / 2)) →
    4 * C * M * I₄ - kappa * I₆ ≤ C_abs * (M ^ 3 * phi ^ ((3 : ℝ) / 2)) - (3 / 4) * kappa * I₆

/-- `P4T`: scalar cubic ODE ceiling. -/
def P4T : Prop :=
  ∀ (C κ'' : ℝ), 0 < C → 0 < κ'' → ∀ y : ℝ → ℝ,
    (∀ s ≥ (0 : ℝ), DifferentiableAt ℝ y s) →
    (∀ s ≥ (0 : ℝ), deriv y s ≤ C * (y s) ^ 2 - κ'' * (y s) ^ 3) →
    ∀ t, 0 ≤ t → y t ≤ max (y 0) (C / κ'')

/-- **Product theorem for the velocity-slot tether on `T³`**, for every `κ > 0`, with no
hypotheses. -/
theorem torus_velocity_tether_product_theorem {kappa : ℝ} (hκ : 0 < kappa) :
    P1T kappa ∧ P2T kappa ∧ P3T kappa ∧ P4T :=
  ⟨⟨uniqueness_T kappa, fun F G s c hc hF hG => step2_degree_T kappa F G s c hc hF hG,
      fun F G c hc hF hG B R n hn => step5_tetherKernelT kappa F G c hc hF hG B R n hn⟩,
    ⟨kineticEnergyCurlIdentity, tetherKernelT_comm kappa, tetherKernelT_C1 kappa,
      tetherKernelT_C2 kappa, tetherKernelT_C3 kappa,
      fun s F => ⟨(tetherKernelT_energy_conservation kappa s F).1,
        (tetherKernelT_energy_conservation kappa s F).2.2⟩,
      tetherKernelT_diag_nonpos hκ.le, Pi_u_smul_self,
      fun s F n => modeDensity_strict_neg hκ s F n⟩,
    fun C M I₄ I₆ phi C_abs h => young_absorption kappa C M I₄ I₆ phi C_abs h,
    comparison_ode_ceiling⟩

end TorusVelocityTether
