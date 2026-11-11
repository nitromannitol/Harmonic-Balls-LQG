import Mathlib
import HarmonicBalls.FirstPass.Frozen.S11i
import HarmonicBalls.Proofs.Sec5.OpenMeasureLaw

/-!
# Tonelli transfer of the marked DMS identity (Lemma 11.13, Step 8)

Input: the frozen marked whole-plane identity `DMSLemmaA10WholePlaneMarked` (`FirstPass/Frozen/S11i.lean`), the marked form of
Duplantier-Miller-Sheffield, Lemma A.10 with `D = B₁`, with mark `z`.

Output: if for Lebesgue-a.e. `z ∈ B₁` the shifted field `dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0)` lies in `S`
(with mark `z`) for `P`-a.e. `ω`, then for `P`-a.e. `ω` one has `(hC ω, z) ∈ S` for `μ_ω`-a.e. `z ∈ B₁`.

Proof: apply the marked identity to the indicator `Ψ` of `Sᶜ`. The right-hand side vanishes, because the inner `P`-integral
vanishes for a.e. `z ∈ B₁`. So the outer `P`-integral of the inner `μ_ω`-integral vanishes. Its integrand is
`P`-a.e. zero exactly when `Ψ` vanishes `μ_ω`-a.e. on `B₁`, which is the conclusion.

Extra hypothesis `hGae`: the outer integrand is `P`-AEMeasurable. This is the AEMeasurable form, as in
`LQGMeasureSquareMeasurableFrozen` (`FirstPass/Frozen/S11c.lean`), because the LQG measure is specified only almost surely.
It is NOT derivable from `IsLQGMeasureOfField`, `IsWholePlaneGFF` or `hS`: measurability of `ω ↦ μ ω S` is not implied
by the field-level inputs. It is an open item for the source-check.
-/

namespace HarmonicBalls.FirstPassS11iStep8Transfer

open MeasureTheory Metric Set
open scoped ENNReal
open ProbabilityTheory (Kernel IsFiniteKernel)

universe u

/-- **Tonelli transfer of the marked identity.** From `DMSLemmaA10WholePlaneMarked` (marked DMS Lemma A.10 for `B₁`), the
Lebesgue-a.e. statement `hleb` about the shifted field and mark `z` gives the `P`-a.s. `μ`-a.e. statement about `hC ω`. -/
theorem ae_ae_ball_of_marked_of_ae_volume {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hA10 : DMSLemmaA10WholePlaneMarked P γ hC hcirc μ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (S : Set (((ℂ → ℝ) → ℝ) × ℂ))
    (hS : MeasurableSet[(pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) Set.univ).prod inferInstance] S)
    (hleb : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball (0 : ℂ) 1 →
      ∀ᵐ ω ∂P, (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0), z) ∈ S)
    (hGae : AEMeasurable (fun ω => ∫⁻ z in ball (0 : ℂ) 1,
      Sᶜ.indicator (fun _ => (1 : ℝ≥0∞)) (hC ω, z) ∂(μ ω)) P) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), z ∈ ball (0 : ℂ) 1 → (hC ω, z) ∈ S := by
  classical
  set Ψ : (((ℂ → ℝ) → ℝ) × ℂ) → ℝ≥0∞ := Sᶜ.indicator (fun _ => (1 : ℝ≥0∞)) with hΨdef
  have hΨ : Measurable[(pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) Set.univ).prod inferInstance] Ψ :=
    measurable_const.indicator hS.compl
  -- the right-hand side of the marked identity vanishes
  have hR : ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ ω, Ψ (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0), z) ∂P ∂volume = 0 := by
    have hae : ∀ᵐ z ∂(volume.restrict (ball (0 : ℂ) 1)),
        ∫⁻ ω, Ψ (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0), z) ∂P = 0 := by
      rw [ae_restrict_iff' measurableSet_ball]
      filter_upwards [hleb] with z hz hzball
      have h0 : ∀ᵐ ω ∂P, Ψ (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0), z) = 0 := by
        filter_upwards [hz hzball] with ω hω
        exact Set.indicator_of_notMem (by simpa using hω) _
      rw [lintegral_congr_ae (g := fun _ => (0 : ℝ≥0∞)) h0, lintegral_zero]
    rw [lintegral_congr_ae (g := fun _ => (0 : ℝ≥0∞)) hae, lintegral_zero]
  -- the marked identity, applied to Ψ, gives the vanishing of the left-hand side
  have hid := hA10 hGFF hμ Ψ hΨ
  have hL : ∫⁻ ω, ∫⁻ z in ball (0 : ℂ) 1, Ψ (hC ω, z) ∂(μ ω) ∂P = 0 := hid.trans hR
  have hG : (fun ω => ∫⁻ z in ball (0 : ℂ) 1, Ψ (hC ω, z) ∂(μ ω)) =ᵐ[P] 0 :=
    (lintegral_eq_zero_iff' hGae).1 hL
  filter_upwards [hG] with ω hω
  -- for such ω, the `μ ω`-integral over `B₁` of `Ψ (hC ω, ·)` vanishes
  have hmz : Measurable fun z : ℂ => Ψ (hC ω, z) :=
    hΨ.comp (measurable_const.prodMk measurable_id)
  have hz0 : (fun z : ℂ => Ψ (hC ω, z)) =ᵐ[(μ ω).restrict (ball (0 : ℂ) 1)] 0 :=
    (lintegral_eq_zero_iff' hmz.aemeasurable).1 hω
  have hz0' : ∀ᵐ z ∂(μ ω), z ∈ ball (0 : ℂ) 1 → Ψ (hC ω, z) = 0 :=
    (ae_restrict_iff' measurableSet_ball).1 hz0
  filter_upwards [hz0'] with z hz hzball
  by_contra hnot
  have h1 : Ψ (hC ω, z) = 1 := Set.indicator_of_mem (show (hC ω, z) ∈ Sᶜ from hnot) _
  exact one_ne_zero (h1.symm.trans (hz hzball))

/-!
## Measurability of the failure mass (discharges `hGae`)

`μ` is `P`-a.e. equal to a measurable version `μ'` (`IsWholePlaneGFF.aemeasurable_lqgMeasure`). The measure
`ν ω := (1 + μ' ω B₁)⁻¹ • (μ' ω)|_{B₁}` has mass at most `1`, so it is a finite kernel and the marked integral
against it is measurable (`Measurable.lintegral_kernel_prod_right'`). The ratio of the two integrals is
`1 + μ' ω B₁`, which is finite because the Radon measure `μ ω` is locally finite (`IsLQGLimit`).
-/

/-- Pairings of a whole-plane GFF make `ω ↦ hC ω` measurable into the pairing σ-algebra of the test functions on `univ`. -/
theorem measurable_hC_pairingUniv {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc) :
    @Measurable Ω ((ℂ → ℝ) → ℝ) _ (pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) Set.univ) hC := by
  refine measurable_iff_comap_le.2 ?_
  unfold pairingSigmaAlgebra
  simp only [MeasurableSpace.comap_iSup]
  refine iSup₂_le fun φ hφ => ?_
  rw [MeasurableSpace.comap_comp]
  exact (hGFF.measurable_pairing φ hφ).comap_le

/-- Elementary bound `(1 + x)⁻¹ * x ≤ 1` in `ℝ≥0∞`. -/
theorem inv_one_add_mul_le_one (x : ℝ≥0∞) : (1 + x)⁻¹ * x ≤ 1 := by
  by_cases hx : x = ⊤
  · simp [hx]
  · have h1 : (1 + x) ≠ ⊤ := ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hx⟩
    have h0 : (1 + x) ≠ 0 := (zero_lt_one.trans_le le_self_add).ne'
    calc (1 + x)⁻¹ * x ≤ (1 + x)⁻¹ * (1 + x) := mul_le_mul_of_nonneg_left le_add_self zero_le
      _ = 1 := ENNReal.inv_mul_cancel h0 h1

/-- Measurability in `ω` of the marked failure mass `∫⁻_{B₁} 1_{Sᶜ}(h_ω, z) μ_ω(dz)`, for the whole-plane GFF and its
LQG measure of `α₀ = 0`. Only the a.s. local finiteness of `μ` and the measurable version of `μ` are used. -/
theorem aemeasurable_ball_lintegral_marked {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (S : Set (((ℂ → ℝ) → ℝ) × ℂ))
    (hS : MeasurableSet[(pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) Set.univ).prod inferInstance] S) :
    AEMeasurable (fun ω => ∫⁻ z in ball (0 : ℂ) 1, Sᶜ.indicator (fun _ => (1 : ℝ≥0∞)) (hC ω, z) ∂(μ ω)) P := by
  classical
  have hAEM : AEMeasurable μ P := hGFF.aemeasurable_lqgMeasure hμ
  set μ' : Ω → Measure ℂ := hAEM.mk μ with hμ'def
  have hμ'm : Measurable μ' := hAEM.measurable_mk
  have hae : ∀ᵐ ω ∂P, μ ω = μ' ω := hAEM.ae_eq_mk
  -- `μ ω B₁ < ∞` almost surely: `μ ω` is Radon (`IsLQGLimit`)
  have hfin : ∀ᵐ ω ∂P, μ ω (ball (0 : ℂ) 1) < ⊤ := by
    have h' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage 0 (hcirc ω)) (μ ω) := hμ
    filter_upwards [h'] with ω hω
    have := hω.isLocallyFiniteMeasure
    exact measure_ball_lt_top
  have hx : Measurable fun ω => μ' ω (ball (0 : ℂ) 1) :=
    (Measure.measurable_coe measurableSet_ball).comp hμ'm
  have hc : Measurable fun ω => (1 + μ' ω (ball (0 : ℂ) 1))⁻¹ :=
    (measurable_const.add hx).inv
  -- the finite kernel `ν ω = (1 + μ' ω B₁)⁻¹ • (μ' ω)|_{B₁}`
  let ν : Ω → Measure ℂ := fun ω => (1 + μ' ω (ball (0 : ℂ) 1))⁻¹ • (μ' ω).restrict (ball (0 : ℂ) 1)
  have hν : Measurable ν := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp only [ν, Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul]
    exact hc.mul ((Measure.measurable_coe (hs.inter measurableSet_ball)).comp hμ'm)
  let κ : Kernel Ω ℂ := ⟨ν, hν⟩
  have hbound : ∀ ω, κ ω Set.univ ≤ 1 := fun ω => by
    show ((1 + μ' ω (ball (0 : ℂ) 1))⁻¹ • (μ' ω).restrict (ball (0 : ℂ) 1)) Set.univ ≤ 1
    rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
    exact inv_one_add_mul_le_one _
  have : IsFiniteKernel κ := ⟨⟨1, ENNReal.one_lt_top, hbound⟩⟩
  -- joint measurability of the marked integrand and measurability of the kernel integral
  have hCm := measurable_hC_pairingUniv hGFF
  have hΨ : Measurable[(pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) Set.univ).prod inferInstance]
      (Sᶜ.indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hS.compl
  have hF : Measurable fun p : Ω × ℂ => Sᶜ.indicator (fun _ => (1 : ℝ≥0∞)) (hC p.1, p.2) :=
    hΨ.comp ((hCm.comp measurable_fst).prodMk measurable_snd)
  have hH : Measurable fun ω => ∫⁻ z, Sᶜ.indicator (fun _ => (1 : ℝ≥0∞)) (hC ω, z) ∂(κ ω) :=
    hF.lintegral_kernel_prod_right' (κ := κ)
  -- the identity with the `μ'`-integral over `B₁`, `P`-a.s.
  have heq : (fun ω => ∫⁻ z in ball (0 : ℂ) 1, Sᶜ.indicator (fun _ => (1 : ℝ≥0∞)) (hC ω, z) ∂(μ ω))
      =ᵐ[P] fun ω => (1 + μ' ω (ball (0 : ℂ) 1)) *
        ∫⁻ z, Sᶜ.indicator (fun _ => (1 : ℝ≥0∞)) (hC ω, z) ∂(κ ω) := by
    filter_upwards [hae, hfin] with ω h1 h2
    rw [h1] at h2 ⊢
    have ha0 : (1 + μ' ω (ball (0 : ℂ) 1)) ≠ 0 := (zero_lt_one.trans_le le_self_add).ne'
    have haT : (1 + μ' ω (ball (0 : ℂ) 1)) ≠ ⊤ := ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, h2.ne⟩
    have hκ : κ ω = (1 + μ' ω (ball (0 : ℂ) 1))⁻¹ • (μ' ω).restrict (ball (0 : ℂ) 1) := rfl
    rw [hκ, lintegral_smul_measure, smul_eq_mul, ← mul_assoc, ENNReal.mul_inv_cancel ha0 haT, one_mul]
  exact ((measurable_const.add hx).mul hH).aemeasurable.congr heq.symm

/-- **Tonelli transfer, hypothesis-free form.** The statement of `ae_ae_ball_of_marked_of_ae_volume` with the
measurability hypothesis `hGae` discharged by `aemeasurable_ball_lintegral_marked`. -/
theorem ae_ae_ball_of_marked_of_ae_volume' {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hA10 : DMSLemmaA10WholePlaneMarked P γ hC hcirc μ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (S : Set (((ℂ → ℝ) → ℝ) × ℂ))
    (hS : MeasurableSet[(pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) Set.univ).prod inferInstance] S)
    (hleb : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball (0 : ℂ) 1 →
      ∀ᵐ ω ∂P, (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0), z) ∈ S) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), z ∈ ball (0 : ℂ) 1 → (hC ω, z) ∈ S :=
  ae_ae_ball_of_marked_of_ae_volume P γ hC hcirc μ hA10 hGFF hμ S hS hleb
    (aemeasurable_ball_lintegral_marked P γ hC hcirc μ hGFF hμ S hS)

end HarmonicBalls.FirstPassS11iStep8Transfer
