import HarmonicBalls.Proofs.Potential.GreenPoleL1Continuity

/-!
# Uniform absolute continuity of the zero-extended Green rows

For a bounded open planar set `U`, the zero-extended Green row `y ↦ G_U(x, y)` (value `0` off `U`,
as in `greenFunction`, the Green function of Armitage–Gardiner) has uniformly absolutely continuous
integrals: for every `ε > 0` there is `δ > 0`, depending only on `U` and `ε`, such that every
measurable `A` with `volume A < δ` satisfies `∫_A |G_U(x, y)| dy < ε` for every pole `x : ℂ`.

Proof outline (the small-disc plus off-disc estimate of `GreenPoleL1Continuity`). Let `U ⊆ B(0, R)`
with `R > 0`, and let `C` be the uniform local Green volume constant of
`exists_greenFunction_local_volume_bound`. For a radius `r > 0`, split `A` into `A ∩ B(x, r)` and
`A \ B(x, r)`.
* On the disc the row is nonnegative, so `∫_{A ∩ B(x, r)} G ≤ ∫_{B(x, r)} G ≤ C r² (1 + |log r|)`.
* Off the disc, `G_U(x, y) ≤ (2π)⁻¹ log⁺(2R / r)` by `greenFunction_le_posLog_div_norm`, so
  `∫_{A \ B(x, r)} G ≤ (2π)⁻¹ log⁺(2R / r) · volume(A).toReal`.
Choose `r` with `C r² (1 + |log r|) < ε / 2`, and then `δ = ε / (2 (M + 1))` with
`M = (2π)⁻¹ log⁺(2R / r)`.

Only `IsOpen U` and `Bornology.IsBounded U` are assumed; no boundary regularity and no literature
input is used. The local volume estimate and the potential-theoretic infrastructure use work of
Leonardo Bonanno, through the pinned Lattice-Probability (lean-v4.35) port.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Real Metric

/-- The zero-extended Green row is nonnegative, so its absolute value is the row itself. -/
theorem greenFunction_row_abs_eq {U : Set ℂ} (hUb : Bornology.IsBounded U) (x y : ℂ) :
    |greenFunction U x y| = greenFunction U x y :=
  abs_of_nonneg (greenFunction_nonneg hUb x y)

/-- Each zero-extended Green row is integrable on every set `A`: the global row integrability
`integrable_greenFunction_pole` of `GreenPoleL1Continuity`, restricted to `A`. -/
theorem greenFunction_row_integrableOn {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (x : ℂ) (A : Set ℂ) : IntegrableOn (greenFunction U x) A :=
  (integrable_greenFunction_pole hU hUb x).integrableOn

/-- Small-disc plus off-disc estimate for a Green row over a set of finite volume. If `U ⊆ B(0, R)`
with `R > 0`, `hloc` is the local volume bound with constant `C`, `r > 0` and `volume A < ∞`, then
`∫_A G_U(x, ·) ≤ C r² (1 + |log r|) + (2π)⁻¹ log⁺(2R / r) · volume(A).toReal`. -/
theorem setIntegral_greenFunction_row_le_ball_add_compl {U : Set ℂ} {R C : ℝ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hR : 0 < R) (hsub : U ⊆ ball (0 : ℂ) R)
    (hloc : ∀ (r : ℝ), 0 < r → ∀ x c : ℂ, IntegrableOn (greenFunction U x) (ball c r) ∧
      (∫ z in ball c r, greenFunction U x z) ≤ C * r ^ 2 * (1 + |Real.log r|))
    {r : ℝ} (hr : 0 < r) (x : ℂ) {A : Set ℂ} (hAfin : volume A < ⊤) :
    (∫ y in A, greenFunction U x y) ≤
      C * r ^ 2 * (1 + |Real.log r|) + (2 * Real.pi)⁻¹ * log⁺ (2 * R / r) * (volume A).toReal := by
  have hBm : MeasurableSet (ball x r) := measurableSet_ball
  have hint : IntegrableOn (greenFunction U x) A := greenFunction_row_integrableOn hU hUb x A
  have hsplit := integral_inter_add_sdiff hBm hint
  have hball : (∫ y in A ∩ ball x r, greenFunction U x y) ≤ C * r ^ 2 * (1 + |Real.log r|) := by
    have hmono : (∫ y in A ∩ ball x r, greenFunction U x y) ≤
        ∫ y in ball x r, greenFunction U x y :=
      setIntegral_mono_set (hloc r hr x x).1
        (Filter.Eventually.of_forall fun y => greenFunction_nonneg hUb x y)
        (Filter.Eventually.of_forall fun y (hy : y ∈ A ∩ ball x r) => hy.2)
    exact hmono.trans (hloc r hr x x).2
  have hM : 0 ≤ (2 * Real.pi)⁻¹ * log⁺ (2 * R / r) :=
    mul_nonneg (by positivity) posLog_nonneg
  have hbound : ∀ y ∈ A \ ball x r,
      ‖greenFunction U x y‖ ≤ (2 * Real.pi)⁻¹ * log⁺ (2 * R / r) := by
    intro y hy
    have hd : r ≤ ‖y - x‖ := by
      have h := hy.2
      rw [mem_ball, dist_eq_norm, not_lt] at h
      exact h
    rw [Real.norm_eq_abs, abs_of_nonneg (greenFunction_nonneg hUb x y)]
    refine (greenFunction_le_posLog_div_norm hR hsub x y).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.posLog_le_posLog ?_ ?_) (by positivity)
    · have h0 : (0 : ℝ) ≤ 2 * R / ‖y - x‖ := div_nonneg (by linarith) (norm_nonneg _)
      linarith
    · exact div_le_div_of_nonneg_left (by linarith) hr hd
  have hfin : volume (A \ ball x r) < ⊤ := lt_of_le_of_lt (measure_mono Set.sdiff_subset) hAfin
  have h1 := norm_setIntegral_le_of_norm_le_const hfin hbound
  rw [Real.norm_eq_abs] at h1
  have h2 : (volume (A \ ball x r)).toReal ≤ (volume A).toReal :=
    ENNReal.toReal_mono hAfin.ne (measure_mono Set.sdiff_subset)
  have hoff : (∫ y in A \ ball x r, greenFunction U x y) ≤
      (2 * Real.pi)⁻¹ * log⁺ (2 * R / r) * (volume A).toReal :=
    (le_abs_self _).trans (h1.trans (mul_le_mul_of_nonneg_left h2 hM))
  linarith [hsplit, hball, hoff]

/-- Uniform absolute continuity of the zero-extended Green rows of a bounded open planar set: for
every `ε > 0` there is `δ > 0`, independent of the measurable set `A` and of the pole `x`, with
`∫_A |G_U(x, y)| dy < ε` whenever `volume A < δ`. -/
theorem greenFunction_row_uniform_absolute_continuity {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ A : Set ℂ, MeasurableSet A →
      volume A < ENNReal.ofReal δ → ∀ x : ℂ, (∫ y in A, |greenFunction U x y|) < ε := by
  intro ε hε
  obtain ⟨R, hR, hsub⟩ := hUb.subset_ball_lt 0 (0 : ℂ)
  obtain ⟨C, -, hloc⟩ := exists_greenFunction_local_volume_bound hU hUb
  have hlim := tendsto_sq_mul_one_add_abs_log.const_mul C
  rw [mul_zero] at hlim
  have hev : ∀ᶠ r : ℝ in 𝓝[>] 0, C * (r ^ 2 * (1 + |Real.log r|)) < ε / 2 :=
    hlim.eventually_lt_const (half_pos hε)
  obtain ⟨r, hr_small, hr⟩ : ∃ r : ℝ, C * (r ^ 2 * (1 + |Real.log r|)) < ε / 2 ∧ 0 < r :=
    (hev.and self_mem_nhdsWithin).exists
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = (2 * Real.pi)⁻¹ * log⁺ (2 * R / r) := ⟨_, rfl⟩
  have hM : 0 ≤ M := by
    rw [hMdef]
    exact mul_nonneg (by positivity) posLog_nonneg
  have hK : (0 : ℝ) < M + 1 := by linarith
  have hK' : M + 1 ≠ 0 := hK.ne'
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = ε / (2 * (M + 1)) := ⟨_, rfl⟩
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact div_pos hε (by linarith)
  have hkey : (M + 1) * δ = ε / 2 := by
    rw [hδdef]
    field_simp
  refine ⟨δ, hδpos, ?_⟩
  intro A _hA hvol x
  have hfin : volume A < ⊤ := lt_trans hvol ENNReal.ofReal_lt_top
  have hest := setIntegral_greenFunction_row_le_ball_add_compl hU hUb hR hsub hloc hr x hfin
  rw [← hMdef] at hest
  have hδvol : (volume A).toReal < δ := ENNReal.toReal_lt_of_lt_ofReal hvol
  have hMδ : M * (volume A).toReal ≤ M * δ := mul_le_mul_of_nonneg_left hδvol.le hM
  have hlt : M * δ < ε / 2 := by nlinarith [hkey, hδpos]
  simp only [greenFunction_row_abs_eq hUb]
  linarith [hest, hMδ, hlt, hr_small]

end HarmonicBalls
