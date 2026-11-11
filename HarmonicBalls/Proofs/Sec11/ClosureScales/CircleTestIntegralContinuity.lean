import HarmonicBalls.Defs.Laplacian
import HarmonicBalls.Defs.LQG
import HarmonicBalls.Proofs.Sec11.ClosureScales.CountableCircleDecoder

/-!
# Continuity of the circle-test integrals on the carrier `C(CircleDomain, ℝ)`

Source. Written argument lines 1046-1062. For a test function `φ`, the displayed
limit `lim_n ∫ c(2^{-n}, z) φ(z) d²z` (line 1052) is accompanied by the claim "Each integral is a continuous function of
`c` and the limit, where it exists, is Borel" (line 1054). This file formalizes the continuity of the integrals jointly in the
radius `r > 0` and in the profile `F : C(CircleDomain, ℝ)`, where `CircleDomain = {p : ℝ × ℂ // 0 < p.1}`.

Carrier and conventions. `CircleDomain` and the compact-open topology and Borel σ-algebra of `C(CircleDomain, ℝ)` come
from `CountableCircleDecoder.lean`. `IsTestFunction Set.univ φ` is the Defs predicate of `Defs/Laplacian.lean`. The
integrals are against Lebesgue measure `volume` on `ℂ`. No probability space, reconstruction, bound at infinity or
domination premise is assumed; the domination used below is proved from compactness.

Main results.
* `integrable_circleTestIntegrand`: for `r > 0` and `F : C(CircleDomain, ℝ)`, `z ↦ F ⟨(r, z), hr⟩ * φ z` is integrable.
* `continuous_circleTestIntegral`: `(r, F) ↦ ∫ z, F ⟨(r, z), _⟩ * φ z` is continuous on
  `{r : ℝ // 0 < r} × C(CircleDomain, ℝ)`, the second factor with the compact-open topology.
* `continuous_circleTestIntegral_fixed`, `measurable_circleTestIntegral_fixed`: the fixed-radius consequence, continuous
  and Borel in `F`.
* `measurable_circleTestIntegral`: joint Borel measurability.
* `measurable_limsup_circleTestIntegral`: `F ↦ limsup_n ∫ z, F ⟨(dyadicScale n, z), _⟩ * φ z` is Borel.

Route. Mathlib's `MeasureTheory.continuous_parametric_integral_of_continuous` (Bochner/Set.lean) requires a locally
compact parameter space, and `C(CircleDomain, ℝ)` is not locally compact. The continuity is therefore proved with
`MeasureTheory.continuousAt_of_dominated` (Bochner/Basic.lean). At a point `q₀ = (r₀, F₀)` the dominating function is
`z ↦ M * ‖φ z‖`, where `M` bounds `F` on the compact positive-radius box `[r₀/2, 2 r₀] × tsupport φ` of `CircleDomain`
for all `F` in an open neighbourhood of `F₀` (`ContinuousMap.isOpen_setOfPred_mapsTo`).
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace HarmonicBalls

/-- Compact positive-radius boxes in `CircleDomain`. For `0 < a` and a compact `K ⊆ ℂ`, some compact `S ⊆ CircleDomain`
contains every point `(r, z)` with `a ≤ r ≤ b` and `z ∈ K`. -/
theorem exists_isCompact_circleDomain {a b : ℝ} (ha : 0 < a) {K : Set ℂ} (hK : IsCompact K) :
    ∃ S : Set CircleDomain, IsCompact S ∧
      ∀ r : ℝ, a ≤ r → r ≤ b → ∀ z ∈ K, ∀ hr : 0 < r, (⟨(r, z), hr⟩ : CircleDomain) ∈ S := by
  have : CompactSpace (Icc a b ×ˢ K : Set (ℝ × ℂ)) := isCompact_iff_compactSpace.mp (isCompact_Icc.prod hK)
  have hpos : ∀ x : (Icc a b ×ˢ K : Set (ℝ × ℂ)), 0 < (x : ℝ × ℂ).1 :=
    fun x => lt_of_lt_of_le ha x.2.1.1
  have hg : Continuous fun x : (Icc a b ×ˢ K : Set (ℝ × ℂ)) => (⟨(x : ℝ × ℂ), hpos x⟩ : CircleDomain) :=
    Continuous.subtype_mk continuous_subtype_val hpos
  refine ⟨Set.range fun x : (Icc a b ×ˢ K : Set (ℝ × ℂ)) => (⟨(x : ℝ × ℂ), hpos x⟩ : CircleDomain),
    isCompact_range hg, ?_⟩
  intro r hra hrb z hz hr
  exact ⟨⟨(r, z), mk_mem_prod ⟨hra, hrb⟩ hz⟩, rfl⟩

/-- Continuity in `(r, F)` of the evaluation `F ⟨(r, z), _⟩` at a fixed `z`. -/
theorem continuous_circleTestIntegrand_q (z : ℂ) :
    Continuous fun q : {r : ℝ // 0 < r} × C(CircleDomain, ℝ) => q.2 ⟨(q.1.val, z), q.1.property⟩ := by
  have hp : Continuous fun q : {r : ℝ // 0 < r} × C(CircleDomain, ℝ) =>
      (⟨(q.1.val, z), q.1.property⟩ : CircleDomain) :=
    Continuous.subtype_mk ((continuous_subtype_val.comp continuous_fst).prodMk continuous_const)
      fun q => q.1.property
  exact continuous_eval.comp (continuous_snd.prodMk hp)

/-- For a fixed radius, `z ↦ F ⟨(r, z), _⟩ * φ z` is continuous when `φ` is continuous. -/
theorem continuous_circleTestIntegrand_z {φ : ℂ → ℝ} (hφ : Continuous φ) (r : {r : ℝ // 0 < r})
    (F : C(CircleDomain, ℝ)) : Continuous fun z : ℂ => F ⟨(r.1, z), r.2⟩ * φ z := by
  have hp : Continuous fun z : ℂ => (⟨(r.1, z), r.2⟩ : CircleDomain) :=
    Continuous.subtype_mk (continuous_const.prodMk continuous_id) fun _ => r.2
  exact (F.continuous.comp hp).mul hφ

/-- **Integrability.** For a test function `φ`, `r > 0` and `F : C(CircleDomain, ℝ)`, the function
`z ↦ F ⟨(r, z), hr⟩ * φ z` is integrable on `ℂ`: it is continuous and supported in `tsupport φ`. -/
theorem integrable_circleTestIntegrand {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) {r : ℝ} (hr : 0 < r)
    (F : C(CircleDomain, ℝ)) : Integrable (fun z => F ⟨(r, z), hr⟩ * φ z) := by
  have hcs : HasCompactSupport (fun z => F ⟨(r, z), hr⟩ * φ z) :=
    HasCompactSupport.intro hφ.2.1.isCompact fun z hz => by simp [image_eq_zero_of_notMem_tsupport hz]
  exact (continuous_circleTestIntegrand_z hφ.1.continuous ⟨r, hr⟩ F).integrable_of_hasCompactSupport hcs

/-- **Joint continuity.** For a test function `φ`, the map `(r, F) ↦ ∫ z, F ⟨(r, z), _⟩ * φ z` is continuous on
`{r : ℝ // 0 < r} × C(CircleDomain, ℝ)`, the second factor carrying the compact-open topology. -/
theorem continuous_circleTestIntegral {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) :
    Continuous fun q : {r : ℝ // 0 < r} × C(CircleDomain, ℝ) =>
      ∫ z, q.2 ⟨(q.1.val, z), q.1.property⟩ * φ z := by
  have hφc : Continuous φ := hφ.1.continuous
  have hKc : IsCompact (tsupport φ) := hφ.2.1.isCompact
  have hφint : Integrable φ := hφc.integrable_of_hasCompactSupport hφ.2.1
  rw [continuous_iff_continuousAt]
  intro q0
  -- compact positive-radius box around `q0.1` and a uniform bound of `q0.2` on it
  obtain ⟨S, hSc, hS⟩ := exists_isCompact_circleDomain (a := q0.1.val / 2) (b := 2 * q0.1.val)
    (by linarith [q0.1.property]) hKc
  obtain ⟨C, hC⟩ := hSc.exists_bound_of_continuousOn q0.2.continuous.continuousOn
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ p ∈ S, ‖q0.2 p‖ < M := ⟨C + 1, fun p hp => by linarith [hC p hp]⟩
  -- an open neighbourhood of `q0`: radius in `(r₀/2, 2 r₀)`, profile bounded by `M` on `S`
  have hWopen : IsOpen {q : {r : ℝ // 0 < r} × C(CircleDomain, ℝ) |
      q.1.val ∈ Ioo (q0.1.val / 2) (2 * q0.1.val) ∧ MapsTo q.2 S (Ioo (-M) M)} :=
    (isOpen_Ioo.preimage (continuous_subtype_val.comp continuous_fst)).inter
      ((ContinuousMap.isOpen_setOfPred_mapsTo hSc isOpen_Ioo).preimage continuous_snd)
  have hq0W : q0 ∈ {q : {r : ℝ // 0 < r} × C(CircleDomain, ℝ) |
      q.1.val ∈ Ioo (q0.1.val / 2) (2 * q0.1.val) ∧ MapsTo q.2 S (Ioo (-M) M)} := by
    refine ⟨⟨by linarith [q0.1.property], by linarith [q0.1.property]⟩, ?_⟩
    intro p hp
    have h := hM p hp
    rw [Real.norm_eq_abs] at h
    exact abs_lt.mp h
  have hbound : ∀ q ∈ {q : {r : ℝ // 0 < r} × C(CircleDomain, ℝ) |
      q.1.val ∈ Ioo (q0.1.val / 2) (2 * q0.1.val) ∧ MapsTo q.2 S (Ioo (-M) M)}, ∀ z : ℂ,
      ‖q.2 ⟨(q.1.val, z), q.1.property⟩ * φ z‖ ≤ M * ‖φ z‖ := by
    rintro q ⟨hq1, hq2⟩ z
    obtain ⟨hA, hB⟩ := hq1
    by_cases hz : z ∈ tsupport φ
    · have hp : (⟨(q.1.val, z), q.1.property⟩ : CircleDomain) ∈ S :=
        hS q.1.val hA.le hB.le z hz q.1.property
      obtain ⟨hF1, hF2⟩ := hq2 hp
      have hF' : ‖q.2 ⟨(q.1.val, z), q.1.property⟩‖ ≤ M := by
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨hF1.le, hF2.le⟩
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hF' (norm_nonneg _)
    · simp [image_eq_zero_of_notMem_tsupport hz]
  have hWmem := hWopen.mem_nhds hq0W
  have hdom : ∀ᶠ q in 𝓝 q0, ∀ᵐ z ∂(volume : Measure ℂ),
      ‖q.2 ⟨(q.1.val, z), q.1.property⟩ * φ z‖ ≤ M * ‖φ z‖ := by
    filter_upwards [hWmem] with q hq
    exact ae_of_all _ (hbound q hq)
  have hmeas : ∀ᶠ q in 𝓝 q0, AEStronglyMeasurable
      (fun z => q.2 ⟨(q.1.val, z), q.1.property⟩ * φ z) (volume : Measure ℂ) :=
    Eventually.of_forall fun q => (continuous_circleTestIntegrand_z hφc q.1 q.2).aestronglyMeasurable
  have hcont : ∀ᵐ z ∂(volume : Measure ℂ), ContinuousAt
      (fun q : {r : ℝ // 0 < r} × C(CircleDomain, ℝ) => q.2 ⟨(q.1.val, z), q.1.property⟩ * φ z) q0 :=
    ae_of_all _ fun z => ((continuous_circleTestIntegrand_q z).mul continuous_const).continuousAt
  exact continuousAt_of_dominated hmeas hdom (hφint.norm.const_mul M) hcont

/-- **Fixed-radius continuity.** For `r > 0`, `F ↦ ∫ z, F ⟨(r, z), hr⟩ * φ z` is continuous on
`C(CircleDomain, ℝ)` (compact-open topology). -/
theorem continuous_circleTestIntegral_fixed {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) {r : ℝ} (hr : 0 < r) :
    Continuous fun F : C(CircleDomain, ℝ) => ∫ z, F ⟨(r, z), hr⟩ * φ z :=
  (continuous_circleTestIntegral hφ).comp
    (continuous_const.prodMk continuous_id :
      Continuous fun F : C(CircleDomain, ℝ) => ((⟨r, hr⟩ : {r : ℝ // 0 < r}), F))

/-- **Fixed-radius Borel measurability** of `F ↦ ∫ z, F ⟨(r, z), hr⟩ * φ z` on `C(CircleDomain, ℝ)`. -/
theorem measurable_circleTestIntegral_fixed {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) {r : ℝ} (hr : 0 < r) :
    Measurable fun F : C(CircleDomain, ℝ) => ∫ z, F ⟨(r, z), hr⟩ * φ z :=
  (continuous_circleTestIntegral_fixed hφ hr).measurable

/-- **Joint Borel measurability** of `(r, F) ↦ ∫ z, F ⟨(r, z), _⟩ * φ z`. -/
theorem measurable_circleTestIntegral {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) :
    Measurable fun q : {r : ℝ // 0 < r} × C(CircleDomain, ℝ) =>
      ∫ z, q.2 ⟨(q.1.val, z), q.1.property⟩ * φ z :=
  (continuous_circleTestIntegral hφ).measurable

/-- **Borel measurability of the limsup along `dyadicScale`.** The map
`F ↦ limsup_n ∫ z, F ⟨(dyadicScale n, z), _⟩ * φ z` is Borel on `C(CircleDomain, ℝ)`; the index is `n : ℕ`, so
`Measurable.limsup` applies to the countable family of fixed-radius integrals. -/
theorem measurable_limsup_circleTestIntegral {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) :
    Measurable fun F : C(CircleDomain, ℝ) =>
      Filter.limsup (fun n : ℕ => ∫ z, F ⟨(dyadicScale n, z), dyadicScale_pos n⟩ * φ z) atTop :=
  Measurable.limsup fun n => measurable_circleTestIntegral_fixed hφ (dyadicScale_pos n)

end HarmonicBalls

end
