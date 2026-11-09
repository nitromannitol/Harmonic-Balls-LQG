import HarmonicBalls.Audit.GreenSubharmonicTestClass
import HarmonicBalls.Proofs.Potential.GeneralDomainGreenLaplacian
import HarmonicBalls.Proofs.Potential.BoundedDensityGreenContinuity
import HarmonicBalls.Proofs.Potential.Fundamental

/-! # Smooth compactly supported functions lie in the bounded subharmonic test class

Bou-Rabee and Gwynne, *Harmonic balls in Liouville quantum gravity* (arXiv:2208.11795), bounded-test ingredient of the
bounded Jensen representative lemma (steps3:230-315; constructive witness steps3:261-280). Let `S ⊆ ℂ` be open and
bounded, `z ∈ S`, and let `F : ℂ → ℝ` be `C^∞` with compact support and `ΔF ≥ 0` on `S`. Then `F` lies in
`boundedSubharmonicBallTestClass S z`. The witnesses are: the bounded open ball `O = B(0, R₀ + 1)` containing
`closure S` and `tsupport F`; the compact `K = closedBall 0 R₀`; the harmonic correction `q = 0`; and the finite source
measures `ν₁ = (-ΔF)₊ dx` and `ν₂ = (ΔF)₊ dx`. Their densities are bounded and compactly supported, `ν₁` vanishes on `S`
(because `ΔF ≥ 0` there) and `ν₂` has no atom at `z`.

The identity `F = G_O ν₁ - G_O ν₂` of Green potentials (Armitage–Gardiner, *Classical Potential Theory*, §4.2) holds at
every point of `ℂ`, not only almost everywhere. It is read off from the distributional Green identity
`Δ G_O(x,·) = -δ_x` (`hasLaplacian_greenFunction_bounded_domain`), a pointwise identity in the pole `x`. Test functions
are `C^∞` as in `IsTestFunction`; a hypothesis `C^ω` would imply the `C^∞` hypothesis used here.

The potential-theoretic infrastructure reached through the import closure use work of Leonardo Bonanno, through the
pinned Lattice-Probability (lean-v4.35) port.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Laplacian
open scoped ContDiff

/-- Pointwise Green identity for a `C^∞` function with compact support in `O`: for every pole `x ∈ ℂ`,
`∫ G_O(x,y) ΔF(y) dy = -F(x)`. For `x ∈ O` this is `Δ G_O(x,·) = -δ_x` tested against `F`
(Armitage–Gardiner §4.1); for `x ∉ O` both sides vanish. -/
theorem integral_greenFunction_mul_laplacian_eq {O : Set ℂ} (hO : IsOpen O) (hOb : Bornology.IsBounded O)
    {F : ℂ → ℝ} (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F) (hFO : tsupport F ⊆ O) (x : ℂ) :
    ∫ y, greenFunction O x y * Laplacian.laplacian F y = -F x := by
  by_cases hx : x ∈ O
  · have hφ : IsTestFunction O F := ⟨hF, hFc, hFO⟩
    obtain ⟨-, -, h⟩ := (hasLaplacian_greenFunction_bounded_domain hO hOb hx).2 F hφ
    rw [integral_zero_measure, integral_dirac, zero_sub] at h
    exact h
  · have hG : ∀ y, greenFunction O x y = 0 := fun y => by simp [greenFunction, hx]
    have hFx : F x = 0 := by
      by_contra h
      exact hx (hFO (subset_tsupport F (Function.mem_support.mpr h)))
    simp [hG, hFx]

/-- The positive parts of `-t` and `t` differ by `-t`: `(-t)₊ - t₊ = -t`. -/
theorem max_neg_sub_max_eq_neg (t : ℝ) : max (-t) 0 - max t 0 = -t := by
  simp only [max_def]
  split_ifs <;> linarith

/-- **Smooth compactly supported test functions lie in the bounded test class.** Let `S ⊆ ℂ` be open and bounded,
`z ∈ S`, and let `F : ℂ → ℝ` be `C^∞` with compact support and `0 ≤ ΔF` on `S`. Then `F` belongs to
`boundedSubharmonicBallTestClass S z`; the conditions of the class at the pole `z` hold for every `z`, so `z ∈ S` is
kept only to match the stated hypotheses. Witnesses: `O = B(0, R₀ + 1)`, `K = closedBall 0 R₀` (where
`closure S ∪ tsupport F ⊆ closedBall 0 R₀`), `q = 0`, `ν₁ = (-ΔF)₊ dx` and `ν₂ = (ΔF)₊ dx`. -/
theorem mem_boundedSubharmonicBallTestClass_of_smooth_compactSupport (S : Set ℂ) (z : ℂ)
    (hS : IsOpen S) (hSb : Bornology.IsBounded S) (_hz : z ∈ S) (F : ℂ → ℝ) (hF : ContDiff ℝ ∞ F)
    (hFc : HasCompactSupport F) (hsub : ∀ x ∈ S, 0 ≤ Laplacian.laplacian F x) :
    F ∈ boundedSubharmonicBallTestClass S z := by
  -- Step 1: a bounded open ball `O` and a compact `K ⊆ O` containing `closure S` and `tsupport F`
  obtain ⟨R₀, hR₀⟩ := (hSb.closure.union hFc.isCompact.isBounded).subset_closedBall (0 : ℂ)
  have hcl : closure S ⊆ closedBall (0 : ℂ) R₀ := subset_union_left.trans hR₀
  have hsupp : tsupport F ⊆ closedBall (0 : ℂ) R₀ := subset_union_right.trans hR₀
  set O : Set ℂ := ball (0 : ℂ) (R₀ + 1) with hO_def
  have hKO : closedBall (0 : ℂ) R₀ ⊆ O := closedBall_subset_ball (lt_add_one R₀)
  have hclO : closure S ⊆ O := hcl.trans hKO
  have hFO : tsupport F ⊆ O := hsupp.trans hKO
  have hOo : IsOpen O := isOpen_ball
  have hOb : Bornology.IsBounded O := isBounded_ball
  -- Step 2: regularity of `ΔF` and its support
  have hF2 : ContDiff ℝ 2 F := hF.of_le (WithTop.coe_le_coe.mpr le_top)
  have hΔc : Continuous (Laplacian.laplacian F) := continuous_laplacian_of_contDiff hF2
  have hΔs : HasCompactSupport (Laplacian.laplacian F) := hasCompactSupport_laplacian hFc
  have hΔout : ∀ y, y ∉ tsupport F → Laplacian.laplacian F y = 0 := fun y hy => by
    by_contra h
    exact hy (support_laplacian_subset F (Function.mem_support.mpr h))
  -- Step 3: the positive-part densities
  set a : ℂ → ℝ := fun y => max (-Laplacian.laplacian F y) 0 with ha_def
  set b : ℂ → ℝ := fun y => max (Laplacian.laplacian F y) 0 with hb_def
  have ha_nonneg : ∀ y, 0 ≤ a y := fun y => le_max_right _ _
  have hb_nonneg : ∀ y, 0 ≤ b y := fun y => le_max_right _ _
  have ha_cont : Continuous a := hΔc.neg.max continuous_const
  have hb_cont : Continuous b := hΔc.max continuous_const
  have ha_cs : HasCompactSupport a := hΔs.comp_left (g := fun t : ℝ => max (-t) 0) (by simp)
  have hb_cs : HasCompactSupport b := hΔs.comp_left (g := fun t : ℝ => max t 0) (by simp)
  have ha_int : Integrable a := ha_cont.integrable_of_hasCompactSupport ha_cs
  have hb_int : Integrable b := hb_cont.integrable_of_hasCompactSupport hb_cs
  -- Step 4: the source measures `ν₁ = a dx` and `ν₂ = b dx`
  set ν₁ : Measure ℂ := volume.withDensity (fun y => ENNReal.ofReal (a y)) with hν₁_def
  set ν₂ : Measure ℂ := volume.withDensity (fun y => ENNReal.ofReal (b y)) with hν₂_def
  have hν₁_fin : IsFiniteMeasure ν₁ := isFiniteMeasure_withDensity_ofReal ha_int.hasFiniteIntegral
  have hν₂_fin : IsFiniteMeasure ν₂ := isFiniteMeasure_withDensity_ofReal hb_int.hasFiniteIntegral
  have hzeroK : ∀ y ∈ (closedBall (0 : ℂ) R₀)ᶜ, ENNReal.ofReal (a y) = 0 ∧ ENNReal.ofReal (b y) = 0 := by
    intro y hy
    have h0 : Laplacian.laplacian F y = 0 := hΔout y (fun h => hy (hsupp h))
    simp [ha_def, hb_def, h0]
  have hν₁K : ν₁ (closedBall (0 : ℂ) R₀)ᶜ = 0 := by
    rw [hν₁_def, withDensity_apply _ measurableSet_closedBall.compl]
    refine (setLIntegral_congr_fun (g := fun _ => 0) measurableSet_closedBall.compl
      (fun y hy => (hzeroK y hy).1)).trans ?_
    simp
  have hν₂K : ν₂ (closedBall (0 : ℂ) R₀)ᶜ = 0 := by
    rw [hν₂_def, withDensity_apply _ measurableSet_closedBall.compl]
    refine (setLIntegral_congr_fun (g := fun _ => 0) measurableSet_closedBall.compl
      (fun y hy => (hzeroK y hy).2)).trans ?_
    simp
  have hν₁S : ν₁ S = 0 := by
    rw [hν₁_def, withDensity_apply _ hS.measurableSet]
    refine (setLIntegral_congr_fun (g := fun _ => 0) hS.measurableSet (fun y hy => ?_)).trans ?_
    · have hneg : -Laplacian.laplacian F y ≤ 0 := by linarith [hsub y hy]
      simp [ha_def, max_eq_right hneg]
    · simp
  have hν₂z : ν₂ {z} = 0 := withDensity_absolutelyContinuous volume _ (measure_singleton z)
  -- Step 5: integrability of the Green functions against the bounded densities
  obtain ⟨Ma, hMa⟩ := ha_cont.bounded_above_of_compact_support ha_cs
  obtain ⟨Mb, hMb⟩ := hb_cont.bounded_above_of_compact_support hb_cs
  have hint_a : ∀ x : ℂ, Integrable (fun y => greenFunction O x y * a y) := fun x =>
    integrable_greenFunction_mul_bdd hOo hOb ha_cont.aestronglyMeasurable
      (ae_of_all _ fun y => by simpa [Real.norm_eq_abs] using hMa y) x
  have hint_b : ∀ x : ℂ, Integrable (fun y => greenFunction O x y * b y) := fun x =>
    integrable_greenFunction_mul_bdd hOo hOb hb_cont.aestronglyMeasurable
      (ae_of_all _ fun y => by simpa [Real.norm_eq_abs] using hMb y) x
  have hameas : Measurable (fun y => ENNReal.ofReal (a y)) :=
    ENNReal.measurable_ofReal.comp ha_cont.measurable
  have hbmeas : Measurable (fun y => ENNReal.ofReal (b y)) :=
    ENNReal.measurable_ofReal.comp hb_cont.measurable
  have halt : ∀ᵐ y ∂(volume : Measure ℂ), ENNReal.ofReal (a y) < ⊤ :=
    ae_of_all _ fun y => ENNReal.ofReal_lt_top
  have hblt : ∀ᵐ y ∂(volume : Measure ℂ), ENNReal.ofReal (b y) < ⊤ :=
    ae_of_all _ fun y => ENNReal.ofReal_lt_top
  have hint_z : Integrable (greenFunction O z) ν₂ := by
    rw [hν₂_def, integrable_withDensity_iff hbmeas hblt]
    refine (hint_b z).congr (ae_of_all _ fun y => ?_)
    simp [ENNReal.toReal_ofReal (hb_nonneg y)]
  -- Step 6: the Green potentials as integrals against `a dx` and `b dx`
  have hpot₁ : ∀ x, greenPotential O ν₁ x = ∫ y, greenFunction O x y * a y := by
    intro x
    unfold greenPotential
    rw [hν₁_def, integral_withDensity_eq_integral_toReal_smul₀ hameas.aemeasurable halt]
    congr 1
    funext y
    rw [ENNReal.toReal_ofReal (ha_nonneg y), smul_eq_mul, mul_comm]
  have hpot₂ : ∀ x, greenPotential O ν₂ x = ∫ y, greenFunction O x y * b y := by
    intro x
    unfold greenPotential
    rw [hν₂_def, integral_withDensity_eq_integral_toReal_smul₀ hbmeas.aemeasurable hblt]
    congr 1
    funext y
    rw [ENNReal.toReal_ofReal (hb_nonneg y), smul_eq_mul, mul_comm]
  -- Step 7: the signed potential is the integral against `-ΔF dx`, which is `F` at every pole
  have hdiff : ∀ x, greenPotential O ν₁ x - greenPotential O ν₂ x
      = -∫ y, greenFunction O x y * Laplacian.laplacian F y := by
    intro x
    rw [hpot₁ x, hpot₂ x, ← integral_sub (hint_a x) (hint_b x), ← integral_neg]
    congr 1
    funext y
    have key := max_neg_sub_max_eq_neg (Laplacian.laplacian F y)
    simp only [ha_def, hb_def]
    linear_combination greenFunction O x y * key
  have hrep : F = (0 : ℂ → ℝ) + greenPotential O ν₁ - greenPotential O ν₂ := by
    funext x
    simp only [Pi.sub_apply, zero_add]
    rw [hdiff x, integral_greenFunction_mul_laplacian_eq hOo hOb hF hFc hFO x, neg_neg]
  exact ⟨O, closedBall (0 : ℂ) R₀, ν₁, ν₂, 0, hOo, hOb, hclO, isCompact_closedBall _ _, hKO,
    hν₁_fin, hν₂_fin, hν₁K, hν₂K, hν₁S, InnerProductSpace.harmonicOnNhd_const 0, hν₂z, hint_z, hrep⟩

end HarmonicBalls
