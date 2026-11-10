import HarmonicBalls.Defs.Notation

/-!
# Step 8 of the corrected proof of `lemma:mu_h-pinch-bad`: countable disk cover (fp-S11i, owner n3)

Q1 answer (`notes/fp-gaps/CHATGPT-n3-Q1-eq34.md`, Step 8): the identification of decoded and physical certificates holds for
`μ`-almost every centre, simultaneously for all centres and scales, on the whole-object identification event. A countable disk
cover of `B₁(0) \ {0}` then gives the unit-ball statement (N), and nonatomicity of the measure removes the origin.

This file proves the generic measure-theoretic part. Rational disks `B(a + b i, r)` with `a, b, r ∈ ℚ`, admissible when they lie in
`B₁(0)` and avoid `0`, cover `B₁(0) \ {0}`. A property `p ω z` that holds `μ ω`-a.e. on every admissible rational disk, almost surely,
holds `μ ω`-a.e. on `B₁(0)`, provided `μ ω {0} = 0` almost surely.
-/

namespace HarmonicBalls.FirstPassS11iStep8

open MeasureTheory Metric Set Filter

/-- The centre `a + b i` of the rational disk with index `t = (a, b, r)`. -/
def ratCentre (t : ℚ × ℚ × ℚ) : ℂ := ⟨(t.1 : ℝ), (t.2.1 : ℝ)⟩

/-- A rational disk `B(a + b i, r)` is admissible when `0 < r`, it lies in the unit ball `B₁(0)` and it does not contain `0`. -/
def AdmissibleRatDisk (t : ℚ × ℚ × ℚ) : Prop :=
  0 < (t.2.2 : ℝ) ∧ ball (ratCentre t) (t.2.2 : ℝ) ⊆ ball (0 : ℂ) 1 ∧ (0 : ℂ) ∉ ball (ratCentre t) (t.2.2 : ℝ)

/-- **Covering lemma.** Every point `z` of `B₁(0) \ {0}` lies in an admissible rational disk. -/
lemma exists_admissibleRatDisk {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ∈ ball (0 : ℂ) 1) :
    ∃ t : ℚ × ℚ × ℚ, AdmissibleRatDisk t ∧ z ∈ ball (ratCentre t) (t.2.2 : ℝ) := by
  rw [mem_ball_zero_iff] at hz1
  have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hε0 : 0 < min ‖z‖ (1 - ‖z‖) := lt_min hpos (by linarith)
  have hεz : min ‖z‖ (1 - ‖z‖) ≤ ‖z‖ := min_le_left _ _
  have hε1 : min ‖z‖ (1 - ‖z‖) ≤ 1 - ‖z‖ := min_le_right _ _
  obtain ⟨r, hr0, hr1⟩ := exists_rat_btwn (div_pos hε0 (by norm_num : (0 : ℝ) < 3))
  obtain ⟨a, ha0, ha1⟩ := exists_rat_btwn (show z.re - (r : ℝ) / 2 < z.re + (r : ℝ) / 2 by linarith)
  obtain ⟨b, hb0, hb1⟩ := exists_rat_btwn (show z.im - (r : ℝ) / 2 < z.im + (r : ℝ) / 2 by linarith)
  have hc : ‖ratCentre (a, b, r) - z‖ < (r : ℝ) := by
    have h1 := Complex.norm_le_abs_re_add_abs_im (ratCentre (a, b, r) - z)
    have e1 : |(a : ℝ) - z.re| < (r : ℝ) / 2 := abs_lt.2 ⟨by linarith, by linarith⟩
    have e2 : |(b : ℝ) - z.im| < (r : ℝ) / 2 := abs_lt.2 ⟨by linarith, by linarith⟩
    have hre : (ratCentre (a, b, r) - z).re = (a : ℝ) - z.re := rfl
    have him : (ratCentre (a, b, r) - z).im = (b : ℝ) - z.im := rfl
    rw [hre, him] at h1
    linarith
  refine ⟨(a, b, r), ⟨hr0, ?_, ?_⟩, ?_⟩
  · intro w hw
    have hw' : dist w (ratCentre (a, b, r)) < (r : ℝ) := hw
    rw [dist_eq_norm] at hw'
    rw [mem_ball_zero_iff]
    have k1 := norm_add_le (w - ratCentre (a, b, r)) (ratCentre (a, b, r) - z)
    have k2 := norm_add_le (w - ratCentre (a, b, r) + (ratCentre (a, b, r) - z)) z
    have e : w - ratCentre (a, b, r) + (ratCentre (a, b, r) - z) + z = w := by ring
    rw [e] at k2
    linarith
  · intro h
    have h' : dist (0 : ℂ) (ratCentre (a, b, r)) < (r : ℝ) := h
    rw [dist_zero_left] at h'
    have k := norm_add_le (ratCentre (a, b, r)) (z - ratCentre (a, b, r))
    have e : ratCentre (a, b, r) + (z - ratCentre (a, b, r)) = z := by ring
    rw [e] at k
    have e2 : ‖z - ratCentre (a, b, r)‖ = ‖ratCentre (a, b, r) - z‖ := norm_sub_rev _ _
    linarith
  · show dist z (ratCentre (a, b, r)) < (r : ℝ)
    rw [dist_eq_norm, norm_sub_rev]
    exact hc

/-- **Step 8, measure-theoretic core.** Let `p ω z` be a property which holds `μ ω`-almost everywhere on each admissible rational disk,
almost surely. If `μ ω {0} = 0` almost surely, then almost surely `p ω z` holds for `μ ω`-almost every `z ∈ B₁(0)`. The
hypothesis `hnon` is the nonatomicity of the LQG measure at the origin (Proposed input, Fact 2.1 I), and `hdisk` is the disk-level
identification of the decoded and physical certificates (Q1 Step 8, input (A)). -/
theorem ae_ball_of_disk_ae {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ)
    (p : Ω → ℂ → Prop)
    (hnon : ∀ᵐ ω ∂P, μ ω {0} = 0)
    (hdisk : ∀ t : ℚ × ℚ × ℚ, AdmissibleRatDisk t → ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω),
      z ∈ ball (ratCentre t) (t.2.2 : ℝ) → p ω z) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), z ∈ ball (0 : ℂ) 1 → p ω z := by
  have hall : ∀ t : ℚ × ℚ × ℚ, ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω),
      AdmissibleRatDisk t → (z ∈ ball (ratCentre t) (t.2.2 : ℝ) → p ω z) := by
    intro t
    by_cases ht : AdmissibleRatDisk t
    · exact (hdisk t ht).mono fun ω hω => hω.mono fun z hz _ => hz
    · exact ae_of_all _ fun ω => ae_of_all _ fun z hz => absurd hz ht
  have h1 : ∀ᵐ ω ∂P, ∀ t : ℚ × ℚ × ℚ, ∀ᵐ z ∂(μ ω),
      AdmissibleRatDisk t → (z ∈ ball (ratCentre t) (t.2.2 : ℝ) → p ω z) :=
    ae_all_iff.2 hall
  have h2 : ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), ∀ t : ℚ × ℚ × ℚ,
      AdmissibleRatDisk t → (z ∈ ball (ratCentre t) (t.2.2 : ℝ) → p ω z) :=
    h1.mono fun ω hω => ae_all_iff.2 hω
  filter_upwards [h2, hnon] with ω hω hn
  have hz0 : ∀ᵐ z ∂(μ ω), z ≠ 0 := by
    rw [ae_iff]
    simpa using hn
  filter_upwards [hω, hz0] with z hz hz0' hzb
  obtain ⟨t, ht, hzt⟩ := exists_admissibleRatDisk hz0' hzb
  exact hz t ht hzt

end HarmonicBalls.FirstPassS11iStep8

#print axioms HarmonicBalls.FirstPassS11iStep8.ae_ball_of_disk_ae
