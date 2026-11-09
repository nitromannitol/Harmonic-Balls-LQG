import HarmonicBalls.FirstPass.S11c.IdentifyBad11_7
import HarmonicBalls.FirstPass.S11c.WindowTransfer11_7

/-!
# Lemma 11.7, fixed-root null section from the origin window (B2 sec 5.1 glue, deterministic given its inputs)

For a fixed root `z ∈ U` and the decoded observation `x` of the rooted field, suppose almost surely:
* the decoder identity `K (x ω) = c ω • (μ_z ω).restrict D` with `c ω ∈ (0, ∞)` (decoder clause, B2 Claim 3.1);
* the rooted measure is a translate of the origin measure, `μ_z ω = c' ω • (ν ω).map (· + z)` (CoordRooted11_7.lean);
* the origin window bound of `origin_window_visits` (Origin11_7.lean:192) for `ν ω`, at the shifted scales `N₀ + n`.
Then almost surely `(z, x ω)` is not in the local bad set `localBadSet K Q M (p/8) U nD` (BadSetMeasurable11_7.lean:43),
the constant `δ = p/8` of B2 sec 1. This is the deterministic core of the fixed-root null (B2 (5.1)); the decoder and the
origin window are inputs, so no decision on the decoder's α₀-dependence is used here.
-/

open MeasureTheory Filter Set
open scoped ENNReal

namespace HarmonicBalls.S11c

open Classical in
theorem ae_not_mem_localBadSet_of_origin {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] {P : Measure Ω}
    {K : ProbabilityTheory.Kernel X ℂ} {Q : Set ℂ} {M p : ℝ} (hp : 0 ≤ p)
    {D U : Set ℂ} (hDm : MeasurableSet D) {nD : ℕ} {z : ℂ}
    (hD : ∀ n : ℕ, nD ≤ n → Metric.closedBall z (6 * (2 : ℝ)⁻¹ ^ n) ⊆ D) (hzU : z ∈ U)
    {x : Ω → X} {μz ν : Ω → Measure ℂ} {c' : Ω → ℝ≥0∞}
    (hK : ∀ᵐ ω ∂P, ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧ K (x ω) = c • (μz ω).restrict D)
    (hμ : ∀ᵐ ω ∂P, μz ω = c' ω • (ν ω).map (fun w => w + z))
    (hc' : ∀ᵐ ω ∂P, c' ω ≠ 0 ∧ c' ω ≠ ⊤)
    (N0 : ℕ)
    (hOrig : ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop,
      p / 4 * (N : ℝ) ≤ (((Finset.Icc (N + 1) (2 * N)).filter
        (fun n : ℕ => coneMassEvent (ν ω) Q M (dyadicScale (N0 + n)) 0)).card : ℝ)) :
    ∀ᵐ ω ∂P, (z, x ω) ∉ localBadSet K Q M (p / 8) U nD := by
  classical
  filter_upwards [hK, hμ, hc', hOrig] with ω hKω hμω hc'ω hOω
  obtain ⟨c, hc0, hcT, hKc⟩ := hKω
  intro hmem
  rw [mem_localBadSet_iff hDm hc0.ne' hcT.ne hKc hD hzU] at hmem
  apply hmem
  -- the indicator of the origin cone event at the shifted scales
  set g : ℕ → ℝ := fun m => if coneMassEvent (ν ω) Q M ((2 : ℝ)⁻¹ ^ m) 0 then 1 else 0 with hg_def
  have hg : ∀ m, 0 ≤ g m := fun m => by
    simp only [hg_def]
    split_ifs <;> norm_num
  have hshift : ∀ᶠ N' : ℕ in atTop, p / 4 * (N' : ℝ) ≤ ∑ n ∈ Finset.Icc (N' + 1) (2 * N'), g (N0 + n) := by
    filter_upwards [hOω] with N' hN'
    refine le_trans hN' (le_of_eq ?_)
    simp [hg_def, dyadicScale, Finset.sum_boole]
  have hwin := window_shift_ge g hg N0 hp hshift
  have hsum : ∀ N : ℕ, ∑ m ∈ Finset.Icc (N + 1) (2 * N), g m = globalWindowSum Q M 0 (ν ω) N := by
    intro N
    unfold globalWindowSum
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [hg_def, Set.indicator_apply, Set.mem_ofPred_eq]
  have hbound : ∀ᶠ N : ℕ in atTop, p / 8 * (N : ℝ) ≤ globalWindowSum Q M 0 (ν ω) N := by
    filter_upwards [hwin] with N hN
    rwa [hsum N] at hN
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp hbound
  refine ⟨N1, fun N hN => ?_⟩
  rw [hμω, globalWindowSum_smul_map_add_right Q M z (ν ω) hc'ω.1 hc'ω.2 N]
  exact hN1 N hN

end HarmonicBalls.S11c
