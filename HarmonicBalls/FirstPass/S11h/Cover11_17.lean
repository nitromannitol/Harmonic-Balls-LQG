import HarmonicBalls.FirstPass.S11h.SetDistPos
import HarmonicBalls.FirstPass.S11h.OuterDiamFinite

/-!
# Lemma 11.17, Step 17.3 (truncation sets and their almost-sure cover)

Step 17.3: the sets
`G n = {a₂ ≥ 1/(n+1), d₂ ≤ n+1}`, with `a₂ = D(∂B_{2δ}, ∂B_{3δ})` (`setDist`, the distance in `pinchThirdEvent`,
Draft/Section11.lean:107) and `d₂ = diam^δ(B_{3δ}(W) \ V)` (`internalDiam`, Draft/Section11.lean:89). Almost surely they
cover the probability space (`a₂ > 0` by `setDist_sphere_pos_of_isEuclideanLengthMetric`, `d₂ < ∞` by
`ae_internalDiam_third_lt_top`), and on `G n` the bump strength `k_n = 1/(2(n+1)²)` makes the strict inequality of
`pinchEvents_of_bumpShift` hold. Real arithmetic and countable covering only; no external input.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric
open scoped ENNReal

/-- The truncation set `G n` of Step 17.3: `a₂ ≥ 1/(n+1)` and `d₂ ≤ n+1`, where `a₂ = D(∂B_{2δ}, ∂B_{3δ})` and
`d₂ = diam^δ(B_{3δ}(W) \ V)`. -/
def pinchSelectGood (D : ℂ → ℂ → ℝ) (V W : Set ℂ) (δ : ℝ) (n : ℕ) : Prop :=
  1 / ((n : ℝ) + 1) ≤ setDist D (sphere (0 : ℂ) (2 * δ)) (sphere (0 : ℂ) (3 * δ)) ∧
    internalDiam D δ (thickening (3 * δ) W \ V) ≤ ENNReal.ofReal ((n : ℝ) + 1)

/-- The bump strength `k_n = 1/(2(n+1)²)` of Step 17.3. -/
noncomputable def pinchSelectK (n : ℕ) : ℝ := 1 / (2 * ((n : ℝ) + 1) ^ 2)

theorem pinchSelectK_pos (n : ℕ) : 0 < pinchSelectK n := by
  unfold pinchSelectK
  positivity

theorem pinchSelectK_le_one (n : ℕ) : pinchSelectK n ≤ 1 := by
  unfold pinchSelectK
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [div_le_one (by positivity)]
  nlinarith

/-- On `G n`, the bump strength `k_n` satisfies the strict inequality of `pinchEvents_of_bumpShift`:
`k_n · d₂ ≤ 1/(2(n+1)) < 1/(n+1) ≤ a₂`. -/
theorem pinchSelectGood_strict {D : ℂ → ℂ → ℝ} {V W : Set ℂ} {δ : ℝ} {n : ℕ}
    (h : pinchSelectGood D V W δ n) :
    ENNReal.ofReal (pinchSelectK n) * internalDiam D δ (thickening (3 * δ) W \ V) <
      ENNReal.ofReal (setDist D (sphere (0 : ℂ) (2 * δ)) (sphere (0 : ℂ) (3 * δ))) := by
  obtain ⟨h1, h2⟩ := h
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hmul : pinchSelectK n * ((n : ℝ) + 1) = 1 / (2 * ((n : ℝ) + 1)) := by
    unfold pinchSelectK
    field_simp
  have hkey : pinchSelectK n * ((n : ℝ) + 1) < 1 / ((n : ℝ) + 1) := by
    rw [hmul]
    exact one_div_lt_one_div_of_lt hn (by linarith)
  calc ENNReal.ofReal (pinchSelectK n) * internalDiam D δ (thickening (3 * δ) W \ V)
      ≤ ENNReal.ofReal (pinchSelectK n) * ENNReal.ofReal ((n : ℝ) + 1) := mul_le_mul_of_nonneg_left h2 zero_le
    _ = ENNReal.ofReal (pinchSelectK n * ((n : ℝ) + 1)) :=
        (ENNReal.ofReal_mul (pinchSelectK_pos n).le).symm
    _ < ENNReal.ofReal (1 / ((n : ℝ) + 1)) := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hkey
    _ ≤ ENNReal.ofReal (setDist D (sphere (0 : ℂ) (2 * δ)) (sphere (0 : ℂ) (3 * δ))) :=
        ENNReal.ofReal_le_ofReal h1

/-- A real `a > 0` and an extended real `d < ∞` admit a common index `n` of the truncation sets. -/
theorem exists_nat_pinchSelect (a : ℝ) (d : ℝ≥0∞) (ha : 0 < a) (hd : d < ⊤) :
    ∃ n : ℕ, 1 / ((n : ℝ) + 1) ≤ a ∧ d ≤ ENNReal.ofReal ((n : ℝ) + 1) := by
  obtain ⟨n₁, hn₁⟩ := exists_nat_one_div_lt ha
  obtain ⟨n₂, hn₂⟩ := exists_nat_ge d.toReal
  refine ⟨max n₁ n₂, ?_, ?_⟩
  · have h1 : (n₁ : ℝ) ≤ ((max n₁ n₂ : ℕ) : ℝ) := by exact_mod_cast le_max_left _ _
    have h2 : 1 / (((max n₁ n₂ : ℕ) : ℝ) + 1) ≤ 1 / ((n₁ : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  · have h2 : (n₂ : ℝ) ≤ ((max n₁ n₂ : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
    refine le_trans (le_of_eq (ENNReal.ofReal_toReal hd.ne).symm) (ENNReal.ofReal_le_ofReal ?_)
    linarith

/-- Almost surely, some truncation set `G n` contains `ω`: the distance `a₂` is positive and the internal diameter
`d₂` is finite for every length metric `D ω`. -/
theorem ae_exists_pinchSelectGood {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {D : Ω → ℂ → ℂ → ℝ}
    (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω)) {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) :
    ∀ᵐ ω ∂P, ∃ n : ℕ, pinchSelectGood (D ω) V W δ n := by
  have hδ : 0 < δ := hgeo.delta_pos
  filter_upwards [hD, ae_internalDiam_third_lt_top hD hgeo] with ω hω hfin
  have ha : 0 < setDist (D ω) (sphere (0 : ℂ) (2 * δ)) (sphere (0 : ℂ) (3 * δ)) :=
    setDist_sphere_pos_of_isEuclideanLengthMetric hω (by linarith) (by linarith)
  obtain ⟨n, h1, h2⟩ := exists_nat_pinchSelect _ _ ha hfin
  exact ⟨n, h1, h2⟩

end HarmonicBalls

