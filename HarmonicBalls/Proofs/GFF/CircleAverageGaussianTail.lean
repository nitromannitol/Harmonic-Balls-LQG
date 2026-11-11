import HarmonicBalls.Proofs.Sec11.FixedSquareFrontierNull
import HarmonicBalls.Proofs.Sec2.CircleAverageTail

/-!
# Fixed circle-average Gaussian tail

A centred circle average has a Gaussian tail, including when its variance vanishes.
Credit: the import closure contains code by Leonardo Bonanno (LatticeProb).
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal

/-- For a fixed radius and centre, the circle average has a quadratic-exponential tail. -/
theorem IsWholePlaneGFF.circleAverage_gaussian_tail {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {L : ℝ} (hL : 0 < L) (z : ℂ)
    {a : ℝ} (ha : 0 < a) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ,
      P {ω | a * n < |hcirc ω L z|} ≤
        ENNReal.ofReal (C * Real.exp (-c * (n : ℝ)^2)) := by
  have hP := hh.isProbabilityMeasure
  set X : Ω → ℝ := fun ω => hcirc ω L z
  have hG : HasGaussianLaw X P := hh.hasGaussianLaw_circle hL z
  have hmean : ∫ ω, X ω ∂P = 0 := hh.integral_eq_zero (.circle L z) hL
  set v : NNReal := (Var[X; P]).toNNReal
  have hv : (v : ℝ) = Var[X; P] := Real.coe_toNNReal _ (variance_nonneg _ _)
  have hlaw : HasLaw X (gaussianReal 0 v) P :=
    ⟨hG.aemeasurable, by rw [hG.map_eq_gaussianReal, hmean]⟩
  have hint : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) P := by
    intro t
    have h := integrable_exp_mul_gaussianReal (μ := 0) (v := v) t
    rw [← hlaw.map_eq] at h
    exact (integrable_map_measure (by fun_prop) hG.aemeasurable).1 h
  set V : ℝ := (v : ℝ) + 1
  have hV : 0 < V := by dsimp [V]; positivity
  have hvV : (v : ℝ) ≤ V := by dsimp [V]; linarith
  refine ⟨a^2 / (2 * V), 2, by positivity, by norm_num, ?_⟩
  intro n
  set T : ℝ := a * n
  have hT : 0 ≤ T := by dsimp [T]; positivity
  set s : ℝ := T / V
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hbound : Real.exp (-s * T) * Real.exp (0 * s + v * s ^ 2 / 2) ≤
      Real.exp (-(T ^ 2) / (2 * V)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    calc -s * T + (0 * s + v * s ^ 2 / 2) ≤ -s * T + V * s ^ 2 / 2 := by
           nlinarith [sq_nonneg s]
      _ = -(T ^ 2) / (2 * V) := by dsimp [s]; field_simp; ring
  have hup : P.real {ω | T ≤ X ω} ≤ Real.exp (-(T ^ 2) / (2 * V)) := by
    refine (measure_ge_le_exp_mul_mgf T hs (hint s)).trans ?_
    rw [mgf_gaussianReal hlaw]; exact hbound
  have hlow : P.real {ω | X ω ≤ -T} ≤ Real.exp (-(T ^ 2) / (2 * V)) := by
    refine (measure_le_le_exp_mul_mgf (-T) (neg_nonpos.2 hs) (hint (-s))).trans ?_
    rw [mgf_gaussianReal hlaw]
    convert hbound using 3 <;> ring
  have hsub : {ω | a * n < |hcirc ω L z|} ⊆ {ω | T ≤ X ω} ∪ {ω | X ω ≤ -T} := by
    intro ω hω
    rcases le_abs'.1 (show T ≤ |X ω| from le_of_lt hω) with h | h
    · exact Or.inr h
    · exact Or.inl h
  calc P {ω | a * n < |hcirc ω L z|} ≤ P {ω | T ≤ X ω} + P {ω | X ω ≤ -T} :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ = ENNReal.ofReal (P.real {ω | T ≤ X ω}) + ENNReal.ofReal (P.real {ω | X ω ≤ -T}) := by
        rw [ofReal_measureReal, ofReal_measureReal]
    _ ≤ ENNReal.ofReal (Real.exp (-(T ^ 2) / (2 * V))) +
        ENNReal.ofReal (Real.exp (-(T ^ 2) / (2 * V))) :=
        add_le_add (ENNReal.ofReal_le_ofReal hup) (ENNReal.ofReal_le_ofReal hlow)
    _ = ENNReal.ofReal (2 * Real.exp (-(a ^ 2 / (2 * V)) * (n : ℝ)^2)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        dsimp [T]
        ring


end HarmonicBalls
