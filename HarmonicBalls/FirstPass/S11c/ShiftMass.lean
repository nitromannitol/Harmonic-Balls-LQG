import HarmonicBalls.FirstPass.Frozen.S11c
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Proposition 11.10, the mass step of the Weyl shift (fp-S11c, owner n1)

FIRST-PASS NEW (deterministic and measure-theoretic). (i) Under a Weyl shift by a function that is constant `a` on a
measurable set `S`, the mass of `S` is multiplied by `e^{γa}` (paper Fact 2.1 III, `e^{γf}·μ_h = μ_{h+f}`, restricted to
`S`; the shift is `weylShiftPair`, Frozen/S11c.lean). (ii) A strictly positive random mass is at least some `C₁ > 0` with
probability at least `1/2` (the step `P[μ_h(S₁) ≥ C₁] ≥ 1/2` of the paper's proof of `lemma:mass-diam`, line 3050).
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- The mass of `S` under the Weyl shift by a function that equals `a` on `S`. -/
lemma weylShiftPair_fst_apply_of_const {γ ξ a : ℝ} {f : ℂ → ℝ} {S : Set ℂ} (hS : MeasurableSet S)
    (hf : ∀ z ∈ S, f z = a) (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) :
    (weylShiftPair γ ξ f (μ, D)).1 S = ENNReal.ofReal (Real.exp (γ * a)) * μ S := by
  simp only [weylShiftPair]
  rw [withDensity_apply _ hS]
  have hconst : ∫⁻ z in S, ENNReal.ofReal (Real.exp (γ * f z)) ∂μ =
      ∫⁻ z in S, ENNReal.ofReal (Real.exp (γ * a)) ∂μ :=
    setLIntegral_congr_fun hS (fun z hz => by rw [hf z hz])
  rw [hconst, setLIntegral_const, mul_comm]

/-- A strictly positive random variable exceeds some `C₁ > 0` with probability at least `1/2`. -/
lemma exists_lower_of_ae_pos {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → ℝ≥0∞} (hX : Measurable X) (hpos : ∀ᵐ ω ∂P, 0 < X ω) :
    ∃ C₁ : ℝ≥0∞, 0 < C₁ ∧ C₁ ≠ ⊤ ∧ 1 / 2 ≤ P {ω | C₁ ≤ X ω} := by
  -- the events `{(k+1)⁻¹ ≤ X}` increase to `{0 < X}`, which has full measure
  set A : ℕ → Set Ω := fun k => {ω | ((k : ℝ≥0∞) + 1)⁻¹ ≤ X ω} with hA
  have hAmono : Monotone A := by
    intro k l hkl ω hω
    simp only [hA, Set.mem_ofPred_eq] at hω ⊢
    have h1 : (k : ℝ≥0∞) + 1 ≤ (l : ℝ≥0∞) + 1 := by
      gcongr
    exact le_trans (ENNReal.inv_le_inv.2 h1) hω
  have hunion : ⋃ k, A k = {ω | 0 < X ω} := by
    ext ω
    simp only [hA, mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨k, hk⟩
      exact lt_of_lt_of_le (ENNReal.inv_pos.2 (by simp)) hk
    · intro h
      obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt h.ne'
      exact ⟨n, le_trans (ENNReal.inv_le_inv.2 le_self_add) hn.le⟩
  have hmeas : MeasurableSet {ω | 0 < X ω} := measurableSet_lt measurable_const hX
  have hfull : P (⋃ k, A k) = 1 := by
    rw [hunion]
    exact (prob_compl_eq_zero_iff hmeas).1 (ae_iff.1 hpos)
  have htend := tendsto_measure_iUnion_atTop (μ := P) hAmono
  rw [hfull] at htend
  obtain ⟨k, hk⟩ := (htend.eventually
    (lt_mem_nhds (ENNReal.half_lt_self one_ne_zero ENNReal.one_ne_top))).exists
  refine ⟨((k : ℝ≥0∞) + 1)⁻¹, ENNReal.inv_pos.2 (by simp), ENNReal.inv_ne_top.2 (by simp), ?_⟩
  exact hk.le

end HarmonicBalls
