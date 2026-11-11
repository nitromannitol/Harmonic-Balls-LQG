import HarmonicBalls.Proofs.Sec11.SingularCutoffWeylComparison
import HarmonicBalls.Steps.Sec11.InternalMetricExhaustion

/-! # Exhaustion of singular Weyl metrics

A countable open exhaustion permits the cutoff radius to decrease with the
exhaustion. Removing the origin from the limiting domain remains a separate
question.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set
open scoped ENNReal

/-- The internal Weyl metric on an increasing union is the infimum of the
corresponding continuously shifted cutoff metrics, provided each exhaustion
set is separated from the singularity. -/
theorem IsWholePlaneGFF.ae_internal_singularMetric_weylShift_eq_iInf_cutoff
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, ENNReal.ofReal (D ω u v) =
      weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (g : ℂ → ℝ) (hg : Continuous g) (hc : HasCompactSupport g)
    (hu : ∀ z, g z ≤ 0) (hξ : 0 ≤ ξ)
    (hshiftmetric : ∀ᵐ ω ∂P,
      IsEuclideanLengthMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal))
    (r : ℕ → ℝ) (hr : ∀ m, 0 < r m) (U : ℕ → ℕ → Set ℂ)
    (hU : ∀ n m, IsOpen (U n m)) (hmono : ∀ n, Monotone (U n))
    (haway : ∀ n m z, z ∈ U n m → r m ≤ ‖z‖) :
    ∀ᵐ ω ∂P, ∀ n x y,
      internalMetric (fun a b => (weylScaling (D ω) ξ g a b).toReal)
          (⋃ m, U n m) x y =
      ⨅ m, internalMetric (fun a b =>
        (weylScaling (𝔇 (hC ω)) ξ
          (fun z => g z + -α * Real.log (max ‖z‖ (r m))) a b).toReal) (U n m) x y := by
  have heach : ∀ m, ∀ᵐ ω ∂P, ∀ n x y,
      internalMetric (fun a b => (weylScaling (D ω) ξ g a b).toReal) (U n m) x y =
        internalMetric (fun a b => (weylScaling (𝔇 (hC ω)) ξ
          (fun z => g z + -α * Real.log (max ‖z‖ (r m))) a b).toReal) (U n m) x y := by
    intro m
    exact h.ae_internal_singularMetric_weylShift_eq_cutoff 𝔇 h𝔇 hD hmetric g hg hc hu hξ
      hshiftmetric (hr m) (fun n => U n m) (fun n => hU n m) (fun n z hz => haway n m z hz)
  filter_upwards [(ae_all_iff).2 heach] with ω hω n x y
  rw [internalMetric_iUnion_of_monotone_isOpen _ (U n) (hU n) (hmono n)]
  exact iInf_congr fun m => hω m n x y

/-- The complements of shrinking closed balls exhaust every punctured set. -/
theorem punctured_open_exhaustion (U : Set ℂ) :
    (⋃ m : ℕ, U ∩ {z : ℂ | 1 / (m + 1 : ℝ) < ‖z‖}) = U \ {0} := by
  ext z
  simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq, Set.mem_sdiff, mem_singleton_iff]
  constructor
  · rintro ⟨m, hzU, hm⟩
    refine ⟨hzU, ?_⟩
    intro hz
    subst z
    have hpos : 0 < (1 / (m + 1 : ℝ)) := by positivity
    simp only [norm_zero] at hm
    exact (not_lt_of_ge hpos.le) hm
  · rintro ⟨hzU, hz0⟩
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (norm_pos_iff.mpr hz0)
    exact ⟨m, hzU, hm⟩

/-- The standard punctured exhaustion is increasing. -/
theorem punctured_open_exhaustion_mono (U : Set ℂ) :
    Monotone (fun m : ℕ => U ∩ {z : ℂ | 1 / (m + 1 : ℝ) < ‖z‖}) := by
  intro m n hmn z hz
  refine ⟨hz.1, ?_⟩
  change 1 / (n + 1 : ℝ) < ‖z‖
  have hle : (1 / (n + 1 : ℝ)) ≤ 1 / (m + 1 : ℝ) := by
    gcongr
  exact lt_of_le_of_lt hle hz.2

/-- On any punctured open set, the singular Weyl internal metric is the
infimum of the internal metrics of smooth cutoff backgrounds. -/
theorem IsWholePlaneGFF.ae_internal_singularMetric_weylShift_punctured_eq_iInf
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, ENNReal.ofReal (D ω u v) =
      weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (g : ℂ → ℝ) (hg : Continuous g) (hc : HasCompactSupport g)
    (hu : ∀ z, g z ≤ 0) (hξ : 0 ≤ ξ)
    (hshiftmetric : ∀ᵐ ω ∂P,
      IsEuclideanLengthMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal))
    (U : ℕ → Set ℂ) (hU : ∀ n, IsOpen (U n)) :
    ∀ᵐ ω ∂P, ∀ n x y,
      internalMetric (fun a b => (weylScaling (D ω) ξ g a b).toReal) (U n \ {0}) x y =
      ⨅ m : ℕ, internalMetric (fun a b => (weylScaling (𝔇 (hC ω)) ξ
        (fun z => g z + -α * Real.log (max ‖z‖ (1 / (m + 1 : ℝ)))) a b).toReal)
          (U n ∩ {z : ℂ | 1 / (m + 1 : ℝ) < ‖z‖}) x y := by
  let V : ℕ → ℕ → Set ℂ := fun n m => U n ∩ {z | 1 / (m + 1 : ℝ) < ‖z‖}
  have hr (m : ℕ) : 0 < (1 / (m + 1 : ℝ)) := by positivity
  have hopen (n m : ℕ) : IsOpen (V n m) :=
    (hU n).inter (isOpen_lt continuous_const continuous_norm)
  have haway (n m : ℕ) (z : ℂ) (hz : z ∈ V n m) : 1 / (m + 1 : ℝ) ≤ ‖z‖ :=
    le_of_lt hz.2
  have hres := h.ae_internal_singularMetric_weylShift_eq_iInf_cutoff 𝔇 h𝔇 hD hmetric
    g hg hc hu hξ hshiftmetric (fun m => 1 / (m + 1 : ℝ)) hr V hopen
    (fun n => punctured_open_exhaustion_mono (U n)) haway
  filter_upwards [hres] with ω hω n x y
  simpa only [V, punctured_open_exhaustion] using hω n x y




end HarmonicBalls
