import HarmonicBalls.Steps.Sec11.WeylInternalComparison

/-! # Point removal under nonpositive Weyl shifts

Summable punctured shell bounds transfer to a nonpositive Weyl shift. The
singular-field result uses staged metric-field axioms awaiting source check.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set
open scoped ENNReal

/-- A nonpositive Weyl shift preserves a summable shell criterion for deleting
zero from an open internal-metric domain. -/
theorem IsEuclideanLengthMetric.internalMetric_sdiff_zero_eq_of_nonpositive_weyl
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) {ξ : ℝ} (hξ : 0 ≤ ξ)
    {f : ℂ → ℝ} (hf : ∀ z, f z ≤ 0) {V : Set ℂ} (hV : IsOpen V)
    (hscale : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y)
    {R q : ℝ} (hR : 0 < R) (hq : 0 < q) (hq1 : q < 1)
    (c : ℕ → ℝ≥0∞)
    (hdiam : ∀ n, ∀ x ∈ geometricShell R q n, ∀ y ∈ geometricShell R q n,
      internalMetric D (V \ {0}) x y ≤ c n)
    (hsum : (∑' n, c n) ≠ ∞) {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    internalMetric E (V \ {0}) x y = internalMetric E V x y := by
  apply hE.internalMetric_sdiff_zero_eq_of_geometric_shells V hR hq hq1 c ?_ hsum hx hy
  intro n a ha b hb
  have hnonneg (u v : ℂ) : 0 ≤ E u v := by
    have ht := hE.triangle u v u
    rw [hE.self_eq_zero, hE.symm v u] at ht
    linarith
  have hcomp := hD.internalMetric_weylScaling_le hE hnonneg
    (U := V \ {0}) (hV.sdiff isClosed_singleton) (hD.weylScaling_zero ξ) hscale
    (B := 0) (fun z _ => mul_nonpos_of_nonneg_of_nonpos hξ (hf z)) a b
  simp only [Real.exp_zero, ENNReal.ofReal_one, one_mul] at hcomp
  exact hcomp.trans (hdiam n a ha b hb)

/-- Point removal for a length metric transfers to any nonpositive Weyl
shift that is itself a length metric. -/
theorem IsEuclideanLengthMetric.internalMetric_sdiff_zero_eq_of_weyl_point_removal
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) {ξ : ℝ} (hξ : 0 ≤ ξ)
    {f : ℂ → ℝ} (hf : ∀ z, f z ≤ 0) {V : Set ℂ} (hV : IsOpen V)
    (hscale : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y)
    (hremove : ∀ a ∈ V \ {0}, ∀ b ∈ V \ {0},
      internalMetric D (V \ {0}) a b = internalMetric D V a b)
    {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    internalMetric E (V \ {0}) x y = internalMetric E V x y := by
  by_cases h0 : (0 : ℂ) ∈ V
  · have hcheap := hD.small_detours_of_internalMetric_sdiff_zero_eq hV h0 hremove
    have hnonneg (u v : ℂ) : 0 ≤ E u v := by
      have ht := hE.triangle u v u
      rw [hE.self_eq_zero, hE.symm v u] at ht
      linarith
    apply hE.internalMetric_sdiff_zero_eq_of_small_detours hx hy
    intro ε hε
    obtain ⟨r, hr, hbound⟩ := hcheap ε hε
    refine ⟨r, hr, ?_⟩
    intro a b ha hb ha0 hb0 har hbr
    have hcomp := hD.internalMetric_weylScaling_le hE hnonneg
      (U := V \ {0}) (hV.sdiff isClosed_singleton) (hD.weylScaling_zero ξ) hscale
      (B := 0) (fun z _ => mul_nonpos_of_nonneg_of_nonpos hξ (hf z)) a b
    simp only [Real.exp_zero, ENNReal.ofReal_one, one_mul] at hcomp
    exact hcomp.trans_lt (hbound a b ha hb ha0 hb0 har hbr)
  · have hs : V \ {0} = V := by
      ext z
      simp only [Set.mem_sdiff, mem_singleton_iff]
      constructor
      · exact fun hz => hz.1
      · intro hz
        exact ⟨hz, fun hz0 => h0 (hz0 ▸ hz)⟩
    rw [hs]

/-- Almost surely, point removal transfers to every admissible nonpositive
shift, on every open domain where it holds for the unshifted metric. -/
theorem ae_singularField_nonpositive_weyl_point_removal_of_point_removal
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ ξ α : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ)
    (haxioms : LQGMetricFieldAxioms P γ ξ α hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α hC D)
    (hξ : 0 ≤ ξ) :
    ∀ᵐ ω ∂P, ∀ (f : ℂ → ℝ), Continuous f → HasCompactSupport f →
      (∀ z, f z ≤ 0) → ∀ (V : Set ℂ), IsOpen V →
      (∀ a ∈ V \ {0}, ∀ b ∈ V \ {0},
        internalMetric (D ω) (V \ {0}) a b = internalMetric (D ω) V a b) →
      ∀ x y : ℂ, x ≠ 0 → y ≠ 0 →
      internalMetric (fun a b => (weylScaling (D ω) ξ f a b).toReal) (V \ {0}) x y =
        internalMetric (fun a b => (weylScaling (D ω) ξ f a b).toReal) V x y := by
  filter_upwards [ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α hC hcirc D
      haxioms hgff hγ hγ₂ hα hD,
    ae_singularField_weylBump_identities_of_metricFieldAxioms P γ ξ α hC hcirc D
      haxioms hgff hγ hγ₂ hα hD hξ,
    ae_singularField_negative_weylScaling_finite P γ ξ α hC hcirc D
      haxioms hgff hγ hγ₂ hα hD hξ] with ω hm hi hfinite
  intro f hf hc hn V hV hremove x y hx hy
  exact hm.internalMetric_sdiff_zero_eq_of_weyl_point_removal (hi f hf hc hn).1 hξ hn hV
    (fun u v => (hfinite f hn u v).2) hremove hx hy

/-- The shell criterion transfers simultaneously to every continuous,
compactly supported nonpositive shift of a singular-field metric. -/
theorem ae_singularField_nonpositive_weyl_point_removal
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ ξ α : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ)
    (haxioms : LQGMetricFieldAxioms P γ ξ α hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α hC D)
    (hξ : 0 ≤ ξ) :
    ∀ᵐ ω ∂P, ∀ (f : ℂ → ℝ), Continuous f → HasCompactSupport f →
      (∀ z, f z ≤ 0) → ∀ (V : Set ℂ), IsOpen V → ∀ (R q : ℝ),
      0 < R → 0 < q → q < 1 → ∀ c : ℕ → ℝ≥0∞,
      (∀ n, ∀ x ∈ geometricShell R q n, ∀ y ∈ geometricShell R q n,
        internalMetric (D ω) (V \ {0}) x y ≤ c n) →
      (∑' n, c n) ≠ ∞ → ∀ x y : ℂ, x ≠ 0 → y ≠ 0 →
      internalMetric (fun a b => (weylScaling (D ω) ξ f a b).toReal) (V \ {0}) x y =
        internalMetric (fun a b => (weylScaling (D ω) ξ f a b).toReal) V x y := by
  filter_upwards [ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α hC hcirc D
      haxioms hgff hγ hγ₂ hα hD,
    ae_singularField_weylBump_identities_of_metricFieldAxioms P γ ξ α hC hcirc D
      haxioms hgff hγ hγ₂ hα hD hξ,
    ae_singularField_negative_weylScaling_finite P γ ξ α hC hcirc D
      haxioms hgff hγ hγ₂ hα hD hξ] with ω hm hi hfinite
  intro f hf hc hn V hV R q hR hq hq1 c hdiam hsum x y hx hy
  exact hm.internalMetric_sdiff_zero_eq_of_nonpositive_weyl (hi f hf hc hn).1 hξ hn hV
    (fun u v => (hfinite f hn u v).2) hR hq hq1 c hdiam hsum hx hy


end HarmonicBalls
