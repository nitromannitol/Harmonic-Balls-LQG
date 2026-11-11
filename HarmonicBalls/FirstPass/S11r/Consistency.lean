import HarmonicBalls.Defs.LQGMetric
import HarmonicBalls.Steps.Sec11.MetricConstantScaling
import HarmonicBalls.FirstPass.S11r.InternalSubdomain

/-!
# Pointwise consistency of the normalised local metrics, the identity (22)

For a fixed field with metric `I` (on `D`, and on the smaller disk `V ⊆ D`), if the normalised local metric decoders
satisfy `ofReal (M x y) = e^a · D_I(x,y;D)` on `D` and `ofReal (MV x y) = e^b · D_I(x,y;V)` on `V` (the local decoder
identity of `LocalLQGMetricNormalizedMeasurableFrozen`, with the constants `e^a = e^{-ξ⟨g,ρ_D⟩}`, `e^b = e^{-ξ⟨g,ρ_V⟩}`),
then the internal metric of `M` on `V` is `e^{a-b}` times `MV`, which is the identity (22),
at the level of one field and one pair of points.

The subdomain identity hII (the internal metric on `V` of the internal metric on `D` equals the internal metric on `V`)
is PROVED (`internalMetric_internalMetric_toReal_of_finite`, InternalSubdomain.lean). No hypothesis of that form remains here; the Euclidean length property of `I` is used instead.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal NNReal

/-- `curveLength` only sees `ENNReal.ofReal` of the metric, at points of the curve. -/
theorem curveLength_congr_ofReal_on {D E : ℂ → ℂ → ℝ} {U : Set ℂ}
    (h : ∀ x ∈ U, ∀ y ∈ U, ENNReal.ofReal (D x y) = ENNReal.ofReal (E x y)) (p : ℝ → ℂ)
    (hp : ∀ t ∈ Icc (0 : ℝ) 1, p t ∈ U) :
    curveLength D p 0 1 = curveLength E p 0 1 := by
  unfold curveLength
  refine iSup_congr fun q => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := q.2.2.2 i
  have h2 := q.2.2.2 (i + 1)
  exact h _ (hp _ h2) _ (hp _ h1)

/-- The internal metric on `U` depends only on `ofReal` of the metric on `U × U`. -/
theorem internalMetric_congr_ofReal_on {D E : ℂ → ℂ → ℝ} {U : Set ℂ}
    (h : ∀ x ∈ U, ∀ y ∈ U, ENNReal.ofReal (D x y) = ENNReal.ofReal (E x y)) (x y : ℂ) :
    internalMetric D U x y = internalMetric E U x y := by
  unfold internalMetric
  refine iInf_congr fun P => iInf_congr fun hP => ?_
  unfold pathLength
  refine curveLength_congr_ofReal_on h _ fun t ht => ?_
  have : P.extend t = P (Set.projIcc 0 1 zero_le_one t) := by
    simp [Path.extend, IccExtend]
  rw [this]
  exact hP _

/-- **Pointwise (22).** For one field with metric `I` (a Euclidean length metric): if `ofReal M = e^a · internalMetric I D`
on `D × D` and `ofReal MV = e^b · internalMetric I V` on `V × V`, with `internalMetric I D` finite on `D × D`, then for
`x, y ∈ V` the internal metric of `M` on `V` is `e^{a-b}` times `MV`. -/
theorem internalMetric_normalised_consistency {D V : Set ℂ} (hVD : V ⊆ D)
    {I M MV : ℂ → ℂ → ℝ} {a b : ℝ} (hI : IsEuclideanLengthMetric I)
    (hfin : ∀ x ∈ D, ∀ y ∈ D, internalMetric I D x y ≠ ⊤)
    (hM : ∀ x ∈ D, ∀ y ∈ D, ENNReal.ofReal (M x y) = ENNReal.ofReal (Real.exp a) * internalMetric I D x y)
    (hMV : ∀ x ∈ V, ∀ y ∈ V, ENNReal.ofReal (MV x y) = ENNReal.ofReal (Real.exp b) * internalMetric I V x y)
    {x y : ℂ} (hx : x ∈ V) (hy : y ∈ V) :
    internalMetric M V x y = ENNReal.ofReal (Real.exp (a - b)) * ENNReal.ofReal (MV x y) := by
  -- Step 1: on `V × V`, `M` and `e^a · (internal metric of I on D)` have the same `ofReal`.
  set T : ℂ → ℂ → ℝ := fun u v => (internalMetric I D u v).toReal with hT
  have hTfin : ∀ u ∈ V, ∀ v ∈ V, ENNReal.ofReal (Real.exp a * T u v) =
      ENNReal.ofReal (Real.exp a) * internalMetric I D u v := by
    intro u hu v hv
    have hd := hfin u (hVD hu) v (hVD hv)
    simp only [hT]
    rw [ENNReal.ofReal_mul (Real.exp_pos a).le, ENNReal.ofReal_toReal hd]
  have hstep1 : internalMetric M V x y = internalMetric (fun u v => Real.exp a * T u v) V x y := by
    refine internalMetric_congr_ofReal_on (fun u hu v hv => ?_) x y
    rw [hM u (hVD hu) v (hVD hv), ← hTfin u hu v hv]
  -- Step 2: scale, then the subdomain identity.
  have hstep2 : internalMetric (fun u v => Real.exp a * T u v) V x y =
      ENNReal.ofReal (Real.exp a) * internalMetric I V x y := by
    rw [internalMetric_const_mul T (Real.exp_pos a) V x y]
    rw [show internalMetric T V x y = internalMetric I V x y from
      internalMetric_internalMetric_toReal_of_finite hI hVD hfin x y]
  -- Step 3: the constant `e^b` of `MV` cancels against `e^{-b}`.
  have hstep3 : internalMetric I V x y = ENNReal.ofReal (Real.exp (-b)) * ENNReal.ofReal (MV x y) := by
    rw [hMV x hx y hy, ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos (-b)).le,
      ← Real.exp_add, neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one, one_mul]
  rw [hstep1, hstep2, hstep3, ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos a).le,
    ← Real.exp_add, sub_eq_add_neg]

end HarmonicBalls
