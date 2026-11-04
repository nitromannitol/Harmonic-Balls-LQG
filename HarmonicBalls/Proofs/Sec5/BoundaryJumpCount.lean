import HarmonicBalls.Proofs.Sec5.ClusterJumpCount
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! # One-dimensional measure of boundary jumps -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Section6
open scoped BigOperators ENNReal MeasureTheory

/-- The one-dimensional Hausdorff measure of the unit circle is at most its
circumference. -/
theorem hausdorffMeasure_one_unit_sphere_le :
    μH[1] (sphere (0 : ℂ) 1) ≤ ENNReal.ofReal (2 * Real.pi) := by
  have hparam : circleMap 0 1 '' Ioc (-Real.pi) Real.pi = sphere (0 : ℂ) 1 := by
    have heq : circleMap 0 1 = (fun θ : ℝ => Complex.exp (θ * Complex.I)) := by
      funext θ
      simp [circleMap]
    rw [heq]
    exact Complex.image_exp_Ioc_eq_sphere
  have hlip : LipschitzWith 1 (circleMap 0 1) := by
    simpa using lipschitzWith_circleMap 0 1
  rw [← hparam]
  calc
    μH[1] (circleMap 0 1 '' Ioc (-Real.pi) Real.pi) ≤
        (1 : ℝ≥0∞) ^ (1 : ℝ) * μH[1] (Ioc (-Real.pi) Real.pi) :=
      hlip.hausdorffMeasure_image_le (by norm_num) _
    _ = ENNReal.ofReal (2 * Real.pi) := by
      rw [MeasureTheory.hausdorffMeasure_real, Real.volume_Ioc]
      simp only [ENNReal.one_rpow, one_mul]
      congr 1
      ring

/-- For a monotone family of closed cluster closures, finitely many distinct
boundary jumps have total one-dimensional measure at most the circumference. -/
theorem sum_measure_boundary_future_jumps_le
    (F : ℝ → Set ℂ) (T : ℝ) (S : Finset ℝ)
    (hS : ∀ t ∈ S, 0 < t ∧ t < T)
    (hclosed : ∀ t, IsClosed (F t))
    (hmono : ∀ a b, 0 < a → a ≤ b → F a ⊆ F b) :
    (∑ t ∈ S, μH[1] (((⋂ n : ℕ, F (t + dyadicScale n)) ∩ sphere 0 1) \ F t)) ≤
      ENNReal.ofReal (2 * Real.pi) := by
  let G : ℝ → Set ℂ := fun t => F t ∩ sphere 0 1
  have hsum := sum_measure_futureIncrementSet_le μH[1] G T S hS
    (fun a b ha hab => inter_subset_inter_left _ (hmono a b ha hab))
    (fun t _ => ((hclosed t).inter isClosed_sphere).measurableSet)
  have heq (t : ℝ) : futureIncrementSet G t =
      ((⋂ n : ℕ, F (t + dyadicScale n)) ∩ sphere 0 1) \ F t := by
    ext x
    simp only [futureIncrementSet, G, Set.mem_sdiff, Set.mem_iInter, Set.mem_inter_iff]
    constructor
    · rintro ⟨h, hn⟩
      refine ⟨⟨fun n => (h n).1, (h 0).2⟩, ?_⟩
      intro hxt
      exact hn ⟨hxt, (h 0).2⟩
    · rintro ⟨⟨h, hs⟩, hn⟩
      exact ⟨fun n => ⟨h n, hs⟩, fun hxt => hn hxt.1⟩
  simp_rw [heq] at hsum
  exact hsum.trans ((measure_mono inter_subset_right).trans hausdorffMeasure_one_unit_sphere_le)

/-- Before any time horizon, the number of boundary jumps with length at
least `ε` is bounded by the circumference divided by `ε`. -/
theorem encard_large_boundary_future_jumps_le
    (F : ℝ → Set ℂ) (T ε : ℝ) (hε : 0 < ε)
    (hclosed : ∀ t, IsClosed (F t))
    (hmono : ∀ a b, 0 < a → a ≤ b → F a ⊆ F b) :
    {t : ℝ | 0 < t ∧ t < T ∧ ENNReal.ofReal ε ≤
      μH[1] (((⋂ n : ℕ, F (t + dyadicScale n)) ∩ sphere 0 1) \ F t)}.encard ≤
      ⌈2 * Real.pi / ε⌉₊ := by
  let A : Set ℝ := {t : ℝ | 0 < t ∧ t < T ∧ ENNReal.ofReal ε ≤
    μH[1] (((⋂ n : ℕ, F (t + dyadicScale n)) ∩ sphere 0 1) \ F t)}
  change A.encard ≤ ⌈2 * Real.pi / ε⌉₊
  classical
  have hcard : ∀ S : Finset ℝ, (↑S : Set ℝ) ⊆ A → S.card ≤ ⌈2 * Real.pi / ε⌉₊ := by
    intro S hS
    have hreal := card_mul_le_of_sum_ennreal_le (show 0 ≤ 2 * Real.pi by positivity) hε.le
      (sum_measure_boundary_future_jumps_le F T S
        (fun t ht => ⟨(hS ht).1, (hS ht).2.1⟩) hclosed hmono)
      (fun t ht => (hS ht).2.2)
    have hdiv : (S.card : ℝ) ≤ 2 * Real.pi / ε := (le_div_iff₀ hε).2 hreal
    exact_mod_cast hdiv.trans (Nat.le_ceil _)
  have hfinite : A.Finite := by
    by_contra h
    obtain ⟨S, hS, hsize⟩ := (show A.Infinite from h).exists_subset_card_eq
      (⌈2 * Real.pi / ε⌉₊ + 1)
    have hbound := hcard S hS
    omega
  rw [hfinite.encard_eq_coe_toFinset_card]
  exact_mod_cast hcard hfinite.toFinset (by simp)

universe u

/-- Almost surely, simultaneously for all centres and horizons, boundary
jumps with one-dimensional measure at least `ε` satisfy the geometric bound. -/
theorem ae_encard_large_boundary_future_jumps_le
    (h33 : ClusterMonotoneStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα₀ : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ T : ℝ, ∀ z ∈ ball (0 : ℂ) 1, ∀ ε : ℝ, 0 < ε →
      {t : ℝ | 0 < t ∧ t < T ∧ ENNReal.ofReal ε ≤
        μH[1] (((⋂ n : ℕ, closure (cluster (μ ω) 1 z (t + dyadicScale n))) ∩ sphere 0 1) \
          closure (cluster (μ ω) 1 z t))}.encard ≤ ⌈2 * Real.pi / ε⌉₊ := by
  filter_upwards [h33 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hmono
  intro T z hz ε hε
  apply encard_large_boundary_future_jumps_le (fun t => closure (cluster (μ ω) 1 z t)) T ε hε
  · exact fun _ => isClosed_closure
  · intro a b ha hab
    exact closure_mono (hmono a b 1 ha hab zero_lt_one z hz)

end HarmonicBalls

