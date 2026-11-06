import HarmonicBalls.Proofs.Sec6.JointRootAnnulusRegularity
import HarmonicBalls.Proofs.Sec6.RelativeCollarTransferProbability

/-! # Relative collar mass under rooted laws

The imported Section 6 iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal Topology

/-- The mass of a two-sided shrinking collar tends to zero when both
boundary circles are null. -/
theorem tendsto_twoSided_annulus_collar_mass_zero
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] (z : ℂ) (r R : ℝ)
    (hr : μ (sphere z r) = 0) (hR : μ (sphere z R) = 0) :
    Tendsto (fun n : ℕ => μ (annulus z (r - 1 / ((n : ℝ) + 1))
      (R + 1 / ((n : ℝ) + 1)) \ annulus z (r + 1 / ((n : ℝ) + 1))
      (R - 1 / ((n : ℝ) + 1)))) atTop (𝓝 0) := by
  let e : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have he (n : ℕ) : 0 < e n := by dsimp [e]; positivity
  have ht : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 : Tendsto (fun n => 2 * e n) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul ht
  have hl (s : ℝ) (hs : μ (sphere z s) = 0) :
      Tendsto (fun n => μ (annulus z (s - 2 * e n) (s + 2 * e n))) atTop (𝓝 0) := by
    have h := tendsto_annulus_mass_of_tendsto_boundaries μ
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => z) atTop (𝓝 z))
      (by simpa using tendsto_const_nhds.sub h2)
      (by simpa using tendsto_const_nhds.add h2) hs hs
    have hempty : annulus z s s = ∅ := sdiff_eq_empty.mpr ball_subset_closedBall
    simpa only [hempty, measure_empty] using h
  have hb := (hl r hr).add (hl R hR)
  have hbound (n : ℕ) :
      μ (annulus z (r-e n) (R+e n) \ annulus z (r+e n) (R-e n)) ≤
      μ (annulus z (r-2*e n) (r+2*e n)) +
        μ (annulus z (R-2*e n) (R+2*e n)) := by
    calc
      _ ≤ μ (annulus z (r-2*e n) (r+2*e n) ∪
          annulus z (R-2*e n) (R+2*e n)) := by
        apply measure_mono
        intro x hx
        simp only [annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le,
          mem_union] at hx ⊢
        by_cases h : dist x z < R - e n
        · left
          have hh : dist x z ≤ r + e n := le_of_not_gt (fun hh => hx.2 ⟨h, hh⟩)
          constructor <;> linarith [hx.1.1, hx.1.2, he n]
        · right; constructor <;> linarith [hx.1.1, hx.1.2, he n]
      _ ≤ _ := measure_union_le _ _
  change Tendsto (fun n => μ (annulus z (r-e n) (R+e n) \
    annulus z (r+e n) (R-e n))) atTop (𝓝 0)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [zero_add] using hb) (fun _ => bot_le) hbound

/-- At a fixed radius, relative two-sided collar failure tends to zero under
any finite rooted law with regular annuli. The result supplies no rate and
makes no assertion uniform in the radius. -/
theorem tendsto_rooted_relative_collar_failure
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure (Ω × ℂ)) [IsFiniteMeasure Q]
    (μ : Ω → Measure ℂ) (hμ : Measurable μ)
    (hloc : ∀ ω, IsLocallyFiniteMeasure (μ ω)) (r R : ℝ) {d : ℝ≥0∞} (hd : 0 < d)
    (hreg : ∀ᵐ p ∂Q, μ p.1 (sphere p.2 r) = 0 ∧
      μ p.1 (sphere p.2 R) = 0 ∧ 0 < μ p.1 (annulus p.2 r R)) :
    Tendsto (fun n : ℕ => Q {p | d * μ p.1 (annulus p.2 r R) <
      μ p.1 (annulus p.2 (r-1/((n : ℝ)+1)) (R+1/((n : ℝ)+1)) \
        annulus p.2 (r+1/((n : ℝ)+1)) (R-1/((n : ℝ)+1)))}) atTop (𝓝 0) := by
  let ν : Ω × ℂ → Measure ℂ := fun p => (μ p.1).map (fun x => x - p.2)
  have hν : Measurable ν := measurable_map_of_locallyFinite (hμ.comp measurable_fst)
    (fun p => hloc p.1) (f := fun p : (Ω × ℂ) × ℂ => p.2 - p.1.2) (by fun_prop)
  have ha (p : Ω × ℂ) (s t : ℝ) : ν p (annulus 0 s t) = μ p.1 (annulus p.2 s t) := by
    have hm : MeasurableSet (annulus (0 : ℂ) s t) :=
      isOpen_ball.measurableSet.diff measurableSet_closedBall
    rw [show ν p = (μ p.1).map (fun x => x-p.2) from rfl, Measure.map_apply (by fun_prop) hm]
    congr 1
    ext x
    simp [annulus, mem_ball, mem_closedBall, dist_eq_norm]
  have hc (p : Ω × ℂ) (s t s' t' : ℝ) :
      ν p (annulus 0 s t \ annulus 0 s' t') =
        μ p.1 (annulus p.2 s t \ annulus p.2 s' t') := by
    have hm : MeasurableSet (annulus (0 : ℂ) s t \ annulus 0 s' t') :=
      (isOpen_ball.measurableSet.diff measurableSet_closedBall).diff
        (isOpen_ball.measurableSet.diff measurableSet_closedBall)
    rw [show ν p = (μ p.1).map (fun x => x-p.2) from rfl, Measure.map_apply (by fun_prop) hm]
    congr 1
    ext x
    simp [annulus, mem_ball, mem_closedBall, dist_eq_norm]
  let E : ℕ → Set (Ω × ℂ) := fun n => {p | d * μ p.1 (annulus p.2 r R) <
      μ p.1 (annulus p.2 (r-1/((n : ℝ)+1)) (R+1/((n : ℝ)+1)) \
        annulus p.2 (r+1/((n : ℝ)+1)) (R-1/((n : ℝ)+1)))}
  have hE (n : ℕ) : MeasurableSet (E n) := by
    have hA : Measurable (fun p : Ω × ℂ => μ p.1 (annulus p.2 r R)) := by
      have h := (Measure.measurable_coe (isOpen_ball.measurableSet.diff
        measurableSet_closedBall : MeasurableSet (annulus (0 : ℂ) r R))).comp hν
      change Measurable (fun p => ν p (annulus 0 r R)) at h
      simpa only [ha] using h
    have hC : Measurable (fun p : Ω × ℂ => μ p.1
        (annulus p.2 (r-1/((n : ℝ)+1)) (R+1/((n : ℝ)+1)) \
          annulus p.2 (r+1/((n : ℝ)+1)) (R-1/((n : ℝ)+1)))) := by
      have h := (Measure.measurable_coe ((isOpen_ball.measurableSet.diff
        measurableSet_closedBall).diff (isOpen_ball.measurableSet.diff
        measurableSet_closedBall) : MeasurableSet (annulus (0 : ℂ)
          (r-1/((n : ℝ)+1)) (R+1/((n : ℝ)+1)) \
            annulus 0 (r+1/((n : ℝ)+1)) (R-1/((n : ℝ)+1))))).comp hν
      change Measurable (fun p => ν p (annulus 0 (r-1/((n : ℝ)+1))
        (R+1/((n : ℝ)+1)) \ annulus 0 (r+1/((n : ℝ)+1))
        (R-1/((n : ℝ)+1)))) at h
      simpa only [hc] using h
    exact measurableSet_lt (measurable_const.mul hA) hC
  have hlim : ∀ᵐ p ∂Q, ∀ᶠ n in atTop, p ∈ E n ↔ p ∈ (∅ : Set (Ω × ℂ)) := by
    filter_upwards [hreg] with p ⟨h3, h5, hp⟩
    let : IsLocallyFiniteMeasure (μ p.1) := hloc p.1
    have ht := tendsto_twoSided_annulus_collar_mass_zero (μ p.1) p.2 r R h3 h5
    have hpos : 0 < d * μ p.1 (annulus p.2 r R) := ENNReal.mul_pos hd.ne' hp.ne'
    filter_upwards [ht.eventually_lt_const hpos] with n hn
    simp only [E, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
    exact hn.le
  simpa only [measure_empty] using
    tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop MeasurableSet.empty hE hlim

end HarmonicBalls.Section6
