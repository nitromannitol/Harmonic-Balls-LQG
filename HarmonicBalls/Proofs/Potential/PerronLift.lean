import Mathlib
import HarmonicBalls.Proofs.Potential.DiscPoisson
import HarmonicBalls.Proofs.Potential.PerronSubMean

/-!
# Harmonic modification of a function in a disc

For a function `v` and a disc `ball c ρ`, the *harmonic modification* `harmonicLift c ρ v` equals
the Poisson integral of `v` on the disc and `v` outside the disc (Gilbarg–Trudinger, *Elliptic
Partial Differential Equations of Second Order*, Section 2.8, p. 21).  When `v` is continuous with
the local sub-mean-value property on an open set `Ω` containing the closed disc, the modification
is continuous, lies above `v`, has the local sub-mean-value property, is harmonic in the disc and
agrees with `v` outside the disc.

* `HarmonicBalls.harmonicLift`: the definition;
* `HarmonicBalls.harmonicOnNhd_harmonicLift`: harmonicity in the disc;
* `HarmonicBalls.continuousOn_harmonicLift`: continuity;
* `HarmonicBalls.le_harmonicLift`: `v ≤ harmonicLift c ρ v`;
* `HarmonicBalls.isLocalSubMean_harmonicLift`: the local sub-mean-value property;
* `HarmonicBalls.harmonicLift_mono`: monotonicity in `v`.
-/

namespace HarmonicBalls

open Metric Set Filter Topology InnerProductSpace

open Classical in
/-- The harmonic modification of `v` in `ball c ρ`: the Poisson integral of `v` inside the disc and
`v` outside. -/
noncomputable def harmonicLift (c : ℂ) (ρ : ℝ) (v : ℂ → ℝ) : ℂ → ℝ :=
  fun z => if z ∈ ball c ρ then discPoissonIntegral v c ρ z else v z

theorem harmonicLift_of_mem {c : ℂ} {ρ : ℝ} {v : ℂ → ℝ} {z : ℂ} (hz : z ∈ ball c ρ) :
    harmonicLift c ρ v z = discPoissonIntegral v c ρ z := by
  simp [harmonicLift, hz]

theorem harmonicLift_of_notMem {c : ℂ} {ρ : ℝ} {v : ℂ → ℝ} {z : ℂ} (hz : z ∉ ball c ρ) :
    harmonicLift c ρ v z = v z := by
  simp [harmonicLift, hz]

/-- The harmonic modification is harmonic in the disc. -/
theorem harmonicOnNhd_harmonicLift {c : ℂ} {ρ : ℝ} {v : ℂ → ℝ} (hρ : 0 < ρ)
    (hv : ContinuousOn v (sphere c ρ)) : HarmonicOnNhd (harmonicLift c ρ v) (ball c ρ) := by
  intro x hx
  have h := harmonicOnNhd_discPoissonIntegral (hv.circleIntegrable hρ.le) x hx
  refine (harmonicAt_congr_nhds ?_).mpr h
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  exact harmonicLift_of_mem hy

/-- The harmonic modification is continuous wherever `v` is, provided the circle is in the set. -/
theorem continuousOn_harmonicLift {c : ℂ} {ρ : ℝ} {v : ℂ → ℝ} {s : Set ℂ} (hρ : 0 < ρ)
    (hvs : ContinuousOn v s) (hsph : sphere c ρ ⊆ s) : ContinuousOn (harmonicLift c ρ v) s := by
  intro z hzs
  have hvsph : ContinuousOn v (sphere c ρ) := hvs.mono hsph
  by_cases hz : z ∈ ball c ρ
  · exact ((harmonicOnNhd_harmonicLift hρ hvsph z hz).1.continuousAt).continuousWithinAt
  · by_cases hzs' : z ∈ sphere c ρ
    · have hunion : s ⊆ (s ∩ ball c ρ) ∪ (s ∩ (ball c ρ)ᶜ) := fun y hy => by
        by_cases hyb : y ∈ ball c ρ
        · exact Or.inl ⟨hy, hyb⟩
        · exact Or.inr ⟨hy, hyb⟩
      refine ContinuousWithinAt.mono (ContinuousWithinAt.union ?_ ?_) hunion
      · have ht := tendsto_discPoissonIntegral_of_continuousOn hρ hvsph hzs'
        have ht' : Tendsto (harmonicLift c ρ v) (𝓝[ball c ρ] z) (𝓝 (v z)) :=
          ht.congr' (eventually_nhdsWithin_of_forall fun y hy => (harmonicLift_of_mem hy).symm)
        rw [ContinuousWithinAt, harmonicLift_of_notMem hz]
        exact ht'.mono_left (nhdsWithin_mono z inter_subset_right)
      · exact ((hvs z hzs).mono inter_subset_left).congr
          (fun y hy => harmonicLift_of_notMem hy.2) (harmonicLift_of_notMem hz)
    · have hzc : z ∈ (closedBall c ρ)ᶜ := by
        intro hzc
        rw [← ball_union_sphere] at hzc
        exact hzc.elim hz hzs'
      refine (hvs z hzs).congr_of_eventuallyEq ?_ (harmonicLift_of_notMem hz)
      filter_upwards [nhdsWithin_le_nhds (isClosed_closedBall.isOpen_compl.mem_nhds hzc)] with y hy
      exact harmonicLift_of_notMem fun hyb => hy (ball_subset_closedBall hyb)

/-- A function with the local sub-mean-value property on an open set containing the closed disc
lies below its harmonic modification on the disc. -/
theorem le_harmonicLift {Ω : Set ℂ} {v : ℂ → ℝ} {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hball : closedBall c ρ ⊆ Ω) (hvc : ContinuousOn v (closedBall c ρ))
    (hv : IsLocalSubMean Ω v) (z : ℂ) : v z ≤ harmonicLift c ρ v z := by
  by_cases hz : z ∈ ball c ρ
  · have hcl : closure (ball c ρ) = closedBall c ρ := closure_ball c hρ.ne'
    have hfr : frontier (ball c ρ) = sphere c ρ := frontier_ball c hρ.ne'
    refine IsLocalSubMean.le_harmonic_of_le_frontier isOpen_ball Metric.isBounded_ball
      (by rw [hcl]; exact hvc)
      (by rw [hcl]; exact continuousOn_harmonicLift hρ hvc sphere_subset_closedBall)
      (harmonicOnNhd_harmonicLift hρ (hvc.mono sphere_subset_closedBall))
      (hv.mono_open isOpen_ball (ball_subset_closedBall.trans hball)) ?_ z hz
    intro x hx
    rw [hfr] at hx
    have hxb : x ∉ ball c ρ := fun h => by
      have h1 := mem_sphere.mp hx
      have h2 := mem_ball.mp h
      linarith
    rw [harmonicLift_of_notMem hxb]
  · rw [harmonicLift_of_notMem hz]

/-- Monotonicity of the harmonic modification in the function. -/
theorem harmonicLift_mono {c : ℂ} {ρ : ℝ} {v w : ℂ → ℝ} {s : Set ℂ} (hρ : 0 < ρ)
    (hv : ContinuousOn v (sphere c ρ)) (hw : ContinuousOn w (sphere c ρ))
    (hsph : sphere c ρ ⊆ s) (hle : ∀ z ∈ s, v z ≤ w z) {z : ℂ} (hzs : z ∈ s) :
    harmonicLift c ρ v z ≤ harmonicLift c ρ w z := by
  by_cases hz : z ∈ ball c ρ
  · rw [harmonicLift_of_mem hz, harmonicLift_of_mem hz]
    exact discPoissonIntegral_mono (hv.circleIntegrable hρ.le) (hw.circleIntegrable hρ.le) hz
      fun y hy => hle y (hsph hy)
  · rw [harmonicLift_of_notMem hz, harmonicLift_of_notMem hz]
    exact hle z hzs

/-- The harmonic modification of a function with the local sub-mean-value property, continuous on
the closure of an open set containing the closed disc, has the local sub-mean-value property. -/
theorem isLocalSubMean_harmonicLift {Ω : Set ℂ} {v : ℂ → ℝ} {c : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hball : closedBall c ρ ⊆ Ω) (hvc : ContinuousOn v (closure Ω))
    (hv : IsLocalSubMean Ω v) : IsLocalSubMean Ω (harmonicLift c ρ v) := by
  have hcl : closedBall c ρ ⊆ closure Ω := hball.trans subset_closure
  have hvsph : ContinuousOn v (sphere c ρ) :=
    hvc.mono (sphere_subset_closedBall.trans hcl)
  have hci : CircleIntegrable v c ρ := hvsph.circleIntegrable hρ.le
  have hlc : ContinuousOn (harmonicLift c ρ v) (closure Ω) :=
    continuousOn_harmonicLift hρ hvc (sphere_subset_closedBall.trans hcl)
  have hle : ∀ z, v z ≤ harmonicLift c ρ v z := fun z =>
    le_harmonicLift hρ hball (hvc.mono hcl) hv z
  intro x hx
  obtain ⟨r, hr, hrU, hmean⟩ := hv x hx
  by_cases hxb : x ∈ ball c ρ
  · obtain ⟨r', hr', hr'sub⟩ := Metric.isOpen_iff.mp isOpen_ball x hxb
    refine ⟨r', hr', hr'sub.trans (ball_subset_closedBall.trans hball), fun ρ' hρ' hρ'r' => ?_⟩
    have hsub : closedBall x |ρ'| ⊆ ball c ρ := by
      rw [abs_of_pos hρ']
      exact (closedBall_subset_ball hρ'r').trans hr'sub
    have h1 : Real.circleAverage (harmonicLift c ρ v) x ρ' =
        Real.circleAverage (discPoissonIntegral v c ρ) x ρ' :=
      Real.circleAverage_congr_sphere fun z hz =>
        harmonicLift_of_mem (hsub (sphere_subset_closedBall hz))
    rw [h1, circleAverage_discPoissonIntegral hci hsub, harmonicLift_of_mem hxb]
  · refine ⟨r, hr, hrU, fun ρ' hρ' hρ'r => ?_⟩
    have hcl' : closedBall x ρ' ⊆ Ω := (closedBall_subset_ball hρ'r).trans hrU
    have hiv := circleIntegrable_of_continuousOn_closedBall hρ'
      (hvc.mono (hcl'.trans subset_closure))
    have hil := circleIntegrable_of_continuousOn_closedBall hρ'
      (hlc.mono (hcl'.trans subset_closure))
    rw [harmonicLift_of_notMem hxb]
    exact (hmean ρ' hρ' hρ'r).trans (Real.circleAverage_mono hiv hil fun z _ => hle z)

end HarmonicBalls
