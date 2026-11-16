import Mathlib
import LatticeProb.Analysis.SuperharmonicMinimumPrinciple

/-!
# Locally sub-mean-valued functions in the plane and their maximum principles

A function `u : ℂ → ℝ` has the *local sub-mean-value property* on an open set `U` when every point
`x ∈ U` has a radius `r > 0` with `ball x r ⊆ U` such that `u x` is at most the circle average of
`u` over `sphere x ρ` for all `0 < ρ < r`.  This is the continuous form of subharmonicity used in
the Perron method (Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*,
Section 2.8, pp. 20–21).

* `HarmonicBalls.IsLocalSubMean`: the definition;
* `HarmonicBalls.IsLocalSubMean.mono_open`: restriction to a smaller open set;
* `HarmonicBalls.IsLocalSubMean.sup`: the pointwise maximum of two such functions;
* `HarmonicBalls.IsLocalSubMean.sub_harmonic`: subtraction of a harmonic function;
* `HarmonicBalls.IsLocalSubMean.eq_of_isMaxOn`: the strong maximum principle on a connected open
  set;
* `HarmonicBalls.IsLocalSubMean.le_of_le_frontier`: the weak maximum principle on a bounded open
  set;
* `HarmonicBalls.IsLocalSubMean.le_harmonic_of_le_frontier`: comparison with a harmonic function.
-/

namespace HarmonicBalls

open Metric Set Filter Topology

/-- The local sub-mean-value property of `u` on the open set `U`. -/
def IsLocalSubMean (U : Set ℂ) (u : ℂ → ℝ) : Prop :=
  ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ ball x r ⊆ U ∧
    ∀ ρ : ℝ, 0 < ρ → ρ < r → u x ≤ Real.circleAverage u x ρ

/-- A function continuous on a closed disc is circle integrable on its boundary circle. -/
theorem circleIntegrable_of_continuousOn_closedBall {u : ℂ → ℝ} {x : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hu : ContinuousOn u (closedBall x ρ)) : CircleIntegrable u x ρ := by
  refine ContinuousOn.circleIntegrable' ?_
  rw [abs_of_pos hρ]
  exact hu.mono sphere_subset_closedBall

/-- The circle average of a function harmonic near a closed disc is its centre value. -/
theorem circleAverage_eq_of_harmonicOnNhd {U : Set ℂ} {h : ℂ → ℝ}
    (hh : InnerProductSpace.HarmonicOnNhd h U) {x : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closedBall x ρ ⊆ U) : Real.circleAverage h x ρ = h x := by
  have h1 : InnerProductSpace.HarmonicOnNhd h (closedBall x |ρ|) := by
    rw [abs_of_pos hρ]
    exact hh.mono hsub
  exact h1.circleAverage_eq

/-- A function harmonic on an open set has the local sub-mean-value property there. -/
theorem IsLocalSubMean.of_harmonicOnNhd {U : Set ℂ} {h : ℂ → ℝ} (hU : IsOpen U)
    (hh : InnerProductSpace.HarmonicOnNhd h U) : IsLocalSubMean U h := by
  intro x hx
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU x hx
  refine ⟨r, hr, hrU, fun ρ hρ hρr => ?_⟩
  exact (circleAverage_eq_of_harmonicOnNhd hh hρ
    ((closedBall_subset_ball hρr).trans hrU)).ge

/-- Restriction of the local sub-mean-value property to a smaller open set. -/
theorem IsLocalSubMean.mono_open {U V : Set ℂ} {u : ℂ → ℝ} (hV : IsOpen V) (hVU : V ⊆ U)
    (hu : IsLocalSubMean U u) : IsLocalSubMean V u := by
  intro x hx
  obtain ⟨r, hr, -, hmean⟩ := hu x (hVU hx)
  obtain ⟨r', hr', hr'V⟩ := Metric.isOpen_iff.mp hV x hx
  refine ⟨min r r', lt_min hr hr', (ball_subset_ball (min_le_right _ _)).trans hr'V,
    fun ρ hρ hρr => hmean ρ hρ (hρr.trans_le (min_le_left _ _))⟩

/-- The pointwise maximum of two continuous functions with the local sub-mean-value property has the
local sub-mean-value property. -/
theorem IsLocalSubMean.sup {U : Set ℂ} {u v : ℂ → ℝ} (hu : IsLocalSubMean U u)
    (hv : IsLocalSubMean U v) (huc : ContinuousOn u U) (hvc : ContinuousOn v U) :
    IsLocalSubMean U (fun z => max (u z) (v z)) := by
  intro x hx
  obtain ⟨r₁, hr₁, hr₁U, h₁⟩ := hu x hx
  obtain ⟨r₂, hr₂, hr₂U, h₂⟩ := hv x hx
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, (ball_subset_ball (min_le_left _ _)).trans hr₁U,
    fun ρ hρ hρr => ?_⟩
  have hcl : closedBall x ρ ⊆ U :=
    (closedBall_subset_ball (hρr.trans_le (min_le_left _ _))).trans hr₁U
  have hiu := circleIntegrable_of_continuousOn_closedBall hρ (huc.mono hcl)
  have hiv := circleIntegrable_of_continuousOn_closedBall hρ (hvc.mono hcl)
  have him : CircleIntegrable (fun z => max (u z) (v z)) x ρ :=
    circleIntegrable_of_continuousOn_closedBall hρ (ContinuousOn.sup (huc.mono hcl) (hvc.mono hcl))
  have hm1 : Real.circleAverage u x ρ ≤ Real.circleAverage (fun z => max (u z) (v z)) x ρ :=
    Real.circleAverage_mono hiu him fun z _ => le_max_left _ _
  have hm2 : Real.circleAverage v x ρ ≤ Real.circleAverage (fun z => max (u z) (v z)) x ρ :=
    Real.circleAverage_mono hiv him fun z _ => le_max_right _ _
  have e1 := h₁ ρ hρ (hρr.trans_le (min_le_left _ _))
  have e2 := h₂ ρ hρ (hρr.trans_le (min_le_right _ _))
  exact max_le (e1.trans hm1) (e2.trans hm2)

/-- Subtracting a function harmonic on `U` preserves the local sub-mean-value property. -/
theorem IsLocalSubMean.sub_harmonic {U : Set ℂ} {u h : ℂ → ℝ} (hu : IsLocalSubMean U u)
    (huc : ContinuousOn u U) (hh : InnerProductSpace.HarmonicOnNhd h U) :
    IsLocalSubMean U (fun z => u z - h z) := by
  intro x hx
  obtain ⟨r, hr, hrU, hmean⟩ := hu x hx
  refine ⟨r, hr, hrU, fun ρ hρ hρr => ?_⟩
  have hcl : closedBall x ρ ⊆ U := (closedBall_subset_ball hρr).trans hrU
  have hiu := circleIntegrable_of_continuousOn_closedBall hρ (huc.mono hcl)
  have hih := circleIntegrable_of_continuousOn_closedBall hρ (hh.continuousOn.mono hcl)
  have hsub : Real.circleAverage (fun z => u z - h z) x ρ =
      Real.circleAverage u x ρ - Real.circleAverage h x ρ :=
    Real.circleAverage_fun_sub hiu hih
  rw [hsub, circleAverage_eq_of_harmonicOnNhd hh hρ hcl]
  linarith [hmean ρ hρ hρr]

/-- Near a maximum point of a function with the local sub-mean-value property, the function is
constant. -/
theorem IsLocalSubMean.exists_ball_eq_of_isMaxOn {U : Set ℂ} {u : ℂ → ℝ}
    (hu : IsLocalSubMean U u) (huc : ContinuousOn u U) {m : ℝ} (hle : ∀ z ∈ U, u z ≤ m) {x : ℂ}
    (hx : x ∈ U) (hxm : u x = m) :
    ∃ r : ℝ, 0 < r ∧ ball x r ⊆ U ∧ ∀ z ∈ ball x r, u z = m := by
  obtain ⟨r, hr, hrU, hmean⟩ := hu x hx
  refine ⟨r, hr, hrU, fun z hz => ?_⟩
  rcases eq_or_ne z x with rfl | hzx
  · exact hxm
  · have hρ : 0 < dist z x := dist_pos.mpr hzx
    have hρr : dist z x < r := mem_ball.mp hz
    have hcl : closedBall x (dist z x) ⊆ U := (closedBall_subset_ball hρr).trans hrU
    have hsph : sphere x (dist z x) ⊆ U := sphere_subset_closedBall.trans hcl
    have hiu := circleIntegrable_of_continuousOn_closedBall hρ (huc.mono hcl)
    have havg : Real.circleAverage (fun w => m - u w) x (dist z x) ≤ 0 := by
      rw [Real.circleAverage_fun_sub (circleIntegrable_const _ _ _) hiu,
        Real.circleAverage_const]
      have := hmean _ hρ hρr
      linarith
    have := LatticeProb.eq_of_mem_sphere_of_circleAverage_le (f := fun w => m - u w) (m := 0) hρ
      (continuousOn_const.sub (huc.mono hsph)) (fun w hw => sub_nonneg.mpr (hle w (hsph hw)))
      havg (mem_sphere.mpr rfl)
    linarith

/-- **Strong maximum principle** for functions with the local sub-mean-value property on a connected
open set. -/
theorem IsLocalSubMean.eq_of_isMaxOn {U : Set ℂ} {u : ℂ → ℝ}
    (hconn : IsConnected U) (hu : IsLocalSubMean U u) (huc : ContinuousOn u U) {x₀ : ℂ}
    (hx₀ : x₀ ∈ U) (hmax : ∀ x ∈ U, u x ≤ u x₀) : ∀ x ∈ U, u x = u x₀ := by
  have hopen : IsOpen {x | x ∈ U ∧ u x = u x₀} := by
    rw [Metric.isOpen_iff]
    rintro x ⟨hxU, hxm⟩
    obtain ⟨r, hr, hrU, hball⟩ := hu.exists_ball_eq_of_isMaxOn huc hmax hxU hxm
    exact ⟨r, hr, fun z hz => ⟨hrU hz, hball z hz⟩⟩
  have hclosed : closure {x | x ∈ U ∧ u x = u x₀} ∩ U ⊆ {x | x ∈ U ∧ u x = u x₀} := by
    rintro z ⟨hzc, hzU⟩
    refine ⟨hzU, ?_⟩
    have hSU : {x | x ∈ U ∧ u x = u x₀} ⊆ U := fun x hx => hx.1
    have hNB : NeBot (𝓝[{x | x ∈ U ∧ u x = u x₀}] z) := mem_closure_iff_nhdsWithin_neBot.mp hzc
    have h1 : Tendsto u (𝓝[{x | x ∈ U ∧ u x = u x₀}] z) (𝓝 (u z)) := (huc z hzU).mono hSU
    have hEq : (fun _ => u x₀) =ᶠ[𝓝[{x | x ∈ U ∧ u x = u x₀}] z] u :=
      eventually_nhdsWithin_of_forall fun w hw => hw.2.symm
    have h2 : Tendsto u (𝓝[{x | x ∈ U ∧ u x = u x₀}] z) (𝓝 (u x₀)) :=
      Filter.Tendsto.congr' hEq tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  have hsub := hconn.isPreconnected.subset_of_closure_inter_subset hopen ⟨x₀, hx₀, hx₀, rfl⟩
    hclosed
  intro x hx
  exact (hsub hx).2

/-- **Weak maximum principle** for functions with the local sub-mean-value property on a bounded
open set: a bound on the frontier is a bound on the set. -/
theorem IsLocalSubMean.le_of_le_frontier {U : Set ℂ} {u : ℂ → ℝ} {M : ℝ} (hU : IsOpen U)
    (hbdd : Bornology.IsBounded U) (huc : ContinuousOn u (closure U)) (hu : IsLocalSubMean U u)
    (hfr : ∀ x ∈ frontier U, u x ≤ M) : ∀ x ∈ U, u x ≤ M := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x₀, hx₀U, hx₀gt⟩ := hcon
  have hcpt : IsCompact (closure U) := hbdd.isCompact_closure
  obtain ⟨y, hyK, hymax⟩ := hcpt.exists_isMaxOn ⟨x₀, subset_closure hx₀U⟩ huc
  have hmax : ∀ v ∈ closure U, u v ≤ u y := fun v hv => isMaxOn_iff.mp hymax v hv
  have hMy : M < u y := lt_of_lt_of_le hx₀gt (hmax x₀ (subset_closure hx₀U))
  have hin : ∀ w ∈ closure U, u w = u y → w ∈ U := by
    intro w hw hwm
    by_contra hwU
    have hwfr : w ∈ frontier U := by
      rw [frontier, hU.interior_eq]
      exact ⟨hw, hwU⟩
    have := hfr w hwfr
    linarith
  have hmax' : ∀ z ∈ U, u z ≤ u y := fun z hz => hmax z (subset_closure hz)
  have hSclosed : IsClosed (closure U ∩ u ⁻¹' {u y}) :=
    huc.preimage_isClosed_of_isClosed isClosed_closure isClosed_singleton
  have hSopen : IsOpen (closure U ∩ u ⁻¹' {u y}) := by
    rw [Metric.isOpen_iff]
    rintro w ⟨hwc, hwm⟩
    have hwm' : u w = u y := hwm
    have hwU : w ∈ U := hin w hwc hwm'
    obtain ⟨r, hr, hrU, hball⟩ :=
      hu.exists_ball_eq_of_isMaxOn (huc.mono subset_closure) hmax' hwU hwm'
    exact ⟨r, hr, fun z hz => ⟨subset_closure (hrU hz), hball z hz⟩⟩
  have hSeq : closure U ∩ u ⁻¹' {u y} = univ :=
    IsClopen.eq_univ ⟨hSclosed, hSopen⟩ ⟨y, hyK, rfl⟩
  have hsubU : (univ : Set ℂ) ⊆ closure U := by
    rw [← hSeq]
    exact inter_subset_left
  exact (NormedSpace.unbounded_univ ℝ ℂ) (hbdd.closure.subset hsubU)

/-- **Comparison with a harmonic function** on a bounded open set: a function with the local
sub-mean-value property that lies below a harmonic function on the frontier lies below it in the
set. -/
theorem IsLocalSubMean.le_harmonic_of_le_frontier {U : Set ℂ} {u h : ℂ → ℝ} (hU : IsOpen U)
    (hbdd : Bornology.IsBounded U) (huc : ContinuousOn u (closure U))
    (hhc : ContinuousOn h (closure U)) (hh : InnerProductSpace.HarmonicOnNhd h U)
    (hu : IsLocalSubMean U u) (hfr : ∀ x ∈ frontier U, u x ≤ h x) : ∀ x ∈ U, u x ≤ h x := by
  have hs := hu.sub_harmonic (huc.mono subset_closure) hh
  have := IsLocalSubMean.le_of_le_frontier (M := 0) hU hbdd (huc.sub hhc) hs
    (fun x hx => sub_nonpos.mpr (hfr x hx))
  intro x hx
  exact sub_nonpos.mp (this x hx)

end HarmonicBalls
