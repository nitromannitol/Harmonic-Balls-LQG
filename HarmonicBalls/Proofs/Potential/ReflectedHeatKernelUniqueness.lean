import HarmonicBalls.Proofs.Potential.ReflectedLQGRevuzMeasure

/-!
# Uniqueness of jointly continuous heat kernels

A heat kernel `p` of a time-changed process with respect to a reference measure `ν` on `K`
(`IsLBMHeatKernel`) is determined `ν`-almost everywhere in `y` by the transition laws. If `ν`
charges every relative ball `B(y, r) ∩ K`, `y ∈ K`, two kernels that are jointly continuous on
`(0, ∞) × K × K` agree everywhere there (`IsLBMHeatKernel.eq_of_continuousOn`). The normalized LQG
measure of a square carried to the unit square charges every relative ball of the unit square,
almost surely (`ae_forall_closedSquare_unitSquareNormalizedMeasure_ball_inter_pos`), by the lower
volume bound of Kigami's condition (13.1).
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Set Filter Topology MarkovProcess Metric
open scoped ENNReal NNReal

/-- **Uniqueness of jointly continuous heat kernels.** If the σ-finite measure `ν` charges every
relative ball `B(y, r) ∩ K` with `y ∈ K`, two heat kernels of the same time-changed process with
respect to `ν`, both jointly continuous on `(0, ∞) × K × K`, agree there. -/
theorem IsLBMHeatKernel.eq_of_continuousOn {Q : Kernel ℂ (ContinuousPath ℂ)}
    {F : ℂ → ContinuousPath ℂ → ℝ≥0 → ℝ} {K : Set ℂ} (hKm : MeasurableSet K) {ν : Measure ℂ}
    [SigmaFinite ν] (hsupp : ∀ y ∈ K, ∀ r : ℝ, 0 < r → 0 < ν (ball y r ∩ K))
    {p q : ℝ → ℂ → ℂ → ℝ} (hp : IsLBMHeatKernel Q F K ν p) (hq : IsLBMHeatKernel Q F K ν q)
    (hpc : ContinuousOn (fun s : ℝ × ℂ × ℂ => p s.1 s.2.1 s.2.2) (Ioi 0 ×ˢ K ×ˢ K))
    (hqc : ContinuousOn (fun s : ℝ × ℂ × ℂ => q s.1 s.2.1 s.2.2) (Ioi 0 ×ˢ K ×ˢ K))
    {t : ℝ} (ht : 0 < t) {x : ℂ} (hx : x ∈ K) {y : ℂ} (hy : y ∈ K) : p t x y = q t x y := by
  obtain ⟨hp0, hpS⟩ := hp t ht x hx
  obtain ⟨hq0, hqS⟩ := hq t ht x hx
  have hmaps : MapsTo (fun z : ℂ => (t, x, z)) K (Ioi 0 ×ˢ K ×ˢ K) := fun z hz => ⟨ht, hx, hz⟩
  have hpy : ContinuousOn (fun z => p t x z) K :=
    hpc.comp (by fun_prop : Continuous fun z : ℂ => (t, x, z)).continuousOn hmaps
  have hqy : ContinuousOn (fun z => q t x z) K :=
    hqc.comp (by fun_prop : Continuous fun z : ℂ => (t, x, z)).continuousOn hmaps
  -- the two densities agree almost everywhere on `K`
  have hfm : AEMeasurable (fun z => ENNReal.ofReal (p t x z)) (ν.restrict K) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hpy.aemeasurable hKm)
  have hgm : AEMeasurable (fun z => ENNReal.ofReal (q t x z)) (ν.restrict K) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hqy.aemeasurable hKm)
  have hae : (fun z => ENNReal.ofReal (p t x z)) =ᵐ[ν.restrict K]
      fun z => ENNReal.ofReal (q t x z) := by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ hfm hgm fun S hS _ => ?_
    rw [Measure.restrict_restrict hS, ← hpS S hS, ← hqS S hS]
  rw [EventuallyEq, ae_restrict_iff' hKm] at hae
  by_contra hne
  have hd : ContinuousWithinAt (fun z => p t x z - q t x z) K y :=
    (hpy y hy).sub (hqy y hy)
  have hev : ∀ᶠ z in 𝓝[K] y, p t x z - q t x z ≠ 0 :=
    hd.eventually (isOpen_ne.mem_nhds (sub_ne_zero.2 hne))
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhdsWithin_iff.1 hev
  have hnull : ν (ball y r ∩ K) = 0 := by
    refine measure_mono_null (fun z hz => ?_) (ae_iff.1 hae)
    intro hzK
    have h1 : p t x z - q t x z ≠ 0 := hsub hz
    have h2 := (ENNReal.ofReal_eq_ofReal_iff (hp0 z hz.2) (hq0 z hz.2)).1 (hzK hz.2)
    exact h1 (sub_eq_zero.2 h2)
  exact (hsupp y hy r hr).ne' hnull

/-- **The normalized LQG measure charges every relative ball of the unit square**, almost surely
for every square. -/
theorem ae_forall_closedSquare_unitSquareNormalizedMeasure_ball_inter_pos {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ (a : ℂ) (L : ℝ), 0 < L → ∀ y ∈ closedSquare 0 1, ∀ r : ℝ, 0 < r →
      0 < unitSquareNormalizedMeasure (μ ω) a L (ball y r ∩ closedSquare 0 1) := by
  filter_upwards [ae_forall_closedSquare_kigamiVolumeBounds hγ hγ2 hα hh hμ] with ω hω
  intro a L hL y hy r hr
  obtain ⟨-, hcarried, c₁, c₂, α₁, α₂, hc₁, -, -, -, -, hb⟩ := hω a L hL
  set ν := unitSquareNormalizedMeasure (μ ω) a L
  set r' := min r 1 with hr'
  have hr'0 : 0 < r' := lt_min hr one_pos
  have hball : ν (ball y r') ≤ ν (ball y r ∩ closedSquare 0 1) := by
    calc ν (ball y r') ≤ ν (ball y r) := measure_mono (ball_subset_ball (min_le_left _ _))
      _ ≤ ν (ball y r ∩ closedSquare 0 1) + ν (closedSquare 0 1)ᶜ := by
          refine (measure_mono fun z hz => ?_).trans (measure_union_le _ _)
          by_cases hz' : z ∈ closedSquare 0 1
          · exact Or.inl ⟨hz, hz'⟩
          · exact Or.inr hz'
      _ = ν (ball y r ∩ closedSquare 0 1) := by rw [hcarried, add_zero]
  refine lt_of_lt_of_le ?_ ((hb y hy r' hr'0 (min_le_right _ _)).1.trans hball)
  exact ENNReal.ofReal_pos.2 (mul_pos hc₁ (Real.rpow_pos_of_pos hr'0 _))

end HarmonicBalls
