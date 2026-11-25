import HarmonicBalls.Proofs.Potential.ReflectedHeatKernelL2Semigroup
import HarmonicBalls.Proofs.Potential.ReflectedClockStartPositivity
import HarmonicBalls.Proofs.Potential.ReflectedLQGRevuzMeasure
import HarmonicBalls.Proofs.Potential.LQGClockStrictEveryStart

/-!
# Proposition 2.6 from the cited theorems, symmetry and irreducibility of the time change

Proposition 2.6 (prop:lbm-continuity) was reduced to the cited theorem of Kigami
(`kigamiHeatKernelContinuityCited`, [Kig19, Theorem 13.1]) and positivity of the unit-square
kernel `p'` for every additive functional with the right Revuz measure
(`reflectedLBMHeatKernel_of_kigami_of_positivity`). This module

* requires positivity only for the clock `A` of the square, the additive functional of reflected
  Brownian motion in `K₀` with `F x b s = μ_h(K) A(s / L², Ψ b)` from every start
  (`reflectedLBMHeatKernel_of_identification_of_clockPositivity`);
* proves that positivity from the cited Keller–Lenz–Vogt–Wojciechowski Theorem A.2
  (`klvwPositivityImprovingCited`) and two properties of the transition semigroup of the time
  change on `L²(ν)` that enter as explicit hypotheses: the symmetry of the kernel `p'` (`hsymm`,
  the `ν`-symmetry of the time change, Fukushima–Oshima–Takeda (2011), Section 6.2) and the
  irreducibility of its transition semigroup `heatKernelL2Semigroup ν p'` (`hirr`, [KLVW]
  Definition A.1) (`reflectedLBMHeatKernel_of_kigami_of_klvw`).

The other inputs are proved: the clock identification (`ae_exists_isUnitSquarePCAF_revuz_eq`), the
Chapman–Kolmogorov identity (`IsLBMHeatKernel.chapmanKolmogorov`), the positivity of the clock at
positive times from almost every start (`ae_ae_forall_pos_unitSquareClock`, with the strictly
increasing planar clock of Proposition 2.5, `exists_ae_forall_isLQGClock_isTimeChangeClock`), the
absence of atoms and the full support of the normalized LQG measure, and the strongly continuous
symmetric sub-Markov semigroup (`isSymmetricMarkovSemigroup_heatKernelL2Semigroup`).
-/

open MeasureTheory ProbabilityTheory Set Filter Topology MarkovProcess Metric
open scoped ENNReal NNReal

universe u

namespace HarmonicBalls

/-- **The normalized LQG measure has no atoms in the unit square**, almost surely for every
square, by the upper volume bound of Kigami's condition (13.1). -/
theorem ae_forall_closedSquare_unitSquareNormalizedMeasure_singleton_eq_zero {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ (a : ℂ) (L : ℝ), 0 < L → ∀ x ∈ closedSquare 0 1,
      unitSquareNormalizedMeasure (μ ω) a L {x} = 0 := by
  filter_upwards [ae_forall_closedSquare_kigamiVolumeBounds hγ hγ2 hα hh hμ] with ω hω
  intro a L hL x hx
  obtain ⟨-, -, c₁, c₂, α₁, α₂, -, -, -, hα₂, -, hb⟩ := hω a L hL
  have hc : ContinuousAt (fun r : ℝ => c₂ * r ^ α₂) 0 :=
    continuousAt_const.mul (Real.continuousAt_rpow_const 0 α₂ (Or.inr hα₂.le))
  have hlim : Tendsto (fun r : ℝ => ENNReal.ofReal (c₂ * r ^ α₂)) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun r : ℝ => ENNReal.ofReal (c₂ * r ^ α₂)) (𝓝[>] 0)
        (𝓝 (ENNReal.ofReal (c₂ * 0 ^ α₂))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp (hc.tendsto.mono_left nhdsWithin_le_nhds)
    rwa [Real.zero_rpow hα₂.ne', mul_zero, ENNReal.ofReal_zero] at h
  refine le_antisymm (ge_of_tendsto hlim ?_) zero_le
  filter_upwards [Ioo_mem_nhdsGT one_pos] with r hr
  exact (measure_mono (singleton_subset_iff.2 (mem_ball_self hr.1))).trans
    (hb x hx r hr.1 hr.2.le).2

/-- Ball bounds `ν(B(x, r)) ≤ c₂ r^{α₂}` for `r ≤ 1` give closed-ball bounds at every radius for a
probability measure. -/
theorem closedBall_le_of_ball_le {ν : Measure ℂ} [IsProbabilityMeasure ν] {c₂ α₂ : ℝ}
    (hc₂ : 0 < c₂) (hα₂ : 0 < α₂)
    (hb : ∀ x ∈ closedSquare 0 1, ∀ r : ℝ, 0 < r → r ≤ 1 →
      ν (ball x r) ≤ ENNReal.ofReal (c₂ * r ^ α₂)) :
    ∀ y ∈ closedSquare 0 1, ∀ ρ : ℝ, 0 < ρ →
      ν (closedBall y ρ) ≤ ENNReal.ofReal ((c₂ + 1) * 2 ^ α₂ * ρ ^ α₂) := by
  intro y hy ρ hρ
  have hpow : (2 * ρ) ^ α₂ = 2 ^ α₂ * ρ ^ α₂ := Real.mul_rpow (by norm_num) hρ.le
  have hX : 0 < 2 ^ α₂ * ρ ^ α₂ :=
    mul_pos (Real.rpow_pos_of_pos two_pos α₂) (Real.rpow_pos_of_pos hρ α₂)
  by_cases h2 : 2 * ρ ≤ 1
  · calc ν (closedBall y ρ) ≤ ν (ball y (2 * ρ)) :=
          measure_mono (closedBall_subset_ball (by linarith))
      _ ≤ ENNReal.ofReal (c₂ * (2 * ρ) ^ α₂) := hb y hy _ (by positivity) h2
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hpow]
          nlinarith
  · calc ν (closedBall y ρ) ≤ 1 := prob_le_one
      _ ≤ _ := by
          rw [← ENNReal.ofReal_one]
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : 1 ≤ (2 * ρ) ^ α₂ := Real.one_le_rpow (by linarith) hα₂.le
          rw [hpow] at h1
          nlinarith

/-- The closed-ball bounds of `closedBall_le_of_ball_le` in the form of `IsUpperRegularSpeed`. -/
theorem exists_closedBall_le_of_ball_le {ν : Measure ℂ} [IsProbabilityMeasure ν] {c₂ α₂ : ℝ}
    (hc₂ : 0 < c₂) (hα₂ : 0 < α₂)
    (hb : ∀ x ∈ closedSquare (0 : ℂ) 1, ∀ r : ℝ, 0 < r → r ≤ 1 →
      ν (ball x r) ≤ ENNReal.ofReal (c₂ * r ^ α₂)) :
    ∃ C β : ℝ, 0 ≤ C ∧ 0 < β ∧ ∀ y ∈ closedSquare (0 : ℂ) 1, ∀ r : ℝ, 0 < r →
      ν (closedBall y r) ≤ ENNReal.ofReal (C * r ^ β) :=
  ⟨(c₂ + 1) * 2 ^ α₂, α₂, by positivity, hα₂, closedBall_le_of_ball_le hc₂ hα₂ hb⟩

/-- **Proposition 2.6 from the instance of the cited theorem of Kigami (`KigamiLQGInstanceStmt`), the
clock identification and positivity for the clock
of the square.** As `reflectedLBMHeatKernel_of_identification`, with positivity required only for
the additive functionals `A` that give the clock `F` after scaling. -/
theorem reflectedLBMHeatKernel_of_identification_of_clockPositivity
    (hKig : KigamiLQGInstanceStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {a : ℂ} {L : ℝ} (hL : 0 < L) (F : Ω → ℂ → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (hid : ∀ᵐ ω ∂P, ∃ A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0, IsUnitSquarePCAF A ∧
      unitSquareRevuzMeasure A = unitSquareNormalizedMeasure (μ ω) a L ∧
      ∀ x ∈ closedSquare a L, ∀ᵐ b ∂(reflectedPlanarBrownianMotion a L x), ∀ s : ℝ≥0,
        F ω x b s = (μ ω (closedSquare a L)).toReal *
          (A (s / (L ^ 2).toNNReal) (unitSquarePathChart a hL b) : ℝ))
    (hpos : ∀ᵐ ω ∂P, ∀ (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (p' : ℝ → ℂ → ℂ → ℝ),
      IsUnitSquarePCAF A → unitSquareRevuzMeasure A = unitSquareNormalizedMeasure (μ ω) a L →
      (∀ x ∈ closedSquare a L, ∀ᵐ b ∂(reflectedPlanarBrownianMotion a L x), ∀ s : ℝ≥0,
        F ω x b s = (μ ω (closedSquare a L)).toReal *
          (A (s / (L ^ 2).toNNReal) (unitSquarePathChart a hL b) : ℝ)) →
      IsLBMHeatKernel (reflectedPlanarBrownianMotion 0 1) (fun _ b t => (A t b : ℝ))
        (closedSquare 0 1) (unitSquareNormalizedMeasure (μ ω) a L) p' →
      ContinuousOn (fun s : ℝ × ℂ × ℂ => p' s.1 s.2.1 s.2.2)
        (Ioi 0 ×ˢ closedSquare 0 1 ×ˢ closedSquare 0 1) →
      ∀ t : ℝ, 0 < t → ∀ x ∈ closedSquare 0 1, ∀ y ∈ closedSquare 0 1, 0 < p' t x y) :
    ∀ᵐ ω ∂P, ∃ p : ℝ → ℂ → ℂ → ℝ,
      IsLBMHeatKernel (reflectedPlanarBrownianMotion a L) (F ω) (closedSquare a L) (μ ω) p ∧
      ContinuousOn (fun s : ℝ × ℂ × ℂ => p s.1 s.2.1 s.2.2)
        (Ioi 0 ×ˢ closedSquare a L ×ˢ closedSquare a L) ∧
      ∀ t : ℝ, 0 < t → ∀ x ∈ closedSquare a L, ∀ y ∈ closedSquare a L, 0 < p t x y := by
  filter_upwards [hKig γ α₀ hγ hγ2 hα Ω P hC hcirc μ hh hμ,
    ae_forall_closedSquare_volume_bounds hγ hγ2 hα hh hμ, hid, hpos] with ω hker hvol hidω hposω
  obtain ⟨A, hA, hRev, hFA⟩ := hidω
  obtain ⟨p', hp', hcont'⟩ := hker a L hL A hA hRev
  obtain ⟨hKpos, hKfin, -⟩ := hvol a L hL
  have hM : 0 < (μ ω (closedSquare a L)).toReal := ENNReal.toReal_pos hKpos.ne' hKfin.ne
  refine ⟨_, isLBMHeatKernel_of_unitSquare hL hKpos hKfin (F' := fun _ b t => (A t b : ℝ)) hp' hFA,
    continuousOn_scaled_kernel hL hM hcont', fun t ht x hx y hy =>
      scaled_kernel_pos hL hM (hposω A p' hA hRev hFA hp' hcont') ht hx hy⟩

/-- **Proposition 2.6 from the instances of the cited theorems of Kigami and of
Keller–Lenz–Vogt–Wojciechowski (`KigamiLQGInstanceStmt`, `KLVWHeatKernelInstanceStmt`), the
symmetry of the unit-square kernel and the irreducibility of its transition semigroup.** Let `F ω x`
be LQG clocks of reflected Brownian motion in `K = closedSquare a L` from every `x ∈ K`, and let
`A` range over the additive functionals of reflected Brownian motion in `K₀` with Revuz measure the
normalized `μ_h` that give `F` after scaling, and `p'` over the jointly continuous heat kernels of
their time changes. If almost surely every such `p'` is symmetric (`hsymm`) and has an irreducible
transition semigroup on `L²(ν)` (`hirr`), then almost surely the reflected Liouville Brownian
motion in `K` has a heat kernel with respect to `μ_h` that is jointly continuous and strictly
positive on `(0, ∞) × K × K`. -/
theorem reflectedLBMHeatKernel_of_kigami_of_klvw (hKig : KigamiLQGInstanceStmt.{u})
    (hKLVW : KLVWHeatKernelInstanceStmt)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {a : ℂ} {L : ℝ} (hL : 0 < L) (F : Ω → ℂ → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (hF : ∀ᵐ ω ∂P, ∀ x ∈ closedSquare a L,
      IsLQGClock (reflectedPlanarBrownianMotion a L) γ (fieldCircleAverage α₀ (hcirc ω)) x
        (F ω x))
    (hsymm : ∀ᵐ ω ∂P, ∀ (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (p' : ℝ → ℂ → ℂ → ℝ),
      IsUnitSquarePCAF A → unitSquareRevuzMeasure A = unitSquareNormalizedMeasure (μ ω) a L →
      (∀ x ∈ closedSquare a L, ∀ᵐ b ∂(reflectedPlanarBrownianMotion a L x), ∀ s : ℝ≥0,
        F ω x b s = (μ ω (closedSquare a L)).toReal *
          (A (s / (L ^ 2).toNNReal) (unitSquarePathChart a hL b) : ℝ)) →
      IsLBMHeatKernel (reflectedPlanarBrownianMotion 0 1) (fun _ b t => (A t b : ℝ))
        (closedSquare 0 1) (unitSquareNormalizedMeasure (μ ω) a L) p' →
      ContinuousOn (fun s : ℝ × ℂ × ℂ => p' s.1 s.2.1 s.2.2)
        (Ioi 0 ×ˢ closedSquare 0 1 ×ˢ closedSquare 0 1) →
      ∀ t : ℝ, 0 < t → ∀ x ∈ closedSquare 0 1, ∀ y ∈ closedSquare 0 1, p' t x y = p' t y x)
    (hirr : ∀ᵐ ω ∂P, ∀ (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (p' : ℝ → ℂ → ℂ → ℝ),
      IsUnitSquarePCAF A → unitSquareRevuzMeasure A = unitSquareNormalizedMeasure (μ ω) a L →
      (∀ x ∈ closedSquare a L, ∀ᵐ b ∂(reflectedPlanarBrownianMotion a L x), ∀ s : ℝ≥0,
        F ω x b s = (μ ω (closedSquare a L)).toReal *
          (A (s / (L ^ 2).toNNReal) (unitSquarePathChart a hL b) : ℝ)) →
      IsLBMHeatKernel (reflectedPlanarBrownianMotion 0 1) (fun _ b t => (A t b : ℝ))
        (closedSquare 0 1) (unitSquareNormalizedMeasure (μ ω) a L) p' →
      ContinuousOn (fun s : ℝ × ℂ × ℂ => p' s.1 s.2.1 s.2.2)
        (Ioi 0 ×ˢ closedSquare 0 1 ×ˢ closedSquare 0 1) →
      ∀ [IsFiniteMeasure (unitSquareNormalizedMeasure (μ ω) a L)],
        IsIrreducibleSemigroup (unitSquareNormalizedMeasure (μ ω) a L)
          (heatKernelL2Semigroup (unitSquareNormalizedMeasure (μ ω) a L) p')) :
    ∀ᵐ ω ∂P, ∃ p : ℝ → ℂ → ℂ → ℝ,
      IsLBMHeatKernel (reflectedPlanarBrownianMotion a L) (F ω) (closedSquare a L) (μ ω) p ∧
      ContinuousOn (fun s : ℝ × ℂ × ℂ => p s.1 s.2.1 s.2.2)
        (Ioi 0 ×ˢ closedSquare a L ×ˢ closedSquare a L) ∧
      ∀ t : ℝ, 0 < t → ∀ x ∈ closedSquare a L, ∀ y ∈ closedSquare a L, 0 < p t x y := by
  obtain ⟨G, hG⟩ := exists_ae_forall_isLQGClock_isTimeChangeClock hh hγ hγ2 hα hμ
  refine reflectedLBMHeatKernel_of_identification_of_clockPositivity hKig hγ hγ2 hα hh hμ hL F
    (ae_exists_isUnitSquarePCAF_revuz_eq hh hγ hγ2 hα hμ a hL hF) ?_
  filter_upwards [hsymm, hirr, hG, hF, ae_forall_closedSquare_kigamiVolumeBounds hγ hγ2 hα hh hμ,
    ae_forall_closedSquare_unitSquareNormalizedMeasure_ball_inter_pos hγ hγ2 hα hh hμ,
    ae_forall_closedSquare_unitSquareNormalizedMeasure_singleton_eq_zero hγ hγ2 hα hh hμ,
    hh.ae_lqgMeasure_frontier_closedSquare_eq_zero_of_pos hγ hγ2 hα hμ a hL,
    ae_forall_closedSquare_volume_bounds hγ hγ2 hα hh hμ]
    with ω hsω hiω hGω hFω hkig hball hatom hfr hvol
  intro A p' hA hRev hFA hp' hpc t ht x hx y hy
  obtain ⟨hprob, hcarried, c₁, c₂, α₁, α₂, -, hc₂, -, hα₂, -, hb⟩ := hkig a L hL
  have := hprob
  have hup := exists_closedBall_le_of_ball_le hc₂ hα₂ fun x hx r hr hr1 => (hb x hx r hr hr1).2
  obtain ⟨hKpos, hKfin, -⟩ := hvol a L hL
  have hM : 0 < (μ ω (closedSquare a L)).toReal := ENNReal.toReal_pos hKpos.ne' hKfin.ne
  have hstart := ae_ae_forall_pos_unitSquareClock hL hM hA hfr hFω hFA
    (fun x => (hGω.1 x).1) (fun x => (hGω.1 x).2)
  exact pos_of_isIrreducibleSemigroup hKLVW hA hRev hprob hup hcarried (hball a L hL) (hatom a L hL)
    hp' hpc
    (hsω A p' hA hRev hFA hp' hpc) hstart (hiω A p' hA hRev hFA hp' hpc) ht hx hy

end HarmonicBalls
