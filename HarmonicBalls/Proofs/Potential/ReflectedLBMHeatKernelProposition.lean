import HarmonicBalls.Proofs.Potential.ReflectedHeatKernelSymmetry
import HarmonicBalls.Proofs.Potential.ReflectedHeatKernelIrreducible
import HarmonicBalls.Proofs.Potential.ReflectedLQGHeatKernelPositivity

/-!
# Proposition 2.6 from the cited theorems of Kigami and of Keller–Lenz–Vogt–Wojciechowski

Proposition 2.6 (prop:lbm-continuity, paper/lqg_harmonic_ball-corrected.tex:560) holds
(`reflectedLBMHeatKernelStmt_of_kigami_of_klvw`) given the cited statements
`kigamiHeatKernelContinuityCited` (Kigami 2019, Theorem 13.1) and `klvwPositivityImprovingCited`
(Keller–Lenz–Vogt–Wojciechowski 2015, Definition A.1 and Theorem A.2). The two hypotheses of
`reflectedLBMHeatKernel_of_kigami_of_klvw` on the unit-square kernel `p'` of the clock of the
square are discharged:

* **symmetry** `p'(t, x, y) = p'(t, y, x)` (`isLBMHeatKernel_symm`): from the occupation identity
  of the clock from every start, the symmetric Green kernel of the square, the resolvent identity
  of the time change and uniqueness of the Laplace transform; its inputs are the volume bounds
  (13.1) of the normalized LQG measure (`ae_forall_closedSquare_kigamiVolumeBounds`), which give
  the closed-ball bounds used for the potential of the clock (`closedBall_le_of_ball_le`), its
  full support and the absence of atoms;
* **irreducibility** of the transition semigroup on `L²(ν)`
  (`isIrreducibleSemigroup_heatKernelL2Semigroup`), from the symmetry.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology MarkovProcess Metric
open scoped ENNReal NNReal

universe u

namespace HarmonicBalls

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

/-- **Symmetry of the unit-square kernel** of a clock whose Revuz measure is a probability measure
carried by `K₀`, without atoms, with full support in `K₀` and the upper bounds of (13.1). -/
theorem isLBMHeatKernel_symm_of_volume_bounds {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A) {ν : Measure ℂ} [IsProbabilityMeasure ν]
    (hRev : unitSquareRevuzMeasure A = ν) (hνK : ν (closedSquare 0 1)ᶜ = 0)
    (hatom : ∀ y ∈ closedSquare 0 1, ν {y} = 0)
    (hsupp : ∀ y ∈ closedSquare 0 1, ∀ r : ℝ, 0 < r → 0 < ν (ball y r ∩ closedSquare 0 1))
    {c₂ α₂ : ℝ} (hc₂ : 0 < c₂) (hα₂ : 0 < α₂)
    (hb : ∀ x ∈ closedSquare 0 1, ∀ r : ℝ, 0 < r → r ≤ 1 →
      ν (ball x r) ≤ ENNReal.ofReal (c₂ * r ^ α₂))
    {p : ℝ → ℂ → ℂ → ℝ}
    (hp : IsLBMHeatKernel (reflectedPlanarBrownianMotion 0 1) (fun _ b t => (A t b : ℝ))
      (closedSquare 0 1) ν p)
    (hpc : ContinuousOn (fun s : ℝ × ℂ × ℂ => p s.1 s.2.1 s.2.2)
      (Ioi 0 ×ˢ closedSquare 0 1 ×ˢ closedSquare 0 1)) :
    ∀ t : ℝ, 0 < t → ∀ x ∈ closedSquare 0 1, ∀ y ∈ closedSquare 0 1, p t x y = p t y x := by
  subst hRev
  intro t ht x hx y hy
  exact isLBMHeatKernel_symm hA hνK hatom hsupp zero_le_one (by positivity) hα₂ (by simp)
    (closedBall_le_of_ball_le hc₂ hα₂ hb) hp hpc ht hx hy

/-- **Proposition 2.6** (prop:lbm-continuity) from the instances of the cited theorems of Kigami
(2019, Theorem 13.1) and of Keller–Lenz–Vogt–Wojciechowski (2015, Theorem A.2) that its proof uses
(`KigamiLQGInstanceStmt`, `KLVWHeatKernelInstanceStmt`). -/
theorem reflectedLBMHeatKernelStmt_of_instances (hKig : KigamiLQGInstanceStmt.{u})
    (hKLVW : KLVWHeatKernelInstanceStmt) : ReflectedLBMHeatKernelStmt.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hh hμ a L hL F hF
  have hvb := ae_forall_closedSquare_kigamiVolumeBounds hγ hγ2 hα hh hμ
  have hpos := ae_forall_closedSquare_unitSquareNormalizedMeasure_ball_inter_pos hγ hγ2 hα hh hμ
  have hat := ae_forall_closedSquare_unitSquareNormalizedMeasure_singleton_eq_zero hγ hγ2 hα hh hμ
  have hsymm : ∀ᵐ ω ∂P, ∀ (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (p' : ℝ → ℂ → ℂ → ℝ),
      IsUnitSquarePCAF A → unitSquareRevuzMeasure A = unitSquareNormalizedMeasure (μ ω) a L →
      (∀ x ∈ closedSquare a L, ∀ᵐ b ∂(reflectedPlanarBrownianMotion a L x), ∀ s : ℝ≥0,
        F ω x b s = (μ ω (closedSquare a L)).toReal *
          (A (s / (L ^ 2).toNNReal) (unitSquarePathChart a hL b) : ℝ)) →
      IsLBMHeatKernel (reflectedPlanarBrownianMotion 0 1) (fun _ b t => (A t b : ℝ))
        (closedSquare 0 1) (unitSquareNormalizedMeasure (μ ω) a L) p' →
      ContinuousOn (fun s : ℝ × ℂ × ℂ => p' s.1 s.2.1 s.2.2)
        (Ioi 0 ×ˢ closedSquare 0 1 ×ˢ closedSquare 0 1) →
      ∀ t : ℝ, 0 < t → ∀ x ∈ closedSquare 0 1, ∀ y ∈ closedSquare 0 1, p' t x y = p' t y x := by
    filter_upwards [hvb, hpos, hat] with ω hω hpω haω
    intro A p' hA hRev _ hp' hpc
    obtain ⟨hprob, hcarried, c₁, c₂, α₁, α₂, -, hc₂, -, hα₂, -, hb⟩ := hω a L hL
    exact isLBMHeatKernel_symm_of_volume_bounds hA hRev hcarried (haω a L hL) (hpω a L hL) hc₂
      hα₂ (fun x hx r hr hr1 => (hb x hx r hr hr1).2) hp' hpc
  refine reflectedLBMHeatKernel_of_kigami_of_klvw hKig hKLVW hγ hγ2 hα hh hμ hL F hF hsymm ?_
  filter_upwards [hsymm, hvb, hpos, hat] with ω hsω hω hpω haω
  intro A p' hA hRev hFA hp' hpc _
  obtain ⟨-, hcarried, -⟩ := hω a L hL
  exact isIrreducibleSemigroup_heatKernelL2Semigroup hA hcarried (hpω a L hL) (haω a L hL) hp' hpc
    (hsω A p' hA hRev hFA hp' hpc)

/-- **Proposition 2.6** (prop:lbm-continuity) from the cited theorems of Kigami (2019,
Theorem 13.1) and of Keller–Lenz–Vogt–Wojciechowski (2015, Theorem A.2). -/
theorem reflectedLBMHeatKernelStmt_of_kigami_of_klvw (hKig : kigamiHeatKernelContinuityCited)
    (hKLVW : klvwPositivityImprovingCited) : ReflectedLBMHeatKernelStmt.{u} :=
  reflectedLBMHeatKernelStmt_of_instances (kigamiLQGInstanceStmt_of_cited hKig)
    (klvwHeatKernelInstanceStmt_of_cited hKLVW)

end HarmonicBalls
