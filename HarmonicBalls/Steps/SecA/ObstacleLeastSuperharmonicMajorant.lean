import HarmonicBalls.Steps.SecA.Basic

/-!
# Lemma A.1 (lemma:appendix-basic-properties, line 3589): carving of the proof

`ObstacleLeastSuperharmonicMajorantStmt` (Draft/SectionA.lean): for `t > 0` the least superharmonic majorant
`ṽ_t` is finite, continuous on the closed ball and an element of `S̃(t)`. The printed proof (lines 3593-3648)
works with the infimum `f_t` of the *lower semicontinuous* superharmonic majorants (eq:lsc-leastsuperharmonic,
line 3594), `lscLeastMajorant` below, over the class `superharmonicMajorants`. Everything is stated for a general
radius `R > 0` and pole `z ∈ B_R` (the paper's case is `R = 1`, `z = 0`, line 3547; Lemma A.6 needs general `R`,
Section 3 needs general `z`): `ObstacleLeastSuperharmonicMajorantGeneral`.

## Steps (difficulty in brackets)

* `ObstacleLeastSuperharmonicMajorantStep1` — Step 1 (finiteness, lines 3602-3604): every superharmonic majorant
  `g ≥ β_t` is `≥ 0` on the closed ball (minimum principle; `β_t → 0` at `∂B_R`). [medium, 1-2 rounds]
* `ObstacleLeastSuperharmonicMajorantStep2` — Step 2 (lines 3606-3620): `f_t` is superharmonic on `B_R`
  (AG01 Thm 3.7.5 on the lower semicontinuous regularization `f̂_t`, and `f̂_t ≥ β_t` gives `f̂_t = f_t`).
  [hard, 2-3 rounds]
* `ObstacleLeastSuperharmonicMajorantStep3` — Step 3 off the pole (lines 3622-3647): `f_t` is upper
  semicontinuous at every `x₀ ∈ B_R \ {z}` (Poisson modification of `ε + f_t` on a small disc).
  [hard, 2-3 rounds]
* `ObstacleLeastSuperharmonicMajorantStep4` — **gap G2**, Step 3 at the pole: the printed choice of `δ`
  (lines 3626-3628, "`β_t(x) + ε/2 ≥ β_t(y)` on `B_δ(x₀)`") is impossible at `x₀ = z`, where `β_t(z) = -∞`.
  Repair: on a small disc `B_δ(z)`, `β_t < 0 ≤ f_t` (Step 1, `ObstacleTendstoAtBotStep`), so the Poisson
  modification of `ε + f_t` on `B_δ(z)` is still admissible; then conclude as in Step 3. [medium, 1-2 rounds,
  shares the Poisson modification with Step 3]

Shared steps used by the reduction (Basic.lean): `SuperharmonicOfLaplacianLEStep`,
`LaplacianLEOfSuperharmonicStep`, `GreenPotentialBallContinuousStep`, `GreenPotentialBallLaplacianStep`.

## The reduction (proved)

`obstacleLeastSuperharmonicMajorantGeneral_of_steps`: Steps 1-4 and the shared steps give `f_t ∈ S̃(t)` and
`S̃(t) ⊆ superharmonicMajorants`, hence `ṽ_t = f_t` on the closed ball (the printed "by definition `f_t ≤ ṽ_t` and
the reverse inequality follows from `f_t ∈ S̃(t)`", lines 3599-3600). A small point the printed Step 3 leaves out
(it treats `x₀ ∈ B_1` only): continuity at points of `∂B_R` follows from `0 ≤ f_t ≤ q_{B_R}` and
`q_{B_R} = 0` on `∂B_R`; it is proved in the reduction.
-/

namespace HarmonicBalls

open MeasureTheory Metric Filter Topology Set

/-- The admissible class of eq:lsc-leastsuperharmonic (line 3594): functions `g` superharmonic on `B_R` in the
classical sense (lower semicontinuous, `IsSuperharmonicOn`) with `g ≥ β_t` on the closed ball off the pole. -/
def superharmonicMajorants (μ : Measure ℂ) (R : ℝ) (z : ℂ) (t : ℝ) : Set (ℂ → ℝ) :=
  {g | IsSuperharmonicOn (ball 0 R) g ∧ ∀ x ∈ closedBall (0 : ℂ) R, x ≠ z → obstacle μ R z t x ≤ g x}

/-- The infimum `f_t` of eq:lsc-leastsuperharmonic (line 3594): the pointwise infimum of
`superharmonicMajorants μ R z t`. Junk value `0` of `sInf` where the values are not bounded below. -/
noncomputable def lscLeastMajorant (μ : Measure ℂ) (R : ℝ) (z : ℂ) (t : ℝ) (x : ℂ) : ℝ :=
  sInf ((fun g : ℂ → ℝ => g x) '' superharmonicMajorants μ R z t)

/-- Lemma A.1 for a general radius `R > 0` and pole `z ∈ B_R` (the paper's case is `R = 1`, `z = 0`, line 3547),
with two by-products of the proof: `ṽ_t ≥ 0` on the closed ball (Step 1) and `ṽ_t = f_t` there (line 3600). -/
def ObstacleLeastSuperharmonicMajorantGeneral : Prop :=
  ∀ μ : Measure ℂ, IsLocallyFiniteMeasure μ → ∀ R βminus βplus : ℝ, 0 < R → VolumeGrowth μ R βminus βplus →
  ∀ z ∈ ball (0 : ℂ) R, ∀ t : ℝ, 0 < t →
    (∀ x ∈ closedBall (0 : ℂ) R, BddBelow ((fun w : ℂ → ℝ => w x) '' shiftedSupersolutions μ R z t)) ∧
    ContinuousOn (shiftedLeastSupersolution μ R z t) (closedBall 0 R) ∧
    shiftedLeastSupersolution μ R z t ∈ shiftedSupersolutions μ R z t ∧
    (∀ x ∈ closedBall (0 : ℂ) R, 0 ≤ shiftedLeastSupersolution μ R z t x) ∧
    EqOn (shiftedLeastSupersolution μ R z t) (lscLeastMajorant μ R z t) (closedBall 0 R)

/-! ## Steps -/

/-- **Lemma A.1, Step 1 (finiteness, lines 3602-3604).** Every lower semicontinuous superharmonic majorant
`g ≥ β_t` (eq:lsc-leastsuperharmonic) is nonnegative on the closed ball. Printed argument: the minimum principle,
"as `g ≥ β_t = 0` on `∂B_1`". In the classical class the boundary values of `g` on `∂B_R` do not control `g`
inside; the minimum principle is applied with `liminf_{y → ξ} g(y) ≥ lim_{y → ξ} β_t(y) = 0` at `ξ ∈ ∂B_R`
(continuity of `q_{B_R}`, `GreenPotentialBallContinuousStep`, and the zero boundary values of `G_{B_R}(z, ·)`,
Prop 2.3), and on `∂B_R` itself `g ≥ β_t = 0`. Uses: the minimum principle for `IsSuperharmonicOn` on bounded
open sets (AG01, Chapter 3), `GreenPotentialBallContinuousStep`, Prop 2.3. Difficulty: medium (1-2 rounds). -/
def ObstacleLeastSuperharmonicMajorantStep1 : Prop :=
  ∀ μ : Measure ℂ, IsLocallyFiniteMeasure μ → ∀ R βminus βplus : ℝ, 0 < R → VolumeGrowth μ R βminus βplus →
  ∀ z ∈ ball (0 : ℂ) R, ∀ t : ℝ, 0 < t →
    ∀ g ∈ superharmonicMajorants μ R z t, ∀ x ∈ closedBall (0 : ℂ) R, 0 ≤ g x

/-- **Lemma A.1, Step 2 (superharmonicity, lines 3606-3620).** The infimum `f_t` of the lower semicontinuous
superharmonic majorants is superharmonic on `B_R`. Printed argument: by AG01 Thm 3.7.5 (recalled at lines
3608-3614) the lower semicontinuous regularization `f̂_t(x) = min {f_t(x), liminf_{y → x} f_t(y)}` of the
infimum of a family of superharmonic functions bounded below (Step 1: `f_t ≥ 0`; `f_t ≤ q_{B_R}`) is
superharmonic; since `β_t` is continuous off the pole, `f̂_t ≥ β_t`, so `f̂_t` (extended by `f_t` on `∂B_R`) is
admissible and `f_t ≤ f̂_t ≤ f_t`. Uses: Step 1, `GreenPotentialBallContinuousStep`, Prop 2.3 (continuity of
`G_{B_R}(z, ·)` off the pole), AG01 Thm 3.7.5 (to be proved for `IsSuperharmonicOn`). Difficulty: hard
(2-3 rounds). -/
def ObstacleLeastSuperharmonicMajorantStep2 : Prop :=
  ∀ μ : Measure ℂ, IsLocallyFiniteMeasure μ → ∀ R βminus βplus : ℝ, 0 < R → VolumeGrowth μ R βminus βplus →
  ∀ z ∈ ball (0 : ℂ) R, ∀ t : ℝ, 0 < t →
    IsSuperharmonicOn (ball 0 R) (lscLeastMajorant μ R z t)

/-- **Lemma A.1, Step 3 off the pole (lines 3622-3647).** `f_t` is upper semicontinuous at every
`x₀ ∈ B_R \ {z}`. Printed argument: for `ε > 0` choose `δ` with `closedBall x₀ δ ⊆ B_R \ {z}` and
`β_t(x) + ε/2 ≥ β_t(y)` on `B_δ(x₀)` (continuity of `β_t` at `x₀ ≠ z`), so `ε + f_t ≥ β_t(x₀) + ε/2 ≥ β_t` there
(eq:lower-bound-continuity); the Poisson modification `g` of `ε + f_t` on `B_δ(x₀)` (harmonic in the disc, equal
to `ε + f_t` outside, `g ≤ ε + f_t` by eq:superharmonic-poisson-inequality) is superharmonic on `B_R` and
`≥ β_t`, hence `g ≥ f_t`, and `limsup_{x → x₀} f_t(x) ≤ g(x₀) ≤ ε + f_t(x₀)`. Uses: Step 2, the Poisson
modification of a lower semicontinuous superharmonic function on a disc (Poisson integral of a lower
semicontinuous boundary function; Mathlib `Mathlib/Analysis/Complex/Harmonic/Poisson.lean` for the Poisson
integral).
Difficulty: hard (2-3 rounds). -/
def ObstacleLeastSuperharmonicMajorantStep3 : Prop :=
  ∀ μ : Measure ℂ, IsLocallyFiniteMeasure μ → ∀ R βminus βplus : ℝ, 0 < R → VolumeGrowth μ R βminus βplus →
  ∀ z ∈ ball (0 : ℂ) R, ∀ t : ℝ, 0 < t →
    ∀ x₀ ∈ ball (0 : ℂ) R, x₀ ≠ z → UpperSemicontinuousAt (lscLeastMajorant μ R z t) x₀

/-- **Lemma A.1, Step 3 at the pole (gap G2, GRAPH.md).** `f_t` is upper semicontinuous at the pole `z`. The
printed choice of `δ` (lines 3626-3628) is impossible at `x₀ = z`, where `β_t(z) = -∞`
(`β_t(x) + ε/2 ≥ β_t(y)` fails for `x` close to `z`). Repair: choose `δ` with `closedBall z δ ⊆ B_R` and
`β_t < 0` on `B_δ(z) \ {z}` (`ObstacleTendstoAtBotStep`; `β_t ≤ sup q_{B_R} + (t/2π) log (δ/r)` there); by Step 1,
`ε + f_t ≥ ε > 0` on `∂B_δ(z)`, so the Poisson modification `g` of `ε + f_t` on `B_δ(z)` satisfies `g ≥ ε > β_t`
on `B_δ(z)` and is admissible; conclude as in Step 3. Uses: Steps 1-2, `ObstacleTendstoAtBotStep`,
`GreenPotentialBallContinuousStep`, the Poisson modification of Step 3. Difficulty: medium (1-2 rounds, given the
Poisson modification of Step 3). -/
def ObstacleLeastSuperharmonicMajorantStep4 : Prop :=
  ∀ μ : Measure ℂ, IsLocallyFiniteMeasure μ → ∀ R βminus βplus : ℝ, 0 < R → VolumeGrowth μ R βminus βplus →
  ∀ z ∈ ball (0 : ℂ) R, ∀ t : ℝ, 0 < t →
    UpperSemicontinuousAt (lscLeastMajorant μ R z t) z

/-! ## The reduction -/

/-- **Lemma A.1, general radius and pole, from its steps.** -/
theorem obstacleLeastSuperharmonicMajorantGeneral_of_steps
    (hW : SuperharmonicOfLaplacianLEStep) (hW' : LaplacianLEOfSuperharmonicStep)
    (hq : GreenPotentialBallContinuousStep) (hΔq : GreenPotentialBallLaplacianStep)
    (h1 : ObstacleLeastSuperharmonicMajorantStep1) (h2 : ObstacleLeastSuperharmonicMajorantStep2)
    (h3 : ObstacleLeastSuperharmonicMajorantStep3) (h4 : ObstacleLeastSuperharmonicMajorantStep4) :
    ObstacleLeastSuperharmonicMajorantGeneral := by
  intro μ hμ R βm βp hR hV z hz t ht
  have hqc : ContinuousOn (greenPotentialBall μ R) (closedBall 0 R) := hq μ hμ R βm βp hR hV
  have hqLE : LaplacianLE (greenPotentialBall μ R) 0 (ball 0 R) := (hΔq μ hμ R βm βp hR hV).laplacianLE
  have hbs : ball (0 : ℂ) R ⊆ closedBall 0 R := ball_subset_closedBall
  have hSA : shiftedSupersolutions μ R z t ⊆ superharmonicMajorants μ R z t := fun w hw =>
    ⟨hW _ w isOpen_ball (hw.1.mono hbs) hw.2.1, hw.2.2⟩
  have hqS : greenPotentialBall μ R ∈ shiftedSupersolutions μ R z t :=
    greenPotentialBall_mem_shiftedSupersolutions ht.le hqc hqLE
  have hqA := hSA hqS
  have hg0 := h1 μ hμ R βm βp hR hV z hz t ht
  have hbdd : ∀ x ∈ closedBall (0 : ℂ) R,
      BddBelow ((fun g : ℂ → ℝ => g x) '' superharmonicMajorants μ R z t) := fun x hx =>
    ⟨0, by rintro _ ⟨g, hg, rfl⟩; exact hg0 g hg x hx⟩
  have hne : ∀ x, ((fun g : ℂ → ℝ => g x) '' superharmonicMajorants μ R z t).Nonempty := fun x =>
    ⟨_, _, hqA, rfl⟩
  have hf_le : ∀ g ∈ superharmonicMajorants μ R z t, ∀ x ∈ closedBall (0 : ℂ) R,
      lscLeastMajorant μ R z t x ≤ g x := fun g hg x hx => csInf_le (hbdd x hx) ⟨g, hg, rfl⟩
  have hf_nonneg : ∀ x ∈ closedBall (0 : ℂ) R, 0 ≤ lscLeastMajorant μ R z t x := fun x hx =>
    le_csInf (hne x) (by rintro _ ⟨g, hg, rfl⟩; exact hg0 g hg x hx)
  have hf_obs : ∀ x ∈ closedBall (0 : ℂ) R, x ≠ z → obstacle μ R z t x ≤ lscLeastMajorant μ R z t x :=
    fun x hx hxz => le_csInf (hne x) (by rintro _ ⟨g, hg, rfl⟩; exact hg.2 x hx hxz)
  have hf2 := h2 μ hμ R βm βp hR hV z hz t ht
  have hfc : ContinuousOn (lscLeastMajorant μ R z t) (closedBall 0 R) := by
    intro x hx
    by_cases hxb : x ∈ ball (0 : ℂ) R
    · have hlsc : LowerSemicontinuousAt (lscLeastMajorant μ R z t) x :=
        fun y hy => by
          have := hf2.1 x hxb y hy
          rwa [nhdsWithin_eq_nhds.2 (isOpen_ball.mem_nhds hxb)] at this
      have husc : UpperSemicontinuousAt (lscLeastMajorant μ R z t) x := by
        by_cases hxz : x = z
        · subst hxz; exact h4 μ hμ R βm βp hR hV x hz t ht
        · exact h3 μ hμ R βm βp hR hV z hz t ht x hxb hxz
      exact (continuousAt_iff_lower_upperSemicontinuousAt.2 ⟨hlsc, husc⟩).continuousWithinAt
    · have hqx : greenPotentialBall μ R x = 0 := greenPotentialBall_eq_zero_of_notMem hxb
      have hfx : lscLeastMajorant μ R z t x = 0 :=
        le_antisymm (hqx ▸ hf_le _ hqA x hx) (hf_nonneg x hx)
      have hqt : Tendsto (greenPotentialBall μ R) (𝓝[closedBall 0 R] x) (𝓝 0) := by
        have := hqc x hx
        rwa [ContinuousWithinAt, hqx] at this
      rw [ContinuousWithinAt, hfx]
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hqt ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with y hy using hf_nonneg y hy
      · filter_upwards [self_mem_nhdsWithin] with y hy using hf_le _ hqA y hy
  have hfS : lscLeastMajorant μ R z t ∈ shiftedSupersolutions μ R z t :=
    ⟨hfc, hW' _ _ isOpen_ball (hfc.mono hbs) hf2, hf_obs⟩
  have hS_bdd : ∀ x ∈ closedBall (0 : ℂ) R,
      BddBelow ((fun w : ℂ → ℝ => w x) '' shiftedSupersolutions μ R z t) := fun x hx =>
    (hbdd x hx).mono (image_mono hSA)
  have heq : EqOn (shiftedLeastSupersolution μ R z t) (lscLeastMajorant μ R z t) (closedBall 0 R) := by
    intro x hx
    apply le_antisymm
    · exact csInf_le (hS_bdd x hx) ⟨_, hfS, rfl⟩
    · exact csInf_le_csInf (hbdd x hx) ⟨_, _, hfS, rfl⟩ (image_mono hSA)
  refine ⟨hS_bdd, hfc.congr heq, ⟨hfc.congr heq, ?_, ?_⟩, fun x hx => (heq hx).symm ▸ hf_nonneg x hx, heq⟩
  · exact hfS.2.1.congr_eqOn measurableSet_ball fun x hx => (heq (hbs hx)).symm
  · intro x hx hxz
    rw [heq hx]
    exact hf_obs x hx hxz

/-- The general form of Lemma A.1 gives the printed statement (`R = 1`, `z = 0`). -/
theorem obstacleLeastSuperharmonicMajorant_of_general (h : ObstacleLeastSuperharmonicMajorantGeneral) :
    ObstacleLeastSuperharmonicMajorantStmt := by
  intro μ hμ βm βp hV t ht
  obtain ⟨h1, h2, h3, -, -⟩ := h μ hμ 1 βm βp one_pos hV 0 (mem_ball_self one_pos) t ht
  exact ⟨h1, h2, h3⟩

/-- **Lemma A.1 from its steps.** -/
theorem obstacleLeastSuperharmonicMajorant_of_steps
    (hW : SuperharmonicOfLaplacianLEStep) (hW' : LaplacianLEOfSuperharmonicStep)
    (hq : GreenPotentialBallContinuousStep) (hΔq : GreenPotentialBallLaplacianStep)
    (h1 : ObstacleLeastSuperharmonicMajorantStep1) (h2 : ObstacleLeastSuperharmonicMajorantStep2)
    (h3 : ObstacleLeastSuperharmonicMajorantStep3) (h4 : ObstacleLeastSuperharmonicMajorantStep4) :
    ObstacleLeastSuperharmonicMajorantStmt :=
  obstacleLeastSuperharmonicMajorant_of_general
    (obstacleLeastSuperharmonicMajorantGeneral_of_steps hW hW' hq hΔq h1 h2 h3 h4)

end HarmonicBalls
