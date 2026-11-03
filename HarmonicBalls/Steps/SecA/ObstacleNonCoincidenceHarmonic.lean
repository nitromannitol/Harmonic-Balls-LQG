import HarmonicBalls.Steps.SecA.ObstacleLeastSuperharmonicMajorant

/-!
# Lemma A.2 (lemma:appendix-non-coincedence-open-harmonic, line 3652): carving of the proof

`ObstacleNonCoincidenceHarmonicStmt` (Draft/SectionA.lean): for `t > 0` the non-coincidence set `Λ_t` is open
and connected and `Δ ṽ_t = 0` on `Λ_t`. Printed proof: lines 3656-3725. Stated for a general radius `R > 0` and
pole `z ∈ B_R`: `ObstacleNonCoincidenceHarmonicGeneral`.

## Steps (difficulty in brackets)

* Step 1 (open, lines 3657-3659): proved in the reduction, from the continuity of `ṽ_t` (Lemma A.1) and of `β_t`
  off the pole (Prop 2.3, `GreenPotentialBallContinuousStep`); at the pole the printed "`ṽ_t` and `β_t` are
  continuous" does not apply (`β_t(z) = -∞`) and `ObstacleTendstoAtBotStep` is used.
* `ObstacleNonCoincidenceHarmonicStep2` — Step 2 (lines 3661-3712): `ṽ_t` is subharmonic on `Λ_t` (AG01
  Thm 3.2.2 and the lowering `ψ = min (H, ṽ_t)`). [hard, 2-3 rounds]
* `ObstacleNonCoincidenceHarmonicStep3` — Step 3 (connected, lines 3714-3716): no nonempty open `W ⊆ Λ_t` with
  `z ∉ closure W` and `∂W ∩ Λ_t = ∅` (the odometer is subharmonic on `W`, vanishes on `∂W`, by Lemma A.4 on the
  part of `∂W` in `∂B_R`, and is positive on `W`: maximum principle). [medium, 1-2 rounds]

Shared steps used by the reduction (Basic.lean): `LaplacianLEOfSuperharmonicStep`,
`HasLaplacianOfLaplacianLEGEStep`, `GreenPotentialBallContinuousStep`, `ObstacleTendstoAtBotStep`.

## The reduction (proved)

`obstacleNonCoincidenceHarmonicGeneral_of_steps`: openness as above; `Δ ṽ_t ≤ 0` on `Λ_t` from `ṽ_t ∈ S̃(t)`
(Lemma A.1) and `Δ ṽ_t ≥ 0` from Step 2, so `Δ ṽ_t = 0`; connectedness from Step 3 applied to `W = Λ_t \ Λ₀`, with
`Λ₀` the connected component of `Λ_t` containing the pole (`isConnected_of_forall_isOpen_eq_empty`).
-/

namespace HarmonicBalls

open MeasureTheory Metric Filter Topology Set

/-- Lemma A.2 for a general radius `R > 0` and pole `z ∈ B_R` (the paper's case is `R = 1`, `z = 0`). -/
def ObstacleNonCoincidenceHarmonicGeneral : Prop :=
  ∀ μ : Measure ℂ, IsLocallyFiniteMeasure μ → ∀ R βminus βplus : ℝ, 0 < R → VolumeGrowth μ R βminus βplus →
  ∀ z ∈ ball (0 : ℂ) R, ∀ t : ℝ, 0 < t →
    IsOpen (nonCoincidenceSet μ R z t) ∧ IsConnected (nonCoincidenceSet μ R z t) ∧
    HasLaplacian (shiftedLeastSupersolution μ R z t) 0 0 (nonCoincidenceSet μ R z t)

/-! ## Steps -/

/-- **Lemma A.2, Step 2 (harmonicity, lines 3661-3712).** `ṽ_t` is subharmonic on `Λ_t` in the classical sense
(with Lemma A.1, `ṽ_t` is then harmonic on `Λ_t`). Printed argument, by contradiction: if not, AG01 Thm 3.2.2
gives `x ∈ Λ_t`, arbitrarily small discs `closedBall x r ⊆ Λ_t` and `H` continuous on the closed disc, harmonic
inside, with `H ≥ ṽ_t` on `∂B_r(x)` (eq:smaller) but `ṽ_t(x₀) > H(x₀)` somewhere inside (eq:below-w); for `r`
small, `inf_{∂B_r(x)} ṽ_t > sup_{closedBall x r} β_t` (eq:lies-way-above), so `H > β_t` on the disc
(eq:above-obstacle) and `ψ = min (H, ṽ_t)` on the disc, `ṽ_t` outside, is an element of `S̃(t)` below `ṽ_t` at
`x₀`, contradicting minimality. Uses: Lemma A.1 (general form), Step 1 (openness, in the reduction),
`SuperharmonicOfLaplacianLEStep`, `LaplacianLEOfSuperharmonicStep`, the Poisson integral on discs
(Mathlib `Mathlib/Analysis/Complex/Harmonic/Poisson.lean`). Difficulty: hard (2-3 rounds). -/
def ObstacleNonCoincidenceHarmonicStep2 : Prop :=
  ∀ μ : Measure ℂ, IsLocallyFiniteMeasure μ → ∀ R βminus βplus : ℝ, 0 < R → VolumeGrowth μ R βminus βplus →
  ∀ z ∈ ball (0 : ℂ) R, ∀ t : ℝ, 0 < t →
    IsSubharmonicOn (nonCoincidenceSet μ R z t) (shiftedLeastSupersolution μ R z t)

/-- **Lemma A.2, Step 3 (connectedness, lines 3714-3716).** There is no nonempty open `W ⊆ Λ_t` with
`z ∉ closure W` and `∂W ∩ Λ_t = ∅`. Printed argument ("a connected component of `Λ_t` not containing the origin
upon which `v_t` is non-zero, subharmonic, and 0 on its boundary — this violates the strong maximum
principle"): on `W`, `Δ v_t = Δ ṽ_t - Δ β_t = 0 + μ ≥ 0` (Step 2 with Lemma A.1, `GreenPotentialBallLaplacianStep`,
Prop 2.3), `v_t` is continuous on `closure W ⊆ closedBall 0 R \ {z}`, `v_t = 0` on `∂W` (points of `∂W ∩ B_R` lie
outside `Λ_t`; on `∂W ∩ ∂B_R` use Lemma A.4, which the printed proof uses implicitly), and `v_t > 0` on `W`; the
maximum principle for continuous subharmonic functions on bounded open sets gives `v_t ≤ 0` on `W`, so `W = ∅`.
Uses: Lemmas A.1, A.4 (general forms), Step 2, `GreenPotentialBallLaplacianStep`,
`GreenPotentialBallContinuousStep`, Prop 2.3, `SuperharmonicOfLaplacianLEStep`. Difficulty: medium
(1-2 rounds). -/
def ObstacleNonCoincidenceHarmonicStep3 : Prop :=
  ∀ μ : Measure ℂ, IsLocallyFiniteMeasure μ → ∀ R βminus βplus : ℝ, 0 < R → VolumeGrowth μ R βminus βplus →
  ∀ z ∈ ball (0 : ℂ) R, ∀ t : ℝ, 0 < t →
    ∀ W : Set ℂ, IsOpen W → W ⊆ nonCoincidenceSet μ R z t → z ∉ closure W →
      Disjoint (frontier W) (nonCoincidenceSet μ R z t) → W = ∅

/-! ## Topological glue -/

/-- An open set `Λ ∋ z` of a locally connected space is connected if every open `W ⊆ Λ` with `z ∉ closure W` and
`∂W ∩ Λ = ∅` is empty: apply the hypothesis to the union `W = Λ \ Λ₀` of the components other than the
component `Λ₀` of `z`. -/
theorem isConnected_of_forall_isOpen_eq_empty {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
    {Λ : Set X} {z : X} (hΛ : IsOpen Λ) (hz : z ∈ Λ)
    (h : ∀ W : Set X, IsOpen W → W ⊆ Λ → z ∉ closure W → Disjoint (frontier W) Λ → W = ∅) :
    IsConnected Λ := by
  have hΛ₀open : IsOpen (connectedComponentIn Λ z) := hΛ.connectedComponentIn
  have hΛ₀sub : connectedComponentIn Λ z ⊆ Λ := connectedComponentIn_subset _ _
  have hzΛ₀ : z ∈ connectedComponentIn Λ z := mem_connectedComponentIn hz
  have hWopen : IsOpen (Λ \ connectedComponentIn Λ z) := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    refine mem_of_superset (hΛ.connectedComponentIn.mem_nhds (mem_connectedComponentIn hx.1)) ?_
    intro y hy
    refine ⟨connectedComponentIn_subset _ _ hy, fun hy0 => hx.2 ?_⟩
    have hx' : x ∈ connectedComponentIn Λ x := mem_connectedComponentIn hx.1
    rwa [connectedComponentIn_eq hy, ← connectedComponentIn_eq hy0] at hx'
  have hcl : closure (Λ \ connectedComponentIn Λ z) ⊆ (connectedComponentIn Λ z)ᶜ :=
    closure_minimal (fun y hy => hy.2) hΛ₀open.isClosed_compl
  have hfr : Disjoint (frontier (Λ \ connectedComponentIn Λ z)) Λ := by
    rw [Set.disjoint_left]
    intro x hxf hxΛ
    rw [hWopen.frontier_eq] at hxf
    have hx0 : x ∈ connectedComponentIn Λ z := by
      by_contra hx0
      exact hxf.2 ⟨hxΛ, hx0⟩
    exact hcl hxf.1 hx0
  have hW := h _ hWopen sdiff_subset (fun hzc => hcl hzc hzΛ₀) hfr
  have heq : connectedComponentIn Λ z = Λ := by
    refine Subset.antisymm hΛ₀sub fun x hx => ?_
    by_contra hx0
    have : x ∈ Λ \ connectedComponentIn Λ z := ⟨hx, hx0⟩
    rw [hW] at this
    exact this
  rw [← heq]
  exact isConnected_connectedComponentIn_iff.2 hz

/-! ## The reduction -/

/-- **Lemma A.2, general radius and pole, from its steps.** -/
theorem obstacleNonCoincidenceHarmonicGeneral_of_steps (hA1 : ObstacleLeastSuperharmonicMajorantGeneral)
    (h23 : GreenFunctionBallStmt) (hW' : LaplacianLEOfSuperharmonicStep) (hLG : HasLaplacianOfLaplacianLEGEStep)
    (hq : GreenPotentialBallContinuousStep) (hpole : ObstacleTendstoAtBotStep)
    (h2 : ObstacleNonCoincidenceHarmonicStep2) (h3 : ObstacleNonCoincidenceHarmonicStep3) :
    ObstacleNonCoincidenceHarmonicGeneral := by
  intro μ hμ R βm βp hR hV z hz t ht
  obtain ⟨-, hvc, hvS, -, -⟩ := hA1 μ hμ R βm βp hR hV z hz t ht
  have hqc := hq μ hμ R βm βp hR hV
  have hβc := continuousOn_obstacle (t := t) h23 hR hz hqc
  have hΛsub : nonCoincidenceSet μ R z t ⊆ ball 0 R := fun x hx => hx.1
  have hvcont : ∀ x ∈ ball (0 : ℂ) R, ContinuousAt (shiftedLeastSupersolution μ R z t) x := fun x hx =>
    hvc.continuousAt (mem_of_superset (isOpen_ball.mem_nhds hx) ball_subset_closedBall)
  have hopen : IsOpen (nonCoincidenceSet μ R z t) := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    by_cases hxz : x = z
    · subst hxz
      have hlow : ∀ᶠ y in 𝓝 x, shiftedLeastSupersolution μ R x t x - 1 < shiftedLeastSupersolution μ R x t y :=
        (hvcont x hx.1).eventually (lt_mem_nhds (by linarith))
      have hβ : ∀ᶠ y in 𝓝[≠] x, obstacle μ R x t y < shiftedLeastSupersolution μ R x t x - 1 :=
        (hpole μ R x t hR hz ht hqc).eventually (eventually_lt_atBot _)
      rw [eventually_nhdsWithin_iff] at hβ
      filter_upwards [isOpen_ball.mem_nhds hx.1, hlow, hβ] with y hyb hyv hyβ
      refine ⟨hyb, ?_⟩
      by_cases hyx : y = x
      · exact Or.inl hyx
      · exact Or.inr ((hyβ hyx).trans hyv)
    · have hxb : x ∈ ball (0 : ℂ) R := hx.1
      have hlt : obstacle μ R z t x < shiftedLeastSupersolution μ R z t x := hx.2.resolve_left hxz
      have hβx : ContinuousAt (obstacle μ R z t) x := by
        refine hβc.continuousAt (mem_of_superset
          ((isOpen_ball.sdiff isClosed_singleton).mem_nhds ⟨hxb, hxz⟩) ?_)
        exact fun y hy => ⟨ball_subset_closedBall hy.1, hy.2⟩
      filter_upwards [isOpen_ball.mem_nhds hxb, hβx.eventually_lt (hvcont x hxb) hlt] with y hyb hy
      exact ⟨hyb, Or.inr hy⟩
  have hLE : LaplacianLE (shiftedLeastSupersolution μ R z t) 0 (nonCoincidenceSet μ R z t) :=
    hvS.2.1.mono_set hΛsub
  have hGE : LaplacianGE (shiftedLeastSupersolution μ R z t) 0 (nonCoincidenceSet μ R z t) :=
    LaplacianGE.of_laplacianLE_neg (hW' _ _ hopen ((hvc.mono (hΛsub.trans ball_subset_closedBall)).neg)
      (h2 μ hμ R βm βp hR hV z hz t ht))
  refine ⟨hopen, ?_, hLG _ _ hopen hLE hGE⟩
  exact isConnected_of_forall_isOpen_eq_empty hopen ⟨hz, Or.inl rfl⟩ (h3 μ hμ R βm βp hR hV z hz t ht)

/-- The general form of Lemma A.2 gives the printed statement (`R = 1`, `z = 0`). -/
theorem obstacleNonCoincidenceHarmonic_of_general (h : ObstacleNonCoincidenceHarmonicGeneral) :
    ObstacleNonCoincidenceHarmonicStmt := fun μ hμ βm βp hV t ht =>
  h μ hμ 1 βm βp one_pos hV 0 (mem_ball_self one_pos) t ht

/-- **Lemma A.2 from its steps** (and Lemma A.1, Prop 2.3, the shared steps). -/
theorem obstacleNonCoincidenceHarmonic_of_steps (hA1 : ObstacleLeastSuperharmonicMajorantGeneral)
    (h23 : GreenFunctionBallStmt) (hW' : LaplacianLEOfSuperharmonicStep) (hLG : HasLaplacianOfLaplacianLEGEStep)
    (hq : GreenPotentialBallContinuousStep) (hpole : ObstacleTendstoAtBotStep)
    (h2 : ObstacleNonCoincidenceHarmonicStep2) (h3 : ObstacleNonCoincidenceHarmonicStep3) :
    ObstacleNonCoincidenceHarmonicStmt :=
  obstacleNonCoincidenceHarmonic_of_general
    (obstacleNonCoincidenceHarmonicGeneral_of_steps hA1 h23 hW' hLG hq hpole h2 h3)

end HarmonicBalls
