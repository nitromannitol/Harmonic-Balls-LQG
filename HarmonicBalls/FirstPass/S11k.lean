import HarmonicBalls.FirstPass.S11h.Faithful
import HarmonicBalls.FirstPass.S11h.LocalEvents
import HarmonicBalls.FirstPass.S11f.SecondThresholds
import HarmonicBalls.FirstPass.S11e.CondPos
import HarmonicBalls.Proofs.Sec11.ModConstPairingLaw
import HarmonicBalls.FirstPass.Frozen.S11k
import HarmonicBalls.FirstPass.Frozen.S11j
import HarmonicBalls.FirstPass.S11k.EventAssembly
import HarmonicBalls.FirstPass.S11k.SetDistPositive

/-!
# First pass, Section 11: the faithful second pinch event, Lemma 11.16 (fp-S11k, owner z3)

Target: `firstPass_11_16_corrected : PinchSecondEventFaithfulStmt` (`FirstPass/S11h/Faithful.lean:80`).

Route (corrected paper, proof of `lemma:E2`, lines 3700-3727, and `lemma:massdiam`, lines 3511-3523; ChatGPT note
`notes/fp-gaps/CHATGPT-11-15-17-faithful.md` section 5, Steps 16.1-16.3). Write `F` for the event that the first
event and the crossing and Green thresholds hold, measurable for the field outside `W`, and `H` for the mass-diameter
event of `lemma:massdiam` on the local geometry `U, V, O₁ = B_δ(V̄), W`. Then `P (F ∩ H) > 0`, since `P[1_H | outside] > 0`
almost surely (conditioning), and `F ∩ H` lies in the faithful events by the threshold inequalities.

This file proves the composition `firstPass_11_16_corrected_of_steps` from two NEW steps. The conditional step
`PinchSecondConditionalMassFaithfulStep` is PROVED from the cited Draft Proposition 11.9 and three EXTERNAL frozen inputs
(`pinchSecondConditionalMass_of_frozen`, `FirstPass/Frozen/S11k.lean`). The exterior step `PinchSecondExteriorStep` is still a
hypothesis (OPEN, see its docstring). `firstPass_11_16_corrected` itself is not claimed (OPEN).
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

universe u

/-- NEW, OPEN: the exterior-measurable first event with the thresholds (paper `lemma:E2` proof, first sentences; ChatGPT
section 5, Step 16.2). For each buffered geometry, `γ ∈ (0, 2)`, `α₀ < Q`, `ξ`, and each LQG measure and metric of the field:
the sigma-algebra of the field outside `closure W` (the comap of the zero-mean pairings of `localModConstPairings`) is
contained in the ambient one, and for every `M > 0` there are deterministic `c₁, c₂ > 0` and an outside-measurable set `F`
of positive probability such that, almost surely, every point of `F` lies in `Ẽ₁ ∩ {c₁ ≤ D(∂B_δ, ∂B_{2δ})} ∩ {M S ≤ c₂}`.
The inclusion is almost everywhere, not pointwise: the model predicates identify `D`, `μ` with their canonical versions
only almost surely, so a pointwise inclusion fails for a version changed on a null set (ChatGPT, operator note 23:27 UTC,
section 3.1 counterexample). -/
def PinchSecondExteriorStep : Prop :=
  ∀ (U V W T Q' Q : Set ℂ) (δ : ℝ), IsBufferedPinchGeometry U V W T Q' Q δ →
  ∀ γ α₀ ξ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ α₀ hcirc μ → IsLQGMetricOfField P γ ξ α₀ hC D →
    MeasurableSpace.comap (localModConstPairings α₀ hC (closure W)ᶜ) inferInstance ≤ ‹MeasurableSpace Ω› ∧
    ∀ M : ℝ, 0 < M → ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∃ F : Set Ω,
        MeasurableSet[MeasurableSpace.comap (localModConstPairings α₀ hC (closure W)ᶜ) inferInstance] F ∧
        (∀ᵐ ω ∂P, ω ∈ F → pinchFirstEvent (D ω) W T Q' Q δ ∧ c₁ ≤ setDist (D ω) (sphere 0 δ) (sphere 0 (2 * δ)) ∧
          ENNReal.ofReal M * annulusGreenPotentialSup (μ ω) 0 3 6 ≤ ENNReal.ofReal c₂) ∧
        0 < P F

/-- The outside-measurability conjunct of `PinchSecondExteriorStep`, for every `α₀`: the zero-mean local pairings of a
whole-plane GFF are measurable (`hC ω φ - α₀ ∫ φ log|·|`, a deterministic shift of `hC ω φ`), so their sigma-algebra is
contained in the ambient one. Proved; no input. -/
theorem localModConstPairings_comap_le {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hgff : IsWholePlaneGFF P hC hcirc) (U : Set ℂ) :
    MeasurableSpace.comap (localModConstPairings α₀ hC U) inferInstance ≤ ‹MeasurableSpace Ω› := by
  refine Measurable.comap_le ?_
  refine measurable_pi_iff.2 (fun φ => ?_)
  have hφ : IsTestFunction Set.univ φ.1 := ⟨φ.2.1.1, φ.2.1.2.1, Set.subset_univ _⟩
  have heq : (fun ω => localModConstPairings α₀ hC U ω φ) =
      fun ω => hC ω φ.1 - α₀ * ∫ x, φ.1 x * Real.log ‖x‖ := by
    funext ω
    rfl
  rw [heq]
  exact (hgff.measurable_pairing φ.1 hφ).sub measurable_const

/-- NEW, OPEN: the event part of `PinchSecondExteriorStep` (the statement `∀ M > 0, ∃ c₁ c₂ F ...` without its
outside-measurability conjunct, which `localModConstPairings_comap_le` proves). This is the single remaining input of
`firstPass_11_16_corrected`. The operator note 23:12 UTC gap (global `setDist` in `pinchFirstEvent`,
Draft/Section11.lean:95-99) is answered by ChatGPT (23:27 UTC, `notes/fp-gaps/CHATGPT-e2-locality-z3-frozen.md`
sections 1-2): both global distances are exit distances, local by first-exit truncation, so `pinchFirstEvent` and the
Draft are unchanged. Still OPEN here: the exit/crossing locality lemmas (formulas (1)-(2) of that note) and the
exterior-code versions of `L, A, a₀, d₀, a₁, S` (its section 2.2, modulo-constant bridge (3)), and the positivity of the
stronger local event `E₁` (corrected `lem:E1`). -/
def PinchSecondExteriorEventStep : Prop :=
  ∀ (U V W T Q' Q : Set ℂ) (δ : ℝ), IsBufferedPinchGeometry U V W T Q' Q δ →
  ∀ γ α₀ ξ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ α₀ hcirc μ → IsLQGMetricOfField P γ ξ α₀ hC D →
    ∀ M : ℝ, 0 < M → ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∃ F : Set Ω,
        MeasurableSet[MeasurableSpace.comap (localModConstPairings α₀ hC (closure W)ᶜ) inferInstance] F ∧
        (∀ᵐ ω ∂P, ω ∈ F → pinchFirstEvent (D ω) W T Q' Q δ ∧ c₁ ≤ setDist (D ω) (sphere 0 δ) (sphere 0 (2 * δ)) ∧
          ENNReal.ofReal M * annulusGreenPotentialSup (μ ω) 0 3 6 ≤ ENNReal.ofReal c₂) ∧
        0 < P F

/-- `PinchSecondExteriorStep` is equivalent to its event part: the outside-measurability conjunct is proved. -/
theorem pinchSecondExteriorStep_of_event (hE : PinchSecondExteriorEventStep.{u}) : PinchSecondExteriorStep.{u} := by
  intro U V W T Q' Q δ hG γ α₀ ξ hγ0 hγ2 hα Ω _ P hC hcirc μ D hGFF hμ hDm
  exact ⟨localModConstPairings_comap_le hGFF (closure W)ᶜ,
    hE U V W T Q' Q δ hG γ α₀ ξ hγ0 hγ2 hα Ω P hC hcirc μ D hGFF hμ hDm⟩

/-- NEW, OPEN: the conditional mass-diameter event of `lemma:massdiam` (paper lines 3511-3523) on the local geometry
`U ⋐ V ⋐ O₁ = B_δ(V̄) ⋐ W` of a buffered configuration, with the field outside `closure W` as conditioning. For all
`c₁, c₂ > 0` there is a measurable `H` inside `{μ(U) > 2c₂, diam_D(V̄; B_δ(V̄)) < c₁/2}` whose conditional probability given
the outside sigma-algebra is almost surely positive (inner-measure form, as in `PinchSecondMassStep`). -/
def PinchSecondConditionalMassFaithfulStep : Prop :=
  ∀ (U V W T Q' Q : Set ℂ) (δ : ℝ), IsBufferedPinchGeometry U V W T Q' Q δ →
  ∀ γ α₀ ξ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ α₀ hcirc μ → IsLQGMetricOfField P γ ξ α₀ hC D →
  ∀ c₁ c₂ : ℝ, 0 < c₁ → 0 < c₂ →
    ∃ H : Set Ω, MeasurableSet H ∧
      H ⊆ {ω | ENNReal.ofReal (2 * c₂) < μ ω U ∧ internalDiam (D ω) δ (closure V) < ENNReal.ofReal (c₁ / 2)} ∧
      ∀ᵐ ω ∂P, 0 < (P[H.indicator (1 : Ω → ℝ) |
        MeasurableSpace.comap (localModConstPairings α₀ hC (closure W)ᶜ) inferInstance]) ω

/-- Lemma 11.16 (`lemma:second-event-proof`, corrected), faithful form, CONDITIONAL on the two NEW steps above (OPEN).
Proof: for `M > 0` take the thresholds `c₁, c₂` and the outside-measurable `F` of `PinchSecondExteriorStep`, and the mass set
`H` of `PinchSecondConditionalMassFaithfulStep` for the same thresholds. Then `0 < P (F ∩ H)` by
`measure_inter_pos_of_condExp_indicator_pos`. On `F ∩ H`: `internalDiam V ≤ internalDiam V̄ < c₁/2 < c₁ ≤ D(∂B_δ, ∂B_{2δ})`
and `M S ≤ c₂ < 2c₂ < μ(U)`, so `pinchSecondEvent_of_thresholds` gives `Ẽ₂(M)`, and `Ẽ₁` holds from `F`. The inclusion
on `F` is almost sure, so the witness is `(F ∩ H) \ N` with `N` an ambient measurable null superset of the exceptions. -/
theorem firstPass_11_16_corrected_of_steps (hX : PinchSecondExteriorStep.{u})
    (hM : PinchSecondConditionalMassFaithfulStep.{u}) : PinchSecondEventFaithfulStmt.{u} := by
  intro U V W T Q' Q δ hG γ α₀ ξ hγ0 hγ2 hα Ω _ P hC hcirc μ D hGFF hμ hD M hM0
  have : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  obtain ⟨hle, hsteps⟩ := hX U V W T Q' Q δ hG γ α₀ ξ hγ0 hγ2 hα Ω P hC hcirc μ D hGFF hμ hD
  obtain ⟨c₁, c₂, hc₁, hc₂, F, hF, hFsub, hFpos⟩ := hsteps M hM0
  obtain ⟨H, hHm, hHsub, hcond⟩ :=
    hM U V W T Q' Q δ hG γ α₀ ξ hγ0 hγ2 hα Ω P hC hcirc μ D hGFF hμ hD c₁ c₂ hc₁ hc₂
  have hpos : 0 < P (F ∩ H) :=
    measure_inter_pos_of_condExp_indicator_pos P hle hF hHm hFpos hcond
  -- The exterior inclusion holds only almost surely: remove an ambient measurable null set AFTER conditioning
  -- (ChatGPT, operator note 23:27 UTC, section 3.4). `P ((F ∩ H) \ N) = P (F ∩ H) > 0`.
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hFsub)
  have hBpos : 0 < P ((F ∩ H) \ N) := by
    rw [measure_sdiff_null hN0]
    exact hpos
  refine ⟨(F ∩ H) \ N, fun ω hω => ?_, ((hle _ hF).inter hHm).diff hNm, hBpos⟩
  have hωF : ω ∈ F := hω.1.1
  have hgood : pinchFirstEvent (D ω) W T Q' Q δ ∧ c₁ ≤ setDist (D ω) (sphere 0 δ) (sphere 0 (2 * δ)) ∧
      ENNReal.ofReal M * annulusGreenPotentialSup (μ ω) 0 3 6 ≤ ENNReal.ofReal c₂ := by
    by_contra hbad
    exact hω.2 (hNsub fun h => hbad (h hωF))
  obtain ⟨hE1, hsep, hS⟩ := hgood
  obtain ⟨hmass, hdiam⟩ := hHsub hω.1.2
  exact ⟨hE1, pinchSecondEvent_of_thresholds hc₁ hc₂
    ((internalDiam_le_closure (D ω) δ V).trans hdiam.le) hsep hS hmass⟩

/-- The conditional mass-diameter step `PinchSecondConditionalMassFaithfulStep`, proved from the cited Draft Proposition 11.9
(`SmallMetricDiameterLargeMassStmt`, hypothesis `hD`) and the three EXTERNAL frozen inputs of `FirstPass/Frozen/S11k.lean`.

Proof. The buffered geometry makes `U = B_ρU(c)`, `V = B_ρV(c)`, `W = B_ρW(c)` concentric disks with `closure (B_{10δ}(V̄)) ⊆ W`.
Put `O = B_δ(V̄)` (thickening) and `V' = B_{δ/2}(V̄)`. Then `U ⊆ V' ⊆ O`, `closure V' ⊆ O`, `closure O ⊆ W ⊆ annulus 0 1 2`, and
`U, V', O` are open, connected (convex) and bounded. Draft 11.9 on `(U, V', O)` with `C = 2c₂ + 1` and
`ε = min(c₁/4, (2c₂+1)/2)` gives a measurable `A` with `P A > 0` and `A ⊆ {diam ≤ ε, μ(U) ≥ C}`; the bound on `V' ⊇ V̄`
gives the internal diameter of `V̄` (no continuity needed). The frozen inputs give `g₁ = μ(U)` and `g₂ = diam^δ(V̄)` almost
surely, with `g_i` measurable for `σ(h|_O)`. Let `E = {2c₂ < g₁, g₂ < c₁/2}` (inner) and `N₀` a measurable null set off which
`μ(U) = g₁` and `diam = g₂`. Then `H = E ∖ N₀` is measurable and lies in the faithful set; `A ⊆ H ∪ N₀`, so `P H ≥ P A > 0`;
`1_H =ᵐ 1_E`, and the domain Markov input gives `0 < P[1_E | outside]` almost surely, hence `0 < P[1_H | outside]` a.s. -/
theorem pinchSecondConditionalMass_of_frozen (hD : SmallMetricDiameterLargeMassStmt.{u})
    (hM : LQGMassInnerMeasurableFrozen.{u}) (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
    (hMk : DomainMarkovConditionalPositiveFrozen.{u}) : PinchSecondConditionalMassFaithfulStep.{u} := by
  intro U V W T Q' Q δ hG γ α₀ ξ hγ0 hγ2 hα Ω _ P hC hcirc μ D hGFF hμ hDm c₁ c₂ hc₁ hc₂
  have : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  obtain ⟨c, ρU, ρV, ρW, hU, hV, hW⟩ := hG.concentric
  have hδ : 0 < δ := hG.delta_pos
  have hδ2 : 0 < δ / 2 := by linarith
  have h10 : (0 : ℝ) < 10 * δ := by linarith
  have hbU := hG.buffer_U
  have hbV := hG.buffer_V
  have hbW := hG.buffer_W
  have hUV : U ⊆ V := fun x hx => hbU (subset_closure (self_subset_thickening h10 _ (subset_closure hx)))
  have hVW : V ⊆ W := fun x hx => hbV (subset_closure (self_subset_thickening h10 _ (subset_closure hx)))
  have hWann : W ⊆ annulus 0 1 2 := fun x hx =>
    (hbW (subset_closure (self_subset_thickening h10 _ (subset_closure hx)))).2
  have hρU : 0 < ρU := by
    obtain ⟨x, hx⟩ := hG.U_nonempty
    rw [hU] at hx
    exact dist_nonneg.trans_lt (mem_ball.1 hx)
  obtain ⟨x0, hx0⟩ := hG.U_nonempty
  have hρW : 0 < ρW := by
    have hx0W : x0 ∈ ball c ρW := by rw [← hW]; exact hVW (hUV hx0)
    exact dist_nonneg.trans_lt (mem_ball.1 hx0W)
  have hUo : IsOpen U := hG.isOpen_U
  have hUc : IsConnected U := by
    rw [hU]; exact (convex_ball c ρU).isConnected (nonempty_ball.2 hρU)
  have hUb : Bornology.IsBounded U := by rw [hU]; exact isBounded_ball
  have hcV : Convex ℝ (closure V) := by rw [hV]; exact (convex_ball c ρV).closure
  have hVb : Bornology.IsBounded (closure V) := by rw [hV]; exact isBounded_ball.closure
  have hVcpt : IsCompact (closure V) := by rw [hV]; exact isBounded_ball.isCompact_closure
  have hV'o : IsOpen (thickening (δ / 2) (closure V)) := isOpen_thickening
  have hO1o : IsOpen (thickening δ (closure V)) := isOpen_thickening
  have hV'c : IsConnected (thickening (δ / 2) (closure V)) :=
    (hcV.thickening (δ / 2)).isConnected ⟨x0, self_subset_thickening hδ2 _ (subset_closure (hUV hx0))⟩
  have hO1c : IsConnected (thickening δ (closure V)) :=
    (hcV.thickening δ).isConnected ⟨x0, self_subset_thickening hδ _ (subset_closure (hUV hx0))⟩
  have hV'b : Bornology.IsBounded (thickening (δ / 2) (closure V)) := hVb.thickening
  have hO1b : Bornology.IsBounded (thickening δ (closure V)) := hVb.thickening
  have hUV' : U ⊆ thickening (δ / 2) (closure V) := fun x hx =>
    self_subset_thickening hδ2 _ (subset_closure (hUV hx))
  have hclV' : closure V ⊆ thickening (δ / 2) (closure V) := self_subset_thickening hδ2 _
  have hV'O1 : thickening (δ / 2) (closure V) ⊆ thickening δ (closure V) := thickening_mono (by linarith) _
  have hcl : closure (thickening (δ / 2) (closure V)) ⊆ thickening δ (closure V) :=
    (closure_thickening_subset_cthickening (δ / 2) (closure V)).trans
      (cthickening_subset_thickening' hδ (by linarith) _)
  have hO1W : closure (thickening δ (closure V)) ⊆ W :=
    (closure_mono (thickening_mono (by linarith) _)).trans hbV
  have hO1W' : thickening δ (closure V) ⊆ W := subset_closure.trans hO1W
  have hdisj : Disjoint (thickening δ (closure V)) (sphere (0 : ℂ) 1) := by
    refine Set.disjoint_left.2 fun x hx hs => ?_
    have hann : x ∈ ball (0 : ℂ) 2 \ closedBall (0 : ℂ) 1 := hWann (hO1W' hx)
    exact hann.2 (sphere_subset_closedBall hs)
  -- Draft Proposition 11.9 on the disks `U ⊆ V' ⊆ O`
  have hε : 0 < min (c₁ / 4) ((2 * c₂ + 1) / 2) := lt_min (by linarith) (by linarith)
  have hεle : min (c₁ / 4) ((2 * c₂ + 1) / 2) ≤ c₁ / 4 := min_le_left _ _
  have hεC : min (c₁ / 4) ((2 * c₂ + 1) / 2) < 2 * c₂ + 1 :=
    lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨A, hAsub, hAm, hAp⟩ := hD γ α₀ ξ hγ0 hγ2 hα Ω P hC hcirc μ D hGFF hμ hDm
    U (thickening (δ / 2) (closure V)) (thickening δ (closure V))
    hUo hUc hUb hV'o hV'c hV'b hO1o hO1c hO1b hUV' hV'O1 hcl hdisj
    (2 * c₂ + 1) _ hε hεC
  -- inner versions of the mass and of the internal diameter
  have hUO1 : closure U ⊆ thickening δ (closure V) :=
    (closure_mono hUV).trans (self_subset_thickening hδ _)
  obtain ⟨g1, hg1m, hg1⟩ := hM γ α₀ Ω P hC hcirc μ hGFF hγ0 hγ2 hα hμ
    (thickening δ (closure V)) U hO1o hUo hUb hUO1
  obtain ⟨g2, hg2m, hg2⟩ := hDiam γ ξ α₀ Ω P hC hcirc D hGFF hγ0 hγ2 hα hDm δ (closure V) hδ hVcpt
  have hbad : ∀ᵐ ω ∂P, μ ω U = g1 ω ∧ internalDiam (D ω) δ (closure V) = g2 ω := hg1.and hg2
  obtain ⟨N0, hN0sub, hN0m, hN0null⟩ : ∃ N0 : Set Ω,
      {ω | ¬ (μ ω U = g1 ω ∧ internalDiam (D ω) δ (closure V) = g2 ω)} ⊆ N0 ∧ MeasurableSet N0 ∧ P N0 = 0 := by
    obtain ⟨t, hts, htm, ht0⟩ := exists_measurable_superset_of_null (ae_iff.1 hbad)
    exact ⟨t, hts, htm, ht0⟩
  set E : Set Ω := {ω | ENNReal.ofReal (2 * c₂) < g1 ω ∧ g2 ω < ENNReal.ofReal (c₁ / 2)} with hE
  have hEm : MeasurableSet[fieldSigmaAlgebra α₀ hC (thickening δ (closure V))] E :=
    (measurableSet_lt measurable_const hg1m).inter (measurableSet_lt hg2m measurable_const)
  have hEm0 : MeasurableSet E := (hGFF.fieldSigmaAlgebra_le α₀ (thickening δ (closure V))) _ hEm
  -- the mass-diameter event `E \ N₀` and its positivity
  have hAH : A ⊆ (E ∩ N0ᶜ) ∪ N0 := by
    intro ω hωA
    by_cases hN : ω ∈ N0
    · exact Or.inr hN
    · left
      have hgood : μ ω U = g1 ω ∧ internalDiam (D ω) δ (closure V) = g2 ω := by
        by_contra hb
        exact hN (hN0sub hb)
      obtain ⟨hb1, hb2⟩ := hAsub hωA
      have hdiam : internalDiam (D ω) δ (closure V) ≤ ENNReal.ofReal (min (c₁ / 4) ((2 * c₂ + 1) / 2)) :=
        iSup₂_le fun x hx => iSup₂_le fun y hy =>
          hb1 x (hclV' hx) y (hclV' hy)
      have hlt1 : ENNReal.ofReal (min (c₁ / 4) ((2 * c₂ + 1) / 2)) < ENNReal.ofReal (c₁ / 2) :=
        (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
      have h1 : ENNReal.ofReal (2 * c₂) < g1 ω := by
        rw [← hgood.1]
        exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)) hb2
      have h2 : g2 ω < ENNReal.ofReal (c₁ / 2) := by
        rw [← hgood.2]
        exact lt_of_le_of_lt hdiam hlt1
      exact ⟨⟨h1, h2⟩, hN⟩
  have hHpos : 0 < P (E ∩ N0ᶜ) := by
    have hle : P A ≤ P ((E ∩ N0ᶜ) ∪ N0) := measure_mono hAH
    have hle2 : P ((E ∩ N0ᶜ) ∪ N0) ≤ P (E ∩ N0ᶜ) + P N0 := measure_union_le _ _
    rw [hN0null, add_zero] at hle2
    exact lt_of_lt_of_le hAp (hle.trans hle2)
  have hEpos : 0 < P E := lt_of_lt_of_le hHpos (measure_mono Set.inter_subset_left)
  -- domain Markov: conditional positivity of the inner event `E`
  have hcond := hMk α₀ Ω P hC hcirc hGFF W (thickening δ (closure V)) ⟨c, ρW, hρW, hW⟩ hO1o hO1W
    E hEm hEpos
  refine ⟨E ∩ N0ᶜ, hEm0.inter hN0m.compl, ?_, ?_⟩
  · rintro ω ⟨⟨h1, h2⟩, hnN⟩
    have hgood : μ ω U = g1 ω ∧ internalDiam (D ω) δ (closure V) = g2 ω := by
      by_contra hb
      exact hnN (hN0sub hb)
    show ENNReal.ofReal (2 * c₂) < μ ω U ∧ internalDiam (D ω) δ (closure V) < ENNReal.ofReal (c₁ / 2)
    rw [hgood.1, hgood.2]
    exact ⟨h1, h2⟩
  · have hae : ∀ᵐ ω ∂P, ω ∉ N0 := by
      rw [ae_iff]; simpa using hN0null
    have hcongr : (E ∩ N0ᶜ).indicator (1 : Ω → ℝ) =ᵐ[P] E.indicator (1 : Ω → ℝ) := by
      filter_upwards [hae] with ω hω
      by_cases h : ω ∈ E
      · simp [Set.indicator, h, hω]
      · simp [Set.indicator, h]
    filter_upwards [condExp_congr_ae hcongr, hcond] with ω h2 h1
    rw [h2]
    exact h1

/-- Lemma 11.16 (`lemma:second-event-proof`, corrected), faithful form, CONDITIONAL on the single NEW step
`PinchSecondExteriorStep` (OPEN). The conditional mass-diameter step is discharged by `pinchSecondConditionalMass_of_frozen`
from Draft Proposition 11.9 and the three EXTERNAL frozen inputs `LQGMassInnerMeasurableFrozen`,
`LQGInternalDiamInnerMeasurableFrozen`, `DomainMarkovConditionalPositiveFrozen`. -/
theorem firstPass_11_16_corrected_of_exterior (hX : PinchSecondExteriorStep.{u})
    (hD : SmallMetricDiameterLargeMassStmt.{u}) (hM : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u}) (hMk : DomainMarkovConditionalPositiveFrozen.{u}) :
    PinchSecondEventFaithfulStmt.{u} :=
  firstPass_11_16_corrected_of_steps hX (pinchSecondConditionalMass_of_frozen hD hM hDiam hMk)

/-- Lemma 11.16 (faithful form), conditional on the event part of the exterior step only (OPEN). Once
`PinchSecondExteriorEventStep` is proved, this gives `firstPass_11_16_corrected` with the same hypotheses minus it. -/
theorem firstPass_11_16_corrected_of_event (hE : PinchSecondExteriorEventStep.{u})
    (hD : SmallMetricDiameterLargeMassStmt.{u}) (hM : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u}) (hMk : DomainMarkovConditionalPositiveFrozen.{u}) :
    PinchSecondEventFaithfulStmt.{u} :=
  firstPass_11_16_corrected_of_exterior (pinchSecondExteriorStep_of_event hE) hD hM hDiam hMk

/-- NEW, OPEN: the exterior version bundle of Lemma 11.16 (the N1 and N2 inputs of the corrected proof of `lemma:E2`,
paper lines 3700-3727; ChatGPT `notes/fp-gaps/CHATGPT-n4-B2-z3-N1N2.md` sections 3-6). With `m` the zero-mean exterior
sigma-algebra `comap (localModConstPairings α₀ hC (closure W)ᶜ)`, it asserts: (N1) an `m`-measurable event `F₀` that is
almost surely `pinchFirstEvent` (the exterior versions of `L, a₀, a₁, d₀`, which `pinchFirstEvent_ae_iff_versions` turns into one event);
(N1') an `m`-measurable real version `d` of `D(∂B_δ, ∂B_{2δ})`; (N2) for every `M > 0` an `m`-measurable `S` with
`M · SG_{3,6}(0) ≤ S` almost surely and `S ≠ ∞` on `F₀` almost surely. The Green bound of (N2) is
`exists_outside_green_of_singular_weyl` (`hbase` is the `α₀ = 0` input, open as B1), and its finiteness on `F₀` is the
input `hFin` of `exists_exterior_annulusGreenPotentialSup` (n4). Nothing here is claimed: it is the single open input of
`PinchSecondExteriorEventStep` after the reductions below. -/
def PinchSecondExteriorVersionsStep : Prop :=
  ∀ (U V W T Q' Q : Set ℂ) (δ : ℝ), IsBufferedPinchGeometry U V W T Q' Q δ →
  ∀ γ α₀ ξ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ α₀ hcirc μ → IsLQGMetricOfField P γ ξ α₀ hC D →
    ∃ F₀ : Set Ω,
      MeasurableSet[MeasurableSpace.comap (localModConstPairings α₀ hC (closure W)ᶜ) inferInstance] F₀ ∧
      (∀ᵐ ω ∂P, ω ∈ F₀ ↔ pinchFirstEvent (D ω) W T Q' Q δ) ∧
      ∃ d : Ω → ℝ,
        Measurable[MeasurableSpace.comap (localModConstPairings α₀ hC (closure W)ᶜ) inferInstance] d ∧
        (∀ᵐ ω ∂P, d ω = setDist (D ω) (sphere 0 δ) (sphere 0 (2 * δ))) ∧
        ∀ M : ℝ, 0 < M → ∃ S : Ω → ENNReal,
          Measurable[MeasurableSpace.comap (localModConstPairings α₀ hC (closure W)ᶜ) inferInstance] S ∧
          (∀ᵐ ω ∂P, ENNReal.ofReal M * annulusGreenPotentialSup (μ ω) 0 3 6 ≤ S ω) ∧
          (∀ᵐ ω ∂P, ω ∈ F₀ → S ω ≠ ⊤)

/-- `PinchSecondExteriorEventStep` from `PinchSecondExteriorVersionsStep` (N1, N2, open) and two inputs already in the
repository: the Draft positivity of the first event of Lemma 11.15 (`PinchFirstEventFaithfulStmt`, used only through its
measurable inner-measure form, which `F₀` dominates almost surely) and the EXTERNAL metric axioms of the LQG metric
(`LQGMetricFieldAxiomsUnivFrozen`, item I: almost surely a Euclidean length metric). Positivity of `d` on `F₀` is
`setDist_sphere_two_pos` (`S11k/SetDistPositive.lean`). Proved, conditional on the two named inputs. -/
theorem pinchSecondExteriorEventStep_of_versions (hV : PinchSecondExteriorVersionsStep.{u})
    (hPos : PinchFirstEventFaithfulStmt.{u}) (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) :
    PinchSecondExteriorEventStep.{u} := by
  intro U V W T Q' Q δ hG γ α₀ ξ hγ0 hγ2 hα Ω _ P hC hcirc μ D hGFF hμ hD M hM
  have hDx := hD
  obtain ⟨F₀, hF₀m, hF₀iff, d, hdm, hdv, hS⟩ :=
    hV U V W T Q' Q δ hG γ α₀ ξ hγ0 hγ2 hα Ω P hC hcirc μ D hGFF hμ hD
  obtain ⟨A, hAsub, -, hAp⟩ := hPos U V W T Q' Q δ hG γ α₀ ξ hγ0 hγ2 hα Ω P hC hcirc D hGFF hDx
  have hAle : A ≤ᵐ[P] F₀ := by
    filter_upwards [hF₀iff] with ω hω hA
    exact hω.2 (hAsub hA)
  have hF₀pos : 0 < P F₀ := lt_of_lt_of_le hAp (measure_mono_ae hAle)
  obtain ⟨𝔇, h𝔇, hDae⟩ := hDx
  have hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω) := by
    obtain ⟨hI, -⟩ := hAx Ω P γ ξ α₀ hC hcirc hGFF hγ0 hγ2 hα 𝔇 h𝔇
    filter_upwards [hI, hDae] with ω h1 h2
    have hDeq : D ω = fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal := by
      funext u v
      have h3 := ENNReal.toReal_ofReal (h2 u v).1
      rw [(h2 u v).2] at h3
      exact h3.symm
    rw [hDeq]
    exact h1.2
  have hdpos : ∀ᵐ ω ∂P, ω ∈ F₀ → 0 < d ω := by
    filter_upwards [hdv, hmetric] with ω h1 h2 _
    rw [h1]
    exact setDist_sphere_two_pos h2 hG.delta_pos
  obtain ⟨S, hSm, hSv, hSfin⟩ := hS M hM
  exact exists_pinchSecondExteriorEvent_of_versions W T Q' Q δ M hF₀m hF₀pos
    (hF₀iff.mono fun ω h hω => h.1 hω) hdm hdv hdpos hSm hSv hSfin

/-- Lemma 11.16, corrected form, conditional on the named inputs `PinchSecondExteriorVersionsStep` (OPEN, N1 and N2)
and the Draft positivity `PinchFirstEventFaithfulStmt` (Lemma 11.15) with the EXTERNAL metric axioms. The Proposition 11.9
input and the two frozen conditional-mass inputs are as in `firstPass_11_16_corrected_of_event`. -/
theorem firstPass_11_16_corrected_of_versions (hV : PinchSecondExteriorVersionsStep.{u})
    (hPos : PinchFirstEventFaithfulStmt.{u}) (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hD : SmallMetricDiameterLargeMassStmt.{u}) (hM : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u}) (hMk : DomainMarkovConditionalPositiveFrozen.{u}) :
    PinchSecondEventFaithfulStmt.{u} :=
  firstPass_11_16_corrected_of_event (pinchSecondExteriorEventStep_of_versions hV hPos hAx) hD hM hDiam hMk

end HarmonicBalls

#print axioms HarmonicBalls.pinchSecondExteriorEventStep_of_versions
#print axioms HarmonicBalls.firstPass_11_16_corrected_of_versions
