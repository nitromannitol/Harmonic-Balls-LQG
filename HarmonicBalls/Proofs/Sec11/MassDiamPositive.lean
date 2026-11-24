import HarmonicBalls.FirstPass.S11k
import HarmonicBalls.FirstPass.Phase2.FieldAxiomsConsequencesDerived
import HarmonicBalls.FirstPass.Phase2.CircleAverageLocalityLinkDerived
import HarmonicBalls.FirstPass.Phase2.DomainMarkovConditionalPositiveHolds

/-!
# Lemma 11.18 for every geometry of concentric disks

Lemma 11.18 (`s11-pinch:lem:massdiam`, corrected paper lines 3583-3595): let `U₀ ⋐ V₀ ⋐ O` be
concentric disks with `Ō ⋐ W₀`, where `W₀` is a disk avoiding `0` and the normalization circle. For
every `c, ε > 0`, with positive probability `μ_{h^α}(U₀) > c` and `diam_{h^α}(V̄₀; O) < ε`, and the
conditional probability of this event given the field outside `W₀` is almost surely positive.

`massDiamModConst_holds` proves the lemma for every such geometry, with the conditioning on the
field outside `W̄₀` modulo additive constants. The route is the one of
`pinchSecondConditionalMass_of_frozen` (`FirstPass/S11k.lean`), which treats the disks of a buffered
pinch geometry: with `δ = ρ_O - ρ_V` the disk `O` is the `δ`-thickening of `V̄₀`, so
`diam_{h^α}(V̄₀; O)` is the internal diameter `internalDiam D δ V̄₀`. Proposition 11.9 on the
disks `U₀ ⊆ B_{δ/2}(V̄₀) ⊆ O` gives the unconditional event; the mass of `U₀` and the internal
diameter agree almost surely with random variables measurable for the field on `O`
(Facts 2.1 II and 2.2 II), and the domain Markov property of the whole-plane GFF gives the
conditional positivity. The unconditional assertion therefore comes from Proposition 11.9 and not
from the tiling and bump construction of the printed proof (lines 3596-3660).
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal

universe u

/-- Lemma 11.18 (`s11-pinch:lem:massdiam`, corrected paper lines 3583-3595), with the conditioning
on the field outside `W̄₀` modulo additive constants. The disks are `U₀ = B_{ρ_U}(c₀)`,
`V₀ = B_{ρ_V}(c₀)`, `O = B_{ρ_O}(c₀)` with `0 < ρ_U < ρ_V < ρ_O` (concentric, `U₀ ⋐ V₀ ⋐ O`), and
`W₀ = B_r(w)` with `Ō ⊆ W₀`, `0 ∉ W₀` and `W₀ ∩ ∂B₁(0) = ∅`. For all `c, ε > 0` there is a measurable
event `H` inside `{μ_h(U₀) > c, diam_h(V̄₀; O) < ε}` (with `diam_h(V̄₀; O)` the supremum over
`x, y ∈ V̄₀` of the internal metric `D_h(x, y; O)`) of positive probability whose conditional
probability given the modulo-constant pairings outside `W̄₀` is almost surely positive. -/
def MassDiamModConstStmt : Prop :=
  ∀ (c₀ : ℂ) (ρU ρV ρO : ℝ), 0 < ρU → ρU < ρV → ρV < ρO →
  ∀ (w : ℂ) (r : ℝ), closure (ball c₀ ρO) ⊆ ball w r → (0 : ℂ) ∉ ball w r →
    Disjoint (ball w r) (sphere (0 : ℂ) 1) →
  ∀ γ α₀ ξ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ α₀ hcirc μ → IsLQGMetricOfField P γ ξ α₀ hC D →
  ∀ c ε : ℝ, 0 < c → 0 < ε →
    ∃ H : Set Ω, MeasurableSet H ∧
      H ⊆ {ω | ENNReal.ofReal c < μ ω (ball c₀ ρU) ∧
        (⨆ x ∈ closure (ball c₀ ρV), ⨆ y ∈ closure (ball c₀ ρV),
          internalMetric (D ω) (ball c₀ ρO) x y) < ENNReal.ofReal ε} ∧
      0 < P H ∧
      ∀ᵐ ω ∂P, 0 < (P[H.indicator (1 : Ω → ℝ) |
        MeasurableSpace.comap (localModConstPairings α₀ hC (closure (ball w r))ᶜ) inferInstance]) ω

/-- **Lemma 11.18 for every geometry of concentric disks**, conditioning on the field outside `W̄₀`
modulo additive constants, with no hypothesis. -/
theorem massDiamModConst_holds : MassDiamModConstStmt.{u} := by
  intro c₀ ρU ρV ρO hρU hUV hVO w r hOW _ hW1 γ α₀ ξ hγ0 hγ2 hα Ω _ P hC hcirc μ D hGFF hμ hDm
    c ε hc hε
  have : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  have hρV : 0 < ρV := hρU.trans hUV
  set δ : ℝ := ρO - ρV with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hδ2 : 0 < δ / 2 := by linarith
  set U : Set ℂ := ball c₀ ρU with hUdef
  set V : Set ℂ := ball c₀ ρV with hVdef
  have hclV : closure V = closedBall c₀ ρV := closure_ball c₀ hρV.ne'
  have hO : thickening δ (closure V) = ball c₀ ρO := by
    rw [hclV, thickening_closedBall hδ hρV.le]
    congr 1
    rw [hδdef]
    ring
  have hr : 0 < r := by
    have hc₀ : c₀ ∈ ball w r :=
      hOW (subset_closure (mem_ball_self (hρV.trans hVO)))
    exact dist_nonneg.trans_lt (mem_ball.1 hc₀)
  have hUV' : U ⊆ V := ball_subset_ball hUV.le
  have hx0 : c₀ ∈ U := mem_ball_self hρU
  have hUo : IsOpen U := isOpen_ball
  have hUc : IsConnected U := (convex_ball c₀ ρU).isConnected (nonempty_ball.2 hρU)
  have hUb : Bornology.IsBounded U := isBounded_ball
  have hcV : Convex ℝ (closure V) := (convex_ball c₀ ρV).closure
  have hVb : Bornology.IsBounded (closure V) := isBounded_ball.closure
  have hVcpt : IsCompact (closure V) := isBounded_ball.isCompact_closure
  have hV'o : IsOpen (thickening (δ / 2) (closure V)) := isOpen_thickening
  have hO1o : IsOpen (thickening δ (closure V)) := isOpen_thickening
  have hV'c : IsConnected (thickening (δ / 2) (closure V)) :=
    (hcV.thickening (δ / 2)).isConnected ⟨c₀, self_subset_thickening hδ2 _ (subset_closure (hUV' hx0))⟩
  have hO1c : IsConnected (thickening δ (closure V)) :=
    (hcV.thickening δ).isConnected ⟨c₀, self_subset_thickening hδ _ (subset_closure (hUV' hx0))⟩
  have hV'b : Bornology.IsBounded (thickening (δ / 2) (closure V)) := hVb.thickening
  have hO1b : Bornology.IsBounded (thickening δ (closure V)) := hVb.thickening
  have hUV'' : U ⊆ thickening (δ / 2) (closure V) := fun x hx =>
    self_subset_thickening hδ2 _ (subset_closure (hUV' hx))
  have hclV' : closure V ⊆ thickening (δ / 2) (closure V) := self_subset_thickening hδ2 _
  have hV'O1 : thickening (δ / 2) (closure V) ⊆ thickening δ (closure V) :=
    thickening_mono (by linarith) _
  have hcl : closure (thickening (δ / 2) (closure V)) ⊆ thickening δ (closure V) :=
    (closure_thickening_subset_cthickening (δ / 2) (closure V)).trans
      (cthickening_subset_thickening' hδ (by linarith) _)
  have hO1W : closure (thickening δ (closure V)) ⊆ ball w r := by rw [hO]; exact hOW
  have hO1W' : thickening δ (closure V) ⊆ ball w r := subset_closure.trans hO1W
  have hdisj : Disjoint (thickening δ (closure V)) (sphere (0 : ℂ) 1) := hW1.mono_left hO1W'
  -- Proposition 11.9 on the disks `U ⊆ V' ⊆ O`
  have hε' : 0 < min (ε / 2) ((c + 1) / 2) := lt_min (by linarith) (by linarith)
  have hε'C : min (ε / 2) ((c + 1) / 2) < c + 1 :=
    lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨A, hAsub, -, hAp⟩ := firstPass_11_9_derived γ α₀ ξ hγ0 hγ2 hα Ω P hC hcirc μ D hGFF hμ hDm
    U (thickening (δ / 2) (closure V)) (thickening δ (closure V))
    hUo hUc hUb hV'o hV'c hV'b hO1o hO1c hO1b hUV'' hV'O1 hcl hdisj (c + 1) _ hε' hε'C
  -- inner versions of the mass and of the internal diameter
  have hUO1 : closure U ⊆ thickening δ (closure V) :=
    (closure_mono hUV').trans (self_subset_thickening hδ _)
  obtain ⟨g1, hg1m, hg1⟩ := lqgMassInnerMeasurable_derived' γ α₀ Ω P hC hcirc μ hGFF hγ0 hγ2 hα hμ
    (thickening δ (closure V)) U hO1o hUo hUb hUO1
  obtain ⟨g2, hg2m, hg2⟩ := lqgInternalDiamInnerMeasurableFrozen_derived γ ξ α₀ Ω P hC hcirc D hGFF
    hγ0 hγ2 hα hDm δ (closure V) hδ hVcpt
  have hbad : ∀ᵐ ω ∂P, μ ω U = g1 ω ∧ internalDiam (D ω) δ (closure V) = g2 ω := hg1.and hg2
  obtain ⟨N0, hN0sub, hN0m, hN0null⟩ := exists_measurable_superset_of_null (ae_iff.1 hbad)
  set E : Set Ω := {ω | ENNReal.ofReal c < g1 ω ∧ g2 ω < ENNReal.ofReal ε} with hE
  have hEm : MeasurableSet[fieldSigmaAlgebra α₀ hC (thickening δ (closure V))] E :=
    (measurableSet_lt measurable_const hg1m).inter (measurableSet_lt hg2m measurable_const)
  have hEm0 : MeasurableSet E := (hGFF.fieldSigmaAlgebra_le α₀ (thickening δ (closure V))) _ hEm
  have hgoodOf : ∀ ω, ω ∉ N0 → μ ω U = g1 ω ∧ internalDiam (D ω) δ (closure V) = g2 ω :=
    fun ω hN => by
      by_contra hb
      exact hN (hN0sub hb)
  -- the mass-diameter event `E \ N₀` and its positivity
  have hAH : A ⊆ (E ∩ N0ᶜ) ∪ N0 := by
    intro ω hωA
    by_cases hN : ω ∈ N0
    · exact Or.inr hN
    · left
      have hgood := hgoodOf ω hN
      obtain ⟨hb1, hb2⟩ := hAsub hωA
      have hdiam : internalDiam (D ω) δ (closure V) ≤ ENNReal.ofReal (min (ε / 2) ((c + 1) / 2)) :=
        iSup₂_le fun x hx => iSup₂_le fun y hy => hb1 x (hclV' hx) y (hclV' hy)
      have hlt1 : ENNReal.ofReal (min (ε / 2) ((c + 1) / 2)) < ENNReal.ofReal ε :=
        (ENNReal.ofReal_lt_ofReal_iff hε).2 (lt_of_le_of_lt (min_le_left _ _) (by linarith))
      have h1 : ENNReal.ofReal c < g1 ω := by
        rw [← hgood.1]
        exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)) hb2
      have h2 : g2 ω < ENNReal.ofReal ε := by
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
  have hcond := domainMarkovConditionalPositive_holds α₀ Ω P hC hcirc hGFF (ball w r)
    (thickening δ (closure V)) ⟨w, r, hr, rfl⟩ hO1o hO1W E hEm hEpos
  refine ⟨E ∩ N0ᶜ, hEm0.inter hN0m.compl, ?_, hHpos, ?_⟩
  · rintro ω ⟨⟨h1, h2⟩, hnN⟩
    have hgood := hgoodOf ω hnN
    refine ⟨hgood.1 ▸ h1, ?_⟩
    have hsup : (⨆ x ∈ closure V, ⨆ y ∈ closure V, internalMetric (D ω) (ball c₀ ρO) x y) =
        internalDiam (D ω) δ (closure V) := by
      rw [internalDiam, hO]
    rw [hsup, hgood.2]
    exact h2
  · have hae : ∀ᵐ ω ∂P, ω ∉ N0 := by
      rw [ae_iff]
      simpa using hN0null
    have hcongr : (E ∩ N0ᶜ).indicator (1 : Ω → ℝ) =ᵐ[P] E.indicator (1 : Ω → ℝ) := by
      filter_upwards [hae] with ω hω
      by_cases h : ω ∈ E
      · simp [Set.indicator, h, hω]
      · simp [Set.indicator, h]
    filter_upwards [condExp_congr_ae hcongr, hcond] with ω h2 h1
    rw [h2]
    exact h1

end HarmonicBalls
