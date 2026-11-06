import HarmonicBalls.Proofs.Sec6.ScaleUniformRelativeCollar
import HarmonicBalls.Proofs.Sec6.UniformSingularGoodAnnulus
import HarmonicBalls.Proofs.Sec6.SingularRootAnnulusRegularity

/-! # Good-annulus counts for singularly weighted measures

The underlying fine-support argument uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. The imported zero-strength
existence input is staged pending source review.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal
universe u

/-- The singular and zero-strength LQG measures of the same field satisfy
the power-weight relation needed for the annulus transfer. -/
theorem ae_singular_lqg_eq_power_weight
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ μ₀ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμ₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀) :
    ∀ᵐ ω ∂P, μ ω = (μ₀ ω).withDensity
      (fun z => ENNReal.ofReal (‖z‖ ^ (-(γ * α)))) := by
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨_, _, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hgrowth hγ hγ2 hα h hμ
  obtain ⟨_, _, hV₀⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hgrowth hγ hγ2 hQ h hμ₀
  have hW := lqgMeasureWeylScaling Ω P γ 0 hC hcirc
  filter_upwards [hV, hV₀, hμ, hW h hγ hγ2 hQ μ₀ hμ₀] with ω hV hV₀ hm hw
  have hz : μ ω {0} = 0 := (hV.2 1 (by norm_num)).measure_singleton (by simp)
  have hz₀ : μ₀ ω {0} = 0 := (hV₀.2 1 (by norm_num)).measure_singleton (by simp)
  exact eq_singularWeight_of_origin_nonatomic hm hw hz hz₀

open Classical in
/-- On a separated size annulus, each good zero-strength annulus transfers to
a nearby good singular-weighted annulus unless its singular collar estimate
fails. Both weight-distortion losses are explicit. -/
theorem exists_singular_goodAnnulus_count_le
    {η : ℝ} (hη : 0 < η) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (μ ν : Measure ℂ) (r : ℕ → ℝ) (s : Finset ℕ)
      (ρ e : ℝ) (z w x₀ : ℂ), 0 < ρ → (∀ i ∈ s, 0 < r i) →
      (∀ i ∈ s, dist w z < δ * r i) →
      ∀ a a' amid b b' : ℝ, ∀ d : ℝ≥0∞,
      (∀ i ∈ s, 0 < ν (annulus z (3*r i) (5*r i))) →
      (∀ i ∈ s, ν (annulus z (3*r i) (5*r i)) ≠ ∞) →
      ENNReal.ofReal b + 2 * ε + ε ≤ ENNReal.ofReal b' →
      ENNReal.ofReal amid < ENNReal.ofReal a →
      ENNReal.ofReal a' + (ENNReal.ofReal a' + 1) *
        (ENNReal.ofReal (((401 : ℝ) ^ |e|) ^ 2) * d) ≤ ENNReal.ofReal amid →
      ρ / 100 ≤ infDist (0 : ℂ) (annulus x₀ (ρ / 4) (2*ρ)) →
      μ.restrict {0}ᶜ = (ν.withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)).restrict {0}ᶜ →
      (∀ i ∈ s, annulus z (3*r i) (5*r i) ⊆ annulus x₀ (ρ/4) (2*ρ)) →
      (∀ i ∈ s, annulus z (3*r i-η*r i) (5*r i+η*r i) ⊆ annulus x₀ (ρ/4) (2*ρ)) →
      (∀ i ∈ s, r i / 100 ≤ infDist (0 : ℂ) (annulus w (3*r i) (5*r i))) →
      (s.filter fun i => IsGoodAnnulus ν (r i) z a b).card ≤
      (s.filter fun i => IsGoodAnnulus μ (r i) w (a' / ((1001 : ℝ) ^ |e|) ^ 2) b').card +
      (s.filter fun i => d * μ (annulus z (3*r i) (5*r i)) <
        μ (annulus z (3*r i-η*r i) (5*r i+η*r i) \
          annulus z (3*r i+η*r i) (5*r i-η*r i))).card := by
  classical
  obtain ⟨δ, hδ, ht⟩ := exists_scale_uniform_goodAnnulus_of_singular_relative_collar hη hε
  refine ⟨δ, hδ, ?_⟩
  intro μ ν r s ρ e z w x₀ hρ hr hw a a' amid b b' d hpos hfin hbudget hmid hslack
    hdist hweight hA hO hwsep
  let G := s.filter fun i => IsGoodAnnulus ν (r i) z a b
  let H := s.filter fun i => IsGoodAnnulus μ (r i) w (a' / ((1001 : ℝ) ^ |e|) ^ 2) b'
  let B := s.filter fun i => d * μ (annulus z (3*r i) (5*r i)) <
    μ (annulus z (3*r i-η*r i) (5*r i+η*r i) \
      annulus z (3*r i+η*r i) (5*r i-η*r i))
  have hsub : G \ B ⊆ H := by
    intro i hi
    have hiG := (Finset.mem_sdiff.mp hi).1
    have hiB := (Finset.mem_sdiff.mp hi).2
    have his := (Finset.mem_filter.mp hiG).1
    have hig := (Finset.mem_filter.mp hiG).2
    have hcollar : μ (annulus z (3*r i-η*r i) (5*r i+η*r i) \
      annulus z (3*r i+η*r i) (5*r i-η*r i)) ≤
        d * μ (annulus z (3*r i) (5*r i)) := by
      apply le_of_not_gt
      intro hb
      exact hiB (Finset.mem_filter.mpr ⟨his, hb⟩)
    have hgood := ht μ ν (r i) ρ e (hr i his) hρ z w x₀ (hw i his)
      a a' amid b b' d (hpos i his) (hfin i his) hig hbudget hmid hslack
      hdist hweight (hA i his) (hO i his) hcollar
    exact Finset.mem_filter.mpr ⟨his,
      isGoodAnnulus_of_singular_weight (hr i his) (hwsep i his) hweight hgood⟩
  calc
    G.card ≤ (G \ B).card + B.card := Finset.card_le_card_sdiff_add_card
    _ ≤ H.card + B.card := Nat.add_le_add_right (Finset.card_le_card hsub) _

end HarmonicBalls.Section6
