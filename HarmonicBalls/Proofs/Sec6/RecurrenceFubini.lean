import HarmonicBalls.Proofs.Sec6.MeasureEvaluation

/-! # Almost-everywhere joint measurability in the fine-support recurrence argument -/

namespace HarmonicBalls.Section6
open MeasureTheory

/-- The positive recurrence conclusion holds for almost every sample and almost
every spatial point when the ratios are jointly almost everywhere measurable.
Positivity and the lower-tail identities need only hold for almost every point. -/
theorem ae_ae_frequently_pos_of_equal_lower_tails_of_aemeasurable
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) [IsFiniteMeasure P] (ν : Measure Ξ) [SFinite ν]
    (X : ℕ → Ω × Ξ → ℝ) (hX : ∀ n, AEMeasurable (X n) (P.prod ν))
    (hpos : ∀ᵐ x ∂ν, ∀ᵐ ω ∂P, 0 < X 0 (ω, x))
    (hlaw : ∀ᵐ x ∂ν, ∀ n a, P {ω | X n (ω, x) < a} = P {ω | X 0 (ω, x) < a}) :
    ∀ᵐ ω ∂P, ∀ᵐ x ∂ν, ∃ a : ℝ, 0 < a ∧ ∀ N : ℕ, ∃ n ≥ N, a ≤ X n (ω, x) := by
  let Y : ℕ → Ω × Ξ → ℝ := fun n => (hX n).mk (X n)
  have hYm : ∀ n, Measurable (Y n) := fun n => (hX n).measurable_mk
  have heq : ∀ᵐ z ∂P.prod ν, ∀ n, Y n z = X n z := by
    apply ae_all_iff.2
    intro n
    exact (hX n).ae_eq_mk.symm
  have heqωx : ∀ᵐ ω ∂P, ∀ᵐ x ∂ν, ∀ n, Y n (ω, x) = X n (ω, x) :=
    Measure.ae_ae_of_ae_prod heq
  have heqxω : ∀ᵐ x ∂ν, ∀ᵐ ω ∂P, ∀ n, Y n (ω, x) = X n (ω, x) := by
    have hswap : ∀ᵐ z ∂ν.prod P, ∀ n, Y n (z.2, z.1) = X n (z.2, z.1) :=
      (Measure.measurePreserving_swap (μ := ν) (ν := P)).quasiMeasurePreserving.ae heq
    exact Measure.ae_ae_of_ae_prod hswap
  have hrec : ∀ᵐ x ∂ν, ∀ᵐ ω ∂P,
      ∃ a : ℝ, 0 < a ∧ ∀ N : ℕ, ∃ n ≥ N, a ≤ Y n (ω, x) := by
    filter_upwards [hpos, hlaw, heqxω] with x hpx hlx hex
    have hYm0 : Measurable (fun ω => Y 0 (ω, x)) :=
      (hYm 0).comp (measurable_id.prodMk measurable_const)
    have hYpos : ∀ᵐ ω ∂P, 0 < Y 0 (ω, x) := by
      filter_upwards [hpx, hex] with ω hp he
      rw [he 0]
      exact hp
    have hYlaw : ∀ n a, P {ω | Y n (ω, x) < a} = P {ω | Y 0 (ω, x) < a} := by
      intro n a
      have hmeasure (k : ℕ) : P {ω | Y k (ω, x) < a} = P {ω | X k (ω, x) < a} := by
        apply measure_congr
        filter_upwards [hex] with ω he
        simp only [he k]
      rw [hmeasure n, hmeasure 0, hlx n a]
    exact ae_frequently_pos_of_equal_lower_tails P (fun n ω => Y n (ω, x))
      hYm0 hYpos hYlaw
  have hrec' : ∀ᵐ ω ∂P, ∀ᵐ x ∂ν,
      ∃ a : ℝ, 0 < a ∧ ∀ N : ℕ, ∃ n ≥ N, a ≤ Y n (ω, x) :=
    (Measure.ae_ae_comm (measurableSet_frequently_pos Y hYm)).2 hrec
  filter_upwards [hrec', heqωx] with ω hω heω
  filter_upwards [hω, heω] with x hx hex
  obtain ⟨a, ha, hf⟩ := hx
  refine ⟨a, ha, fun N => ?_⟩
  obtain ⟨n, hn, hval⟩ := hf N
  exact ⟨n, hn, hval.trans (hex n).le⟩

/-- The Green-potential infimum-to-supremum ratio on a domain and a test set. -/
noncomputable def greenPotentialExtremaRatio (O K : Set ℂ) (μ : Measure ℂ) : ℝ :=
  ((⨅ z : K, ENNReal.ofReal (greenPotential O μ z)) /
    (⨆ z : O, ENNReal.ofReal (greenPotential O μ z))).toReal

universe u

/-- If a sequence of LQG potential ratios has the same lower tails, then it is
frequently bounded below by a positive constant almost surely. -/
theorem ae_frequently_lqg_potential_ratio_of_equal_lower_tails
    (hholder : GreenPotentialHolderStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hnonatom : LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc)
    (O K : ℕ → Set ℂ) (hO : IsSmoothBoundedOpen (O 0))
    (hK : IsCompact (K 0)) (hKne : (K 0).Nonempty) (hKO : K 0 ⊆ O 0)
    (R : ℝ) (hR : 0 < R) (hOR : O 0 ⊆ Metric.ball 0 R)
    (hlaw : ∀ n a, P {ω | greenPotentialExtremaRatio (O n) (K n) (μ ω) < a} =
      P {ω | greenPotentialExtremaRatio (O 0) (K 0) (μ ω) < a}) :
    ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧ ∀ N : ℕ, ∃ n ≥ N,
      a ≤ greenPotentialExtremaRatio (O n) (K n) (μ ω) := by
  have hmeas : AEMeasurable (fun ω => greenPotentialExtremaRatio (O 0) (K 0) (μ ω)) P := by
    simpa only [greenPotentialExtremaRatio] using
      aemeasurable_lqg_greenPotential_ratio_of_locality hholder hγ hγ2 hα hGFF hμ hloc
        hO (hKO.trans subset_closure)
  have hpos : ∀ᵐ ω ∂P, 0 < greenPotentialExtremaRatio (O 0) (K 0) (μ ω) := by
    filter_upwards [ae_lqg_greenPotential_extrema_ratio_pos hholder hfull hgrowth
      hγ hγ2 hα hGFF hμ hnonatom] with ω hω
    simpa only [greenPotentialExtremaRatio] using hω (O 0) hO R hR hOR (K 0) hK hKne hKO
  exact ae_frequently_pos_of_equal_lower_tails_of_aemeasurable P
    (fun n ω => greenPotentialExtremaRatio (O n) (K n) (μ ω)) hmeas hpos hlaw

/-- Under joint almost-everywhere measurability and equal lower tails, LQG
potential ratios are frequently positive simultaneously for almost every
spatial parameter. -/
theorem ae_ae_frequently_lqg_potential_ratio_of_equal_lower_tails
    (hholder : GreenPotentialHolderStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {Ξ : Type*} [MeasurableSpace Ξ] (ν : Measure Ξ) [SFinite ν]
    {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hnonatom : LQGMeasureNonatomic P γ α₀ hC hcirc)
    (O K : ℕ → Ξ → Set ℂ)
    (hgeom : ∀ x, IsSmoothBoundedOpen (O 0 x) ∧ IsCompact (K 0 x) ∧
      (K 0 x).Nonempty ∧ K 0 x ⊆ O 0 x ∧
      ∃ R : ℝ, 0 < R ∧ O 0 x ⊆ Metric.ball 0 R)
    (hjoint : ∀ n, AEMeasurable
      (fun p : Ω × Ξ => greenPotentialExtremaRatio (O n p.2) (K n p.2) (μ p.1))
      (P.prod ν))
    (hlaw : ∀ᵐ x ∂ν, ∀ n a,
      P {ω | greenPotentialExtremaRatio (O n x) (K n x) (μ ω) < a} =
      P {ω | greenPotentialExtremaRatio (O 0 x) (K 0 x) (μ ω) < a}) :
    ∀ᵐ ω ∂P, ∀ᵐ x ∂ν, ∃ a : ℝ, 0 < a ∧ ∀ N : ℕ, ∃ n ≥ N,
      a ≤ greenPotentialExtremaRatio (O n x) (K n x) (μ ω) := by
  apply ae_ae_frequently_pos_of_equal_lower_tails_of_aemeasurable P ν
    (fun n p => greenPotentialExtremaRatio (O n p.2) (K n p.2) (μ p.1)) hjoint ?_ hlaw
  filter_upwards [] with x
  obtain ⟨ho, hk, hkne, hko, R, hr, hor⟩ := hgeom x
  filter_upwards [ae_lqg_greenPotential_extrema_ratio_pos hholder hfull hgrowth
    hγ hγ2 hα hGFF hμ hnonatom] with ω hω
  simpa only [greenPotentialExtremaRatio] using hω (O 0 x) ho R hr hor (K 0 x) hk hkne hko

end HarmonicBalls.Section6
