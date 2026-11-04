import HarmonicBalls.Proofs.Sec5.RestrictedContainmentTest

/-! # Field-local stopped families on arbitrary open sets -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

universe u

/-- Compact containment and the corresponding regularized family member have
field-local representatives on any open set, simultaneously over all centres
in the set and positive times. The field locality input is proposed and awaits
source review. -/
theorem exists_local_lqg_open_stoppedFamily_representative
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc)
    {U : Set ℂ} (hU : IsOpen U)
    {Λ : Ω → ℂ → ℝ → Set ℂ}
    (hΛ : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (μ ω) (Λ ω z) z) :
    ∃ E : Ω → (U × Ioi (0 : ℝ) → Prop),
      ∃ G : Ω → (U × Ioi (0 : ℝ) → Set ℂ),
        Measurable[fieldSigmaAlgebra α₀ hC U] E ∧
        Measurable[fieldSigmaAlgebra α₀ hC U] G ∧
        ∀ᵐ ω ∂P, ∀ p, (E ω p ↔ closure (Λ ω p.1 p.2) ⊆ U) ∧
          (E ω p → G ω p = Λ ω p.1 p.2) ∧
          (¬ E ω p → G ω p = ∅) := by
  classical
  let V : ℕ → Set ℂ := fun n => U ∩ ball 0 ((n : ℝ) + 1)
  have hVopen (n : ℕ) : IsOpen (V n) := hU.inter isOpen_ball
  have hVbounded (n : ℕ) : Bornology.IsBounded (V n) :=
    isBounded_ball.subset inter_subset_right
  have hVsub (n : ℕ) : V n ⊆ U := inter_subset_left
  choose E G hE hG hEq using fun n : ℕ =>
    exists_local_lqg_bounded_stoppedFamily_representative hI2 hγ hγ2 hα
      hGFF hμ hloc (hVopen n) (hVbounded n) hΛ
  let J := U × Ioi (0 : ℝ)
  let T : ℕ → Ω → J → Prop := fun n ω p =>
    if hp : (p.1 : ℂ) ∈ V n then E n ω (⟨p.1, hp⟩, p.2) else False
  let H : ℕ → Ω → J → Set ℂ := fun n ω p =>
    if hp : (p.1 : ℂ) ∈ V n then G n ω (⟨p.1, hp⟩, p.2) else ∅
  have hT (n : ℕ) : Measurable[fieldSigmaAlgebra α₀ hC U] (T n) := by
    let : MeasurableSpace Ω := fieldSigmaAlgebra α₀ hC U
    apply Measurable.of_eval
    intro p
    by_cases hp : (p.1 : ℂ) ∈ V n
    · simpa only [T, dite_eq_left hp, Function.comp_def] using
        (measurable_pi_apply (⟨(p.1 : ℂ), hp⟩, p.2)).comp
          ((hE n).mono (fieldSigmaAlgebra_mono α₀ hC (hVsub n)) le_rfl)
    · simpa only [T, dite_eq_right hp] using (measurable_const : Measurable (fun _ : Ω => False))
  have hH (n : ℕ) : Measurable[fieldSigmaAlgebra α₀ hC U] (H n) := by
    let : MeasurableSpace Ω := fieldSigmaAlgebra α₀ hC U
    apply Measurable.of_eval
    intro p
    by_cases hp : (p.1 : ℂ) ∈ V n
    · simpa only [H, dite_eq_left hp, Function.comp_def] using
        (measurable_pi_apply (⟨(p.1 : ℂ), hp⟩, p.2)).comp
          ((hG n).mono (fieldSigmaAlgebra_mono α₀ hC (hVsub n)) le_rfl)
    · simpa only [H, dite_eq_right hp] using
        (measurable_const : Measurable (fun _ : Ω => (∅ : Set ℂ)))
  let E' : Ω → J → Prop := fun ω p => ∃ n, T n ω p
  let G' : Ω → J → Set ℂ := fun ω p => {x | ∃ n, T n ω p ∧ x ∈ H n ω p}
  have hE' : Measurable[fieldSigmaAlgebra α₀ hC U] E' := by
    let : MeasurableSpace Ω := fieldSigmaAlgebra α₀ hC U
    apply Measurable.of_eval
    intro p
    apply Measurable.exists
    intro n
    exact (measurable_pi_apply p).comp (hT n)
  have hG' : Measurable[fieldSigmaAlgebra α₀ hC U] G' := by
    let : MeasurableSpace Ω := fieldSigmaAlgebra α₀ hC U
    apply Measurable.of_eval
    intro p
    apply Measurable.of_eval
    intro x
    apply Measurable.exists
    intro n
    exact ((measurable_pi_apply p).comp (hT n)).and
      ((measurable_pi_apply x).comp ((measurable_pi_apply p).comp (hH n)))
  refine ⟨E', G', hE', hG', ?_⟩
  filter_upwards [ae_all_iff.mpr hEq, hΛ] with ω hEqω hΛω
  intro p
  have hstep : ∀ n, T n ω p → closure (Λ ω p.1 p.2) ⊆ V n ∧
      H n ω p = Λ ω p.1 p.2 := by
    intro n hn
    by_cases hp : (p.1 : ℂ) ∈ V n
    · have he := hEqω n (⟨p.1, hp⟩, p.2)
      have hEn : E n ω (⟨p.1, hp⟩, p.2) := by simpa only [T, dite_eq_left hp] using hn
      exact ⟨he.1.mp hEn, by simpa only [H, dite_eq_left hp] using he.2 hEn⟩
    · simp only [T, dite_eq_right hp] at hn
  have hEchar : E' ω p ↔ closure (Λ ω p.1 p.2) ⊆ U := by
    constructor
    · rintro ⟨n, hn⟩
      exact (hstep n hn).1.trans (hVsub n)
    · intro hcl
      obtain ⟨r, hr⟩ := (((hΛω p.1).1.isBounded p.2 p.2.property).closure).subset_ball (0 : ℂ)
      obtain ⟨n, hn⟩ := exists_nat_gt r
      have hrn : r ≤ (n : ℝ) + 1 := by linarith
      have hclV : closure (Λ ω p.1 p.2) ⊆ V n :=
        fun x hx => ⟨hcl hx, ball_subset_ball hrn (hr hx)⟩
      have hp : (p.1 : ℂ) ∈ V n := hclV (subset_closure ((hΛω p.1).1.mem p.2 p.2.property))
      refine ⟨n, ?_⟩
      simpa only [T, dite_eq_left hp] using (hEqω n (⟨p.1, hp⟩, p.2)).1.mpr hclV
  refine ⟨hEchar, ?_, ?_⟩
  · intro hgood
    ext x
    constructor
    · rintro ⟨n, hn, hx⟩
      exact (hstep n hn).2 ▸ hx
    · intro hx
      obtain ⟨n, hn⟩ := hgood
      exact ⟨n, hn, (hstep n hn).2.symm ▸ hx⟩
  · intro hbad
    ext x
    simp only [G', mem_ofPred_eq, mem_empty_iff_false, iff_false]
    rintro ⟨n, hn, _⟩
    exact hbad ⟨n, hn⟩

/-- Hausdorff continuity preserves compact containment for a short time. -/
theorem exists_later_compact_containment_of_hausdorffContinuousOn
    {A : ℝ → Set ℂ} {U : Set ℂ} (hU : IsOpen U) {t : ℝ} (ht : 0 < t)
    (hbounded : Bornology.IsBounded (A t))
    (hcont : HausdorffContinuousOn A (Ioi 0))
    (hsub : closure (A t) ⊆ U) :
    ∃ s : ℝ, t < s ∧ closure (A s) ⊆ U := by
  have hK : IsCompact (closure (A t)) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hbounded.closure
  obtain ⟨ε, hε, hεsub⟩ := hK.exists_thickening_subset_open hU hsub
  have hnear : ∀ᶠ s in 𝓝 t, hausdorffEDist (A s) (A t) < ENNReal.ofReal ε := by
    have h := hcont t ht (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
    rwa [nhdsWithin_eq_nhds.mpr (isOpen_Ioi.mem_nhds ht)] at h
  obtain ⟨δ, hδ, hδbound⟩ := Metric.eventually_nhds_iff.mp hnear
  let s := t + δ / 2
  have hts : t < s := by dsimp [s]; linarith
  have hsnear : dist s t < δ := by
    dsimp [s, Real.dist_eq]
    rw [add_sub_cancel_left, abs_of_pos (half_pos hδ)]
    linarith
  refine ⟨s, hts, fun x hx => ?_⟩
  have hdist : hausdorffEDist (closure (A s)) (closure (A t)) < ENNReal.ofReal ε := by
    simpa only [hausdorffEDist_closure] using hδbound hsnear
  obtain ⟨y, hy, hxy⟩ := exists_edist_lt_of_hausdorffEDist_lt hx hdist
  apply hεsub
  apply mem_thickening_iff.mpr
  refine ⟨y, hy, ?_⟩
  simpa only [edist_dist, ENNReal.ofReal_lt_ofReal_iff hε] using hxy

/-- The supremum of compact-containment times is field-local on an arbitrary
open set. Its strict lower cuts are characterized by later compact
containment, without any finiteness assumption on the horizon. -/
theorem exists_fieldLocal_open_containment_horizons
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc)
    {U : Set ℂ} (hU : IsOpen U)
    {Λ : Ω → ℂ → ℝ → Set ℂ}
    (hΛ : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (μ ω) (Λ ω z) z) :
    ∃ H : Ω → (U → ℝ≥0∞), Measurable[fieldSigmaAlgebra α₀ hC U] H ∧
      ∀ᵐ ω ∂P, ∀ z : U, ∀ t : ℝ, 0 < t →
        (ENNReal.ofReal t < H ω z ↔ ∃ s : ℝ, t < s ∧ closure (Λ ω z s) ⊆ U) := by
  classical
  obtain ⟨E, G, hE, hG, heq⟩ := exists_local_lqg_open_stoppedFamily_representative
    hI2 hγ hγ2 hα hGFF hμ hloc hU hΛ
  let Q := {q : ℚ // 0 < (q : ℝ)}
  let H : Ω → (U → ℝ≥0∞) := fun ω z => ⨆ q : Q,
    if E ω (z, ⟨q, q.property⟩) then ENNReal.ofReal q else 0
  have hH : Measurable[fieldSigmaAlgebra α₀ hC U] H := by
    let : MeasurableSpace Ω := fieldSigmaAlgebra α₀ hC U
    apply Measurable.of_eval
    intro z
    apply Measurable.iSup
    intro q
    apply Measurable.ite _ measurable_const measurable_const
    have hm : Measurable (fun ω => E ω (z, ⟨(q : ℚ), q.property⟩)) :=
      (measurable_pi_apply (z, (⟨(q : ℚ), q.property⟩ : Ioi (0 : ℝ)))).comp hE
    exact hm.setOf
  refine ⟨H, hH, ?_⟩
  filter_upwards [heq, hΛ] with ω heqω hΛω
  intro z t ht
  constructor
  · intro hlt
    change ENNReal.ofReal t < ⨆ q : Q,
      if E ω (z, ⟨q, q.property⟩) then ENNReal.ofReal q else 0 at hlt
    obtain ⟨q, hq⟩ := lt_iSup_iff.mp hlt
    by_cases hgood : E ω (z, ⟨q, q.property⟩)
    · rw [ite_eq_left hgood] at hq
      exact ⟨q, (ENNReal.ofReal_lt_ofReal_iff q.property).mp hq,
        ((heqω _).1).mp hgood⟩
    · rw [ite_eq_right hgood] at hq
      exact False.elim ((not_lt_of_ge bot_le) hq)
  · rintro ⟨s, hts, hs⟩
    obtain ⟨q, htq, hqs⟩ := exists_rat_btwn hts
    let q' : Q := ⟨q, lt_trans ht htq⟩
    have hqinside : closure (Λ ω z q) ⊆ U :=
      (closure_mono ((hΛω z).1.monotoneOn q'.property (lt_trans ht hts) hqs.le)).trans hs
    have hgood : E ω (z, ⟨q', q'.property⟩) := ((heqω _).1).mpr hqinside
    have hle : ENNReal.ofReal (q : ℝ) ≤ H ω z :=
      le_iSup_of_le q' (by simp [hgood, q'])
    exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff q'.property).mpr htq) hle

/-- Compact containment holds exactly at times strictly before a field-local
horizon, with no boundedness assumption on the open domain or on the horizon. -/
theorem exists_fieldLocal_open_exact_containment_horizons
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc)
    {U : Set ℂ} (hU : IsOpen U)
    {Λ : Ω → ℂ → ℝ → Set ℂ}
    (hΛ : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (μ ω) (Λ ω z) z) :
    ∃ H : Ω → (U → ℝ≥0∞), Measurable[fieldSigmaAlgebra α₀ hC U] H ∧
      ∀ᵐ ω ∂P, ∀ z : U, ∀ t : ℝ, 0 < t →
        (ENNReal.ofReal t < H ω z ↔ closure (Λ ω z t) ⊆ U) := by
  obtain ⟨H, hH, hchar⟩ := exists_fieldLocal_open_containment_horizons
    hI2 hγ hγ2 hα hGFF hμ hloc hU hΛ
  refine ⟨H, hH, ?_⟩
  filter_upwards [hchar, hΛ] with ω hcharω hΛω
  intro z t ht
  rw [hcharω z t ht]
  constructor
  · rintro ⟨s, hts, hs⟩
    exact (closure_mono ((hΛω z).1.monotoneOn ht (lt_trans ht hts) hts.le)).trans hs
  · intro hsub
    exact exists_later_compact_containment_of_hausdorffContinuousOn hU ht
      ((hΛω z).1.isBounded t ht) (hΛω z).1.hausdorffContinuousOn hsub

end HarmonicBalls
