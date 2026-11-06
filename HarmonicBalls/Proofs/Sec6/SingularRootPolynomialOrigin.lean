import HarmonicBalls.Proofs.Sec6.SingularRootOriginTail
import HarmonicBalls.Steps.Sec2.VolumeGrowth

/-! # Quantitative origin control for singular LQG roots

The imported annulus-count argument uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal
universe u

/-- A normalized root inherits a small-set bound outside an arbitrary field
exceptional set; the latter need not be measurable. -/
theorem normalized_root_measure_le_of_field_exception
    {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    (P : Measure Ω) [IsProbabilityMeasure P] (κ : Kernel Ω Z) [IsSFiniteKernel κ]
    (hκ : ∀ᵐ ω ∂P, κ ω univ = 1) (A : Set Z) (hA : MeasurableSet A)
    (E : Set Ω) (c : ℝ≥0∞)
    (hbound : ∀ᵐ ω ∂P, ω ∈ E → κ ω A ≤ c) :
    (P ⊗ₘ κ) (univ ×ˢ A) ≤ P Eᶜ + c := by
  let N := toMeasurable P Eᶜ
  have hN : MeasurableSet N := measurableSet_toMeasurable P Eᶜ
  have hsubset : Eᶜ ⊆ N := subset_toMeasurable P Eᶜ
  calc
    _ ≤ (P ⊗ₘ κ) (N ×ˢ univ) + (P ⊗ₘ κ) (Nᶜ ×ˢ A) := by
      apply (measure_mono ?_).trans (measure_union_le _ _)
      intro x hx
      by_cases hn : x.1 ∈ N
      · exact Or.inl ⟨hn, mem_univ _⟩
      · exact Or.inr ⟨hn, hx.2⟩
    _ = P Eᶜ + ∫⁻ ω in Nᶜ, κ ω A ∂P := by
      rw [Measure.compProd_apply_prod hN MeasurableSet.univ,
        Measure.compProd_apply_prod hN.compl hA]
      rw [lintegral_congr_ae (ae_restrict_of_ae hκ)]
      simp only [lintegral_one, Measure.restrict_apply_univ, N, measure_toMeasurable]
    _ ≤ P Eᶜ + c := by
      gcongr
      calc
        _ ≤ ∫⁻ _ω in Nᶜ, c ∂P := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_of_ae hbound, ae_restrict_mem hN.compl] with ω hb hω
          exact hb (by
            by_contra he
            exact hω (hsubset he))
        _ ≤ ∫⁻ _ω, c ∂P := lintegral_mono' Measure.restrict_le_self le_rfl
        _ = c := by simp


/-- The normalized mass of a small ball is controlled by an upper mass bound
at its radius and a lower mass bound at a larger radius. -/
theorem normalizedRestriction_ball_le_rpow
    (ν : Measure ℂ) {t a p q : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (ha : 0 < a)
    (hu : ν (ball 0 t) ≤ ENNReal.ofReal (t ^ p))
    (hl : ENNReal.ofReal ((t ^ a) ^ q) ≤ ν (ball 0 (t ^ a))) :
    normalizedRestriction ν (ball 0 1) (ball 0 t) ≤
      ENNReal.ofReal (t ^ (p - a * q)) := by
  have htapos : 0 < t ^ a := Real.rpow_pos_of_pos ht _
  have hta1 : t ^ a ≤ 1 := Real.rpow_le_one ht.le ht1 ha.le
  have hsub : ball (0 : ℂ) (t ^ a) ⊆ ball 0 1 := ball_subset_ball hta1
  have hl' : ENNReal.ofReal ((t ^ a) ^ q) ≤ ν (ball 0 1) := hl.trans (measure_mono hsub)
  have hsmall : ball (0 : ℂ) t ⊆ ball 0 1 := ball_subset_ball ht1
  rw [normalizedRestriction, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply measurableSet_ball, inter_eq_self_of_subset_left hsmall]
  calc
    _ ≤ (ENNReal.ofReal ((t ^ a) ^ q))⁻¹ * ENNReal.ofReal (t ^ p) := by
      exact mul_le_mul' (ENNReal.inv_le_inv.mpr hl') hu
    _ = ENNReal.ofReal (t ^ (p - a * q)) := by
      rw [← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos htapos _),
        ← ENNReal.ofReal_mul (inv_nonneg.mpr (Real.rpow_nonneg htapos.le _)),
        ← Real.rpow_mul ht.le, ← Real.rpow_neg ht.le,
        ← Real.rpow_add ht, neg_add_eq_sub]

/-- A polynomially high probability estimate remains polynomial under a
positive power change of scale. -/
theorem polyHighProb_comp_rpow {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {E : ℝ → Set Ω} (h : PolyHighProb P E) {a : ℝ} (ha : 0 < a) :
    PolyHighProb P (fun t => E (t ^ a)) := by
  obtain ⟨p, hp, C, r₀, hr₀, hE⟩ := h
  refine ⟨a * p, mul_pos ha hp, C, r₀ ^ a⁻¹,
    Real.rpow_pos_of_pos hr₀ _, fun t ht htr => ?_⟩
  have hta : t ^ a < r₀ := by
    calc
      t ^ a < (r₀ ^ a⁻¹) ^ a := Real.rpow_lt_rpow ht.le htr ha
      _ = r₀ := by rw [← Real.rpow_mul hr₀.le, inv_mul_cancel₀ ha.ne', Real.rpow_one]
  simpa only [← Real.rpow_mul ht.le] using hE (t ^ a) (Real.rpow_pos_of_pos ht _) hta

/-- Polynomial ball-mass bounds imply a polynomial small-ball bound for a
singular LQG root sampled from normalized mass in the unit disk. -/
theorem singular_unitDisc_root_origin_polynomial_bound
    (hball : LiouvilleBallMassBoundStep.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    {bp bm a : ℝ} (hbp : 0 < bp)
    (hbp' : bp < min ((2 - γ)^2 / 2) (γ * (lqgQ γ - α)))
    (hbm : max ((2 + γ)^2 / 2) (γ * (lqgQ γ - α)) < bm)
    (ha : 0 < a) (ha' : a * bm < bp) :
    ∃ k : ℝ, 0 < k ∧ ∃ C : ℝ, 0 < C ∧ ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ t : ℝ, 0 < t → t < t₀ →
        (P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
          (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const)
          (univ ×ˢ ball (0 : ℂ) t) ≤ ENNReal.ofReal (C * t ^ k) := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  let hm := h.aemeasurable_lqgMeasure hμ
  let κ := weightedRestrictionKernel P μ hm (ball 0 1) measurableSet_ball
    (fun _ => 1) measurable_const
  have hgrowth := lqgVolumeGrowthAllScalesStmt_of_ballMass hball
  have hfull := lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth γ α hγ hγ2 hα
    Ω P hC hcirc μ h hμ
  have hmass : ∀ᵐ ω ∂P, ((μ ω).withDensity (fun _ => 1)) (ball 0 1) ≠ 0 ∧
      ((μ ω).withDensity (fun _ => 1)) (ball 0 1) ≠ ∞ := by
    filter_upwards [hfull, hμ] with ω hf hloc
    let : IsLocallyFiniteMeasure (μ ω) := hloc.isLocallyFiniteMeasure
    simpa only [withDensity_const, one_smul] using
      (show μ ω (ball 0 1) ≠ 0 ∧ μ ω (ball 0 1) ≠ ∞ from
        ⟨(hf _ isOpen_ball ⟨0, mem_ball_self (by norm_num)⟩).ne', measure_ball_ne_top⟩)
  have hk : ∀ᵐ ω ∂P, κ ω univ = 1 := by
    filter_upwards [ae_weightedRestrictionKernel_eq P μ hm (ball 0 1) measurableSet_ball
      (fun _ => 1) measurable_const, hmass] with ω he hh
    rw [he]
    simp only [normalizedRestriction, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel hh.1 hh.2
  have hpoly := hball γ α hγ hγ2 hα Ω P hC hcirc μ h hμ 1 one_pos bp bm hbp hbp' hbm
  obtain ⟨p, hp, C, t₀, ht₀, hE⟩ := hpoly.inter (polyHighProb_comp_rpow hpoly ha)
  refine ⟨min p (bp - a * bm), lt_min hp (sub_pos.mpr ha'),
    max C 0 + 1, by positivity, min t₀ 1, lt_min ht₀ one_pos, ?_⟩
  intro t ht ht₀'
  have ht1 : t ≤ 1 := (ht₀'.trans_le (min_le_right _ _)).le
  have ht₀'' : t < t₀ := ht₀'.trans_le (min_le_left _ _)
  have htpos : 0 < t ^ (bp - a * bm) := Real.rpow_pos_of_pos ht _
  have hfield : ∀ᵐ ω ∂P,
      ω ∈ ballMassBoundEvent μ 1 bp bm t ∩ ballMassBoundEvent μ 1 bp bm (t ^ a) →
        κ ω (ball 0 t) ≤ ENNReal.ofReal (t ^ (bp - a * bm)) := by
    filter_upwards [ae_weightedRestrictionKernel_eq P μ hm (ball 0 1) measurableSet_ball
      (fun _ => 1) measurable_const] with ω he hω
    rw [he, withDensity_const, one_smul]
    exact normalizedRestriction_ball_le_rpow (μ ω) ht ht1 ha
      ((hω.1 0 (mem_ball_self one_pos)).2) ((hω.2 0 (mem_ball_self one_pos)).1)
  have hroot := normalized_root_measure_le_of_field_exception P κ hk (ball 0 t)
    measurableSet_ball _ _ hfield
  have htp : t ^ p ≤ t ^ min p (bp - a * bm) :=
    Real.rpow_le_rpow_of_exponent_ge ht ht1 (min_le_left _ _)
  have htk : t ^ (bp - a * bm) ≤ t ^ min p (bp - a * bm) :=
    Real.rpow_le_rpow_of_exponent_ge ht ht1 (min_le_right _ _)
  calc
    _ ≤ P (ballMassBoundEvent μ 1 bp bm t ∩ ballMassBoundEvent μ 1 bp bm (t ^ a))ᶜ +
        ENNReal.ofReal (t ^ (bp - a * bm)) := hroot
    _ ≤ ENNReal.ofReal (max C 0 * t ^ min p (bp - a * bm)) +
        ENNReal.ofReal (t ^ min p (bp - a * bm)) := by
      apply add_le_add
      · exact (hE t ht ht₀'').trans (ENNReal.ofReal_le_ofReal
          (mul_le_mul (le_max_left _ _) htp (Real.rpow_nonneg ht.le _) (le_max_right _ _)))
      · exact ENNReal.ofReal_le_ofReal htk
    _ = ENNReal.ofReal ((max C 0 + 1) * t ^ min p (bp - a * bm)) := by
      rw [← ENNReal.ofReal_add (by positivity) (Real.rpow_nonneg ht.le _)]
      congr 1
      ring

/-- The polynomial origin bound holds for every subcritical singularity. -/
theorem exists_singular_unitDisc_root_origin_polynomial_bound
    (hball : LiouvilleBallMassBoundStep.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ) :
    ∃ k : ℝ, 0 < k ∧ ∃ C : ℝ, 0 < C ∧ ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ t : ℝ, 0 < t → t < t₀ →
        (P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
          (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const)
          (univ ×ˢ ball (0 : ℂ) t) ≤ ENNReal.ofReal (C * t ^ k) := by
  let L := min ((2 - γ)^2 / 2) (γ * (lqgQ γ - α))
  let U := max ((2 + γ)^2 / 2) (γ * (lqgQ γ - α))
  have hL : 0 < L := by
    dsimp [L]
    exact lt_min (by positivity) (mul_pos hγ (sub_pos.mpr hα))
  have hU : 0 < U := by
    dsimp [U]
    exact lt_of_lt_of_le (by positivity : 0 < (2 + γ)^2 / 2) (le_max_left _ _)
  have hbm : 0 < U + 1 := by linarith
  apply singular_unitDisc_root_origin_polynomial_bound hball hγ hγ2 hα h hμ
    (bp := L / 2) (bm := U + 1) (a := (L / 2) / (2 * (U + 1)))
  · positivity
  · change L / 2 < L
    linarith
  · change U < U + 1
    linarith
  · positivity
  · have : ((L / 2) / (2 * (U + 1))) * (U + 1) = L / 4 := by
      field_simp
      ring
    rw [this]
    linarith

/-- A polynomial origin estimate removes the separation error from the
singular-measure good-annulus count tail. -/
theorem exists_singular_unitDisc_root_goodAnnuli_polynomial_tail
    (hball : LiouvilleBallMassBoundStep.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ μ₀ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμ₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀)
    {b : ℝ} (hb : 0 < b) (β : ℝ) (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ q : ℝ, 0 < q ∧ ∃ a ∈ Ioo (0 : ℝ) 1,
    ∀ s : ℝ, 0 < s → ∃ C : ℝ, 0 < C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ → 16 ≤ Real.logb 7 (ε ^ (-1 : ℝ)) →
      (P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
        (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const)
        {p | ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
          IsGoodAnnulus (μ p.1) (s * r) p.2
            (a / ((1001 : ℝ) ^ |-(γ * α)|) ^ 2) (b + 1)}.ncard : ℝ) <
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} ≤ ENNReal.ofReal (C * ε ^ q) := by
  let hgrowth := lqgVolumeGrowthAllScalesStmt_of_ballMass hball
  obtain ⟨k, hk, D, hD, t₀, ht₀, hnear⟩ :=
    exists_singular_unitDisc_root_origin_polynomial_bound hball hγ hγ2 hα h hμ
  have hq : 0 < (3 / 4 : ℝ) * k := mul_pos (by norm_num) hk
  obtain ⟨a, ha, htail⟩ := exists_singular_unitDisc_root_separated_goodAnnuli_polynomial_tail
    hgrowth hγ hγ2 hα h hμ hμ₀ hb ((3 / 4 : ℝ) * k) β hq hβ
  refine ⟨_, hq, a, ha, ?_⟩
  intro s hs
  obtain ⟨C, hC, htail⟩ := htail s hs
  obtain ⟨ε₁, hε₁, hsmall⟩ := exists_pos_forall_rpow_le
    (a := (3 / 4 : ℝ)) (c := t₀ / (12 * s)) (by norm_num) (by positivity)
  refine ⟨C + D * (6 * s) ^ k, by positivity, min ε₁ 1, lt_min hε₁ one_pos, ?_⟩
  intro ε hε hε₀ hlog
  have hε1 : ε ≤ 1 := (hε₀.trans_le (min_le_right _ _)).le
  have hscale : 0 < 6 * s * ε ^ (3 / 4 : ℝ) := by positivity
  have hscale' : 6 * s * ε ^ (3 / 4 : ℝ) < t₀ := by
    have hh := hsmall ε hε (hε₀.trans_le (min_le_left _ _))
    have hs' : 0 < 12 * s := by positivity
    have hh' := (le_div_iff₀ hs').mp hh
    nlinarith
  have hn := hnear (6 * s * ε ^ (3 / 4 : ℝ)) hscale hscale'
  have hn' : (P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
        (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const)
        {p | ‖p.2‖ < 6 * s * ε ^ (3 / 4 : ℝ)} ≤
      ENNReal.ofReal (D * (6 * s) ^ k * ε ^ ((3 / 4 : ℝ) * k)) := by
    have heq : (univ ×ˢ ball (0 : ℂ) (6 * s * ε ^ (3 / 4 : ℝ))) =
        {p : Ω × ℂ | ‖p.2‖ < 6 * s * ε ^ (3 / 4 : ℝ)} := by
      ext p
      simp only [mem_prod, mem_univ, true_and, mem_ball, dist_zero_right, mem_ofPred_eq]
    rw [heq] at hn
    convert hn using 1
    rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hε.le _),
      ← Real.rpow_mul hε.le]
    ring_nf
  calc
    _ ≤ (P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
        (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const)
        {p | ‖p.2‖ < 6 * s * ε ^ (3 / 4 : ℝ)} +
      (P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
        (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const)
        {p | 6 * s * ε ^ (3 / 4 : ℝ) ≤ ‖p.2‖ ∧
          ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
            (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
            IsGoodAnnulus (μ p.1) (s * r) p.2
              (a / ((1001 : ℝ) ^ |-(γ * α)|) ^ 2) (b + 1)}.ncard : ℝ) <
          (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} := by
      apply (measure_mono ?_).trans (measure_union_le _ _)
      intro p hp
      by_cases hz : ‖p.2‖ < 6 * s * ε ^ (3 / 4 : ℝ)
      · exact Or.inl hz
      · exact Or.inr ⟨le_of_not_gt hz, hp⟩
    _ ≤ ENNReal.ofReal (D * (6 * s) ^ k * ε ^ ((3 / 4 : ℝ) * k)) +
      ENNReal.ofReal (C * ε ^ ((3 / 4 : ℝ) * k)) :=
        add_le_add hn' (htail ε _ hε hε1 hlog le_rfl)
    _ = ENNReal.ofReal ((C + D * (6 * s) ^ k) * ε ^ ((3 / 4 : ℝ) * k)) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

end HarmonicBalls.Section6
