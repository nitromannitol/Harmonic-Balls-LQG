import HarmonicBalls.Draft.Section6

/-!
# Localization: comparable measures and the flat weight (steps S-Flat, S-Transfer)

The deterministic steps used to obtain the
printed `α₀`-uniform constants of Lemmas 6.3 and 6.6 from their `α₀ = 0` instances.

* S-Transfer. Two measures `μ`, `ν` are *comparable on `B`* (`IsComparableOn μ ν B c`) if `c ν ≤ μ ≤ 4c ν` on subsets
  of `B`, for some `c ∈ (0, ∞)`. The good annulus event `E_r(z; a, b)` (eq:good-annulus-harmonic, lines 1115-1123)
  uses the measure only on `𝔸_{3r,5r}(z)` and only through mass ratios, so `E_r(z; a, b)[ν] ⊆ E_r(z; a/4, b)[μ]`
  when `𝔸_{3r,5r}(z) ⊆ B` (`isGoodAnnulus_of_comparable`). The very good annulus event `Ē_ρ(x₀)` (lines 1144-1157)
  uses the measure only on `B_{2ρ}(x₀)` once `N₀ ≥ 5`, through the ratios `M_ρ/μ(𝔸_{ρ/4,2ρ})`,
  `SG_ρ/μ(𝔸_{ρ/4,2ρ})` and good annuli, so it transfers with `(a, C₁^±, C₂^±) ↦ (a/4, C₁⁻/4, 4C₁⁺, C₂⁻/4, 4C₂⁺)`
  (`isVeryGoodAnnulus_of_comparable`).
* S-Flat. On a ball `B_R(x₀)` with `2R ≤ |x₀|` and `|e| · 4R/|x₀| ≤ log 2`, the weight `|x|^e` lies within a factor
  `2` of `|x₀|^e` (`rpow_norm_flat`). With the Weyl identity `μ_h = |x|^{-γα₀} μ_{h^ℂ}` on `ℂ \ {0}`
  (`SingularWeightStep`), this makes `μ_h` and `μ_{h^ℂ}` comparable on such balls (`isComparableOn_of_withDensity`).
-/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped ENNReal

namespace Section6

/-! ## Comparable measures -/

/-- `μ` and `ν` are comparable on `B` with constant `c ∈ (0, ∞)`: `c ν ≤ μ ≤ 4 c ν` on subsets of `B`. -/
structure IsComparableOn (μ ν : Measure ℂ) (B : Set ℂ) (c : ℝ≥0∞) : Prop where
  ne_zero : c ≠ 0
  ne_top : c ≠ ⊤
  lower : c • ν.restrict B ≤ μ.restrict B
  upper : μ.restrict B ≤ (4 * c) • ν.restrict B

variable {μ ν : Measure ℂ} {B : Set ℂ} {c : ℝ≥0∞} {x₀ : ℂ} {ρ : ℝ}

theorem IsComparableOn.le_apply (h : IsComparableOn μ ν B c) {s : Set ℂ} (hs : s ⊆ B) : c * ν s ≤ μ s := by
  have := h.lower s
  rwa [Measure.smul_apply, Measure.restrict_eq_self _ hs, Measure.restrict_eq_self _ hs, smul_eq_mul] at this

theorem IsComparableOn.apply_le (h : IsComparableOn μ ν B c) {s : Set ℂ} (hs : s ⊆ B) :
    μ s ≤ 4 * c * ν s := by
  have := h.upper s
  rwa [Measure.smul_apply, Measure.restrict_eq_self _ hs, Measure.restrict_eq_self _ hs, smul_eq_mul] at this

theorem IsComparableOn.mono (h : IsComparableOn μ ν B c) {B' : Set ℂ} (hB : B' ⊆ B) :
    IsComparableOn μ ν B' c where
  ne_zero := h.ne_zero
  ne_top := h.ne_top
  lower := by
    have := Measure.restrict_mono (subset_refl B') h.lower
    rwa [Measure.restrict_smul, Measure.restrict_restrict_of_subset hB,
      Measure.restrict_restrict_of_subset hB] at this
  upper := by
    have := Measure.restrict_mono (subset_refl B') h.upper
    rwa [Measure.restrict_smul, Measure.restrict_restrict_of_subset hB,
      Measure.restrict_restrict_of_subset hB] at this

theorem ofReal_div_four_mul_four (a : ℝ) : ENNReal.ofReal (a / 4) * 4 = ENNReal.ofReal a := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat,
    ENNReal.div_mul_cancel (by norm_num) (by norm_num)]

/-- S-Transfer for the good annulus event. -/
theorem isGoodAnnulus_of_comparable (h : IsComparableOn μ ν B c) {r a b : ℝ} {z : ℂ}
    (hA : annulus z (3 * r) (5 * r) ⊆ B) (hg : IsGoodAnnulus ν r z a b) :
    IsGoodAnnulus μ r z (a / 4) b := by
  intro Y hY hYA hmass u hu
  refine hg Y hY hYA ?_ u hu
  refine (ENNReal.mul_le_mul_iff_right h.ne_zero h.ne_top).1 ?_
  calc c * ν Y ≤ μ Y := h.le_apply (hYA.trans hA)
    _ ≤ ENNReal.ofReal (a / 4) * μ (annulus z (3 * r) (5 * r)) := hmass
    _ ≤ ENNReal.ofReal (a / 4) * (4 * c * ν (annulus z (3 * r) (5 * r))) := by
        gcongr; exact h.apply_le hA
    _ = c * (ENNReal.ofReal (a / 4) * 4 * ν (annulus z (3 * r) (5 * r))) := by ring
    _ = c * (ENNReal.ofReal a * ν (annulus z (3 * r) (5 * r))) := by rw [ofReal_div_four_mul_four a]

/-- Ratios of comparable quantities: `X/Y ∈ [lo, hi]` gives `X'/Y' ∈ [lo/4, 4 hi]`. -/
theorem ratio_mem_of_comparable {X X' Y Y' : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hX : c * X ≤ X') (hX' : X' ≤ 4 * c * X) (hY : c * Y ≤ Y') (hY' : Y' ≤ 4 * c * Y) {lo hi : ℝ}
    (h : X / Y ∈ Icc (ENNReal.ofReal lo) (ENNReal.ofReal hi)) :
    X' / Y' ∈ Icc (ENNReal.ofReal (lo / 4)) (ENNReal.ofReal (4 * hi)) := by
  have h4 : (4 : ℝ≥0∞) ≠ 0 := by norm_num
  have h4' : (4 : ℝ≥0∞) ≠ ⊤ := by norm_num
  constructor
  · calc ENNReal.ofReal (lo / 4) = ENNReal.ofReal lo / 4 := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat]
      _ ≤ X / Y / 4 := ENNReal.div_le_div_right h.1 4
      _ = c * X / (c * (4 * Y)) := by
          rw [ENNReal.mul_div_mul_left _ _ hc0 hct, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
            ENNReal.mul_inv (Or.inl h4) (Or.inl h4'), mul_comm (4 : ℝ≥0∞)⁻¹ Y⁻¹, mul_assoc]
      _ ≤ X' / Y' := ENNReal.div_le_div hX (hY'.trans_eq (by ring))
  · calc X' / Y' ≤ 4 * c * X / (c * Y) := ENNReal.div_le_div hX' hY
      _ = 4 * (X / Y) := by
          rw [mul_comm (4 : ℝ≥0∞) c, mul_assoc, ENNReal.mul_div_mul_left _ _ hc0 hct, mul_div_assoc]
      _ ≤ 4 * ENNReal.ofReal hi := by gcongr; exact h.2
      _ = ENNReal.ofReal (4 * hi) := by rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

/-- `M_ρ(x₀)` under comparable measures on `B_{2ρ}(x₀)`. -/
theorem annulusBallMassSize_comparable (h : IsComparableOn μ ν (ball x₀ (2 * ρ)) c) (hρ : 0 < ρ)
    (β : ℝ) : c * annulusBallMassSize ν β ρ x₀ ≤ annulusBallMassSize μ β ρ x₀ ∧
      annulusBallMassSize μ β ρ x₀ ≤ 4 * c * annulusBallMassSize ν β ρ x₀ := by
  have hsub : ∀ z ∈ annulus x₀ (ρ / 2) ρ, ∀ r ∈ Ioo 0 (ρ / 4), ball z r ⊆ ball x₀ (2 * ρ) := by
    intro z hz r hr
    refine ball_subset_ball' ?_
    have := mem_ball.1 hz.1
    linarith [hr.2]
  have h4c0 : 4 * c ≠ 0 := mul_ne_zero (by norm_num) h.ne_zero
  have h4ct : 4 * c ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) h.ne_top
  constructor
  · refine le_iInf₂ fun z hz => le_iInf₂ fun r hr => ?_
    calc c * annulusBallMassSize ν β ρ x₀ ≤ c * (ν (ball z r) / ENNReal.ofReal ((r / ρ) ^ β)) := by
          gcongr; exact iInf₂_le_of_le z hz (iInf₂_le r hr)
      _ = c * ν (ball z r) / ENNReal.ofReal ((r / ρ) ^ β) := (mul_div_assoc _ _ _).symm
      _ ≤ μ (ball z r) / ENNReal.ofReal ((r / ρ) ^ β) :=
          ENNReal.div_le_div_right (h.le_apply (hsub z hz r hr)) _
  · unfold annulusBallMassSize
    simp_rw [ENNReal.mul_iInf_of_ne h4c0 h4ct]
    refine iInf₂_mono fun z hz => iInf₂_mono fun r hr => ?_
    calc μ (ball z r) / ENNReal.ofReal ((r / ρ) ^ β) ≤
        4 * c * ν (ball z r) / ENNReal.ofReal ((r / ρ) ^ β) :=
          ENNReal.div_le_div_right (h.apply_le (hsub z hz r hr)) _
      _ = 4 * c * (ν (ball z r) / ENNReal.ofReal ((r / ρ) ^ β)) := mul_div_assoc _ _ _

/-- `SG` under comparable measures on a set containing the annulus. -/
theorem annulusGreenPotentialSup_comparable {s₁ s₂ : ℝ}
    (h : IsComparableOn μ ν (annulus x₀ s₁ s₂) c) :
    c * annulusGreenPotentialSup ν x₀ s₁ s₂ ≤ annulusGreenPotentialSup μ x₀ s₁ s₂ ∧
      annulusGreenPotentialSup μ x₀ s₁ s₂ ≤ 4 * c * annulusGreenPotentialSup ν x₀ s₁ s₂ := by
  unfold annulusGreenPotentialSup
  constructor
  · simp_rw [ENNReal.mul_iSup]
    refine iSup₂_mono fun x _ => ?_
    rw [← smul_eq_mul c, ← lintegral_smul_measure]
    exact lintegral_mono' h.lower le_rfl
  · simp_rw [ENNReal.mul_iSup]
    refine iSup₂_mono fun x _ => ?_
    rw [← smul_eq_mul (4 * c), ← lintegral_smul_measure]
    exact lintegral_mono' h.upper le_rfl

/-- A set of radii `≥ lo > 0` of the form `A q^k`, `q < 1`, is finite. -/
theorem finite_of_geometric {q A lo : ℝ} (hq0 : 0 ≤ q) (hq : q < 1) (hlo : 0 < lo) {S : Set ℝ}
    (hS : ∀ r ∈ S, lo ≤ r ∧ ∃ k : ℕ, r = A * q ^ k) : S.Finite := by
  have ht : Filter.Tendsto (fun k : ℕ => A * q ^ k) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq).const_mul A
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (ht.eventually (gt_mem_nhds hlo))
  refine ((Set.finite_Iio N).image fun k : ℕ => A * q ^ k).subset fun r hr => ?_
  obtain ⟨hlo', k, rfl⟩ := hS r hr
  refine ⟨k, mem_Iio.2 (lt_of_not_ge fun hk => ?_), rfl⟩
  linarith [hN k hk]

/-- `√(2^{-n}) ≤ 1/5` for `n ≥ 5`. -/
theorem sqrt_dyadicScale_le {n : ℕ} (hn : 5 ≤ n) : Real.sqrt (dyadicScale n) ≤ 1 / 5 := by
  rw [Real.sqrt_le_left (by norm_num)]
  unfold dyadicScale
  calc (2 : ℝ)⁻¹ ^ n ≤ (2 : ℝ)⁻¹ ^ 5 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    _ ≤ (1 / 5) ^ 2 := by norm_num

/-- S-Transfer for the very good annulus event, for `N₀ ≥ 5`. -/
theorem isVeryGoodAnnulus_of_comparable (h : IsComparableOn μ ν (ball x₀ (2 * ρ)) c) (hρ : 0 < ρ)
    {β : ℝ} {N₀ : ℕ} (hN₀ : 5 ≤ N₀) {a b C₁m C₁p C₂m C₂p C₃ : ℝ}
    (hv : IsVeryGoodAnnulus ν β ρ x₀ N₀ a b C₁m C₁p C₂m C₂p C₃) :
    IsVeryGoodAnnulus μ β ρ x₀ N₀ (a / 4) b (C₁m / 4) (4 * C₁p) (C₂m / 4) (4 * C₂p) C₃ := by
  obtain ⟨hv1, hv2, hv3⟩ := hv
  have hA : annulus x₀ (ρ / 4) (2 * ρ) ⊆ ball x₀ (2 * ρ) := sdiff_subset
  have hM := annulusBallMassSize_comparable h hρ β
  have hSG := annulusGreenPotentialSup_comparable (h.mono hA)
  refine ⟨ratio_mem_of_comparable h.ne_zero h.ne_top hM.1 hM.2 (h.le_apply hA) (h.apply_le hA) hv1,
    ratio_mem_of_comparable h.ne_zero h.ne_top hSG.1 hSG.2 (h.le_apply hA) (h.apply_le hA) hv2,
    fun n hn z hz hlat => ?_⟩
  have hε : 0 < dyadicScale n := by unfold dyadicScale; positivity
  have hsq := sqrt_dyadicScale_le (hN₀.trans hn)
  refine (hv3 n hn z hz hlat).trans ?_
  norm_cast
  refine Set.ncard_le_ncard (fun r hr => ⟨hr.1, hr.2.1, ?_⟩) ?_
  · refine isGoodAnnulus_of_comparable h ?_ hr.2.2
    refine sdiff_subset.trans (ball_subset_ball' ?_)
    have h1 := mem_ball.1 hz.1
    have h2 := hr.1.2
    have h3 : Real.sqrt (dyadicScale n) * ρ ≤ 1 / 5 * ρ := mul_le_mul_of_nonneg_right hsq hρ.le
    linarith
  · refine finite_of_geometric (q := (7 : ℝ)⁻¹) (A := ρ) (lo := dyadicScale n * ρ) (by norm_num)
      (by norm_num) (by positivity) fun r hr => ⟨hr.1.1, ?_⟩
    obtain ⟨k, -, hk⟩ := hr.2.1
    exact ⟨k, hk⟩

/-! ## The flat weight (S-Flat) -/

/-- S-Flat: on `B_R(x₀)` with `2R ≤ |x₀|` and `|e| · 4R/|x₀| ≤ log 2`, `|x₀|^e/2 ≤ |x|^e ≤ 2 |x₀|^e`. -/
theorem rpow_norm_flat {x₀ x : ℂ} {R e : ℝ} (hR : 0 ≤ R) (h2R : 2 * R ≤ ‖x₀‖) (hx₀ : x₀ ≠ 0)
    (he : |e| * (4 * R / ‖x₀‖) ≤ Real.log 2) (hx : x ∈ ball x₀ R) :
    ‖x₀‖ ^ e / 2 ≤ ‖x‖ ^ e ∧ ‖x‖ ^ e ≤ 2 * ‖x₀‖ ^ e := by
  set n := ‖x₀‖ with hn_def
  have hn : 0 < n := norm_pos_iff.2 hx₀
  have hd : |‖x‖ - n| < R := (abs_norm_sub_norm_le x x₀).trans_lt (by rw [← dist_eq_norm]; exact hx)
  have hd' := abs_lt.1 hd
  set q := R / n with hq_def
  have hq : 0 ≤ q := div_nonneg hR hn.le
  have hq2 : q ≤ 1 / 2 := by rw [hq_def, div_le_iff₀ hn]; linarith
  set t := ‖x‖ / n with ht_def
  have htn : ‖x‖ = t * n := by rw [ht_def, div_mul_cancel₀ _ hn.ne']
  have ht1 : t - 1 < q := by
    rw [ht_def, hq_def, div_sub_one hn.ne', div_lt_div_iff_of_pos_right hn]; linarith
  have ht2 : -q < t - 1 := by
    rw [ht_def, hq_def, div_sub_one hn.ne', ← neg_div, div_lt_div_iff_of_pos_right hn]; linarith
  have ht0 : 0 < t := by linarith
  have hlog_hi : Real.log t ≤ 2 * q := by linarith [Real.log_le_sub_one_of_pos ht0]
  have hlog_lo : -(2 * q) ≤ Real.log t := by
    refine le_trans ?_ (Real.one_sub_inv_le_log_of_pos ht0)
    have : 1 - t⁻¹ = (t - 1) / t := by field_simp [ht0.ne']
    rw [this, le_div_iff₀ ht0]
    nlinarith [mul_nonneg hq (by linarith : (0 : ℝ) ≤ 2 * t - 1)]
  have hel : |Real.log t * e| ≤ Real.log 2 := by
    rw [abs_mul]
    have h1 : |Real.log t| ≤ 2 * q := abs_le.2 ⟨hlog_lo, hlog_hi⟩
    have h2 : |e| * (4 * R / n) = 2 * (|e| * (2 * q)) := by rw [hq_def]; ring
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith [abs_nonneg e, abs_nonneg (Real.log t), mul_le_mul_of_nonneg_right h1 (abs_nonneg e)]
  have htpow : t ^ e = Real.exp (Real.log t * e) := Real.rpow_def_of_pos ht0 e
  have hup : t ^ e ≤ 2 := by
    rw [htpow]
    calc Real.exp (Real.log t * e) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 (abs_le.1 hel).2
      _ = 2 := Real.exp_log (by norm_num)
  have hlo : 1 / 2 ≤ t ^ e := by
    rw [htpow]
    calc (1 : ℝ) / 2 = Real.exp (-Real.log 2) := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
      _ ≤ Real.exp (Real.log t * e) := Real.exp_le_exp.2 (by linarith [(abs_le.1 hel).1])
  have hne : 0 < n ^ e := Real.rpow_pos_of_pos hn e
  rw [htn, Real.mul_rpow ht0.le hn.le]
  constructor <;> nlinarith

/-- Comparability of `μ` with `ν` on `B` from `μ = w ν` on `B` and `w(p)/2 ≤ w ≤ 2 w(p)` on `B`. -/
theorem isComparableOn_of_withDensity {w : ℂ → ℝ≥0∞} (hB : MeasurableSet B)
    (hμ : μ.restrict B = (ν.withDensity w).restrict B) {p : ℂ} (hp0 : w p ≠ 0) (hpt : w p ≠ ⊤)
    (hw : ∀ x ∈ B, w p / 2 ≤ w x ∧ w x ≤ 2 * w p) : IsComparableOn μ ν B (w p / 2) where
  ne_zero := ENNReal.div_ne_zero.2 ⟨hp0, by norm_num⟩
  ne_top := ENNReal.div_ne_top hpt (by norm_num)
  lower := by
    rw [hμ, Measure.le_iff]
    intro s hs
    rw [Measure.smul_apply, Measure.restrict_apply hs, Measure.restrict_apply hs,
      withDensity_apply _ (hs.inter hB), smul_eq_mul, ← setLIntegral_const]
    exact setLIntegral_mono' (hs.inter hB) fun x hx => (hw x hx.2).1
  upper := by
    rw [hμ, Measure.le_iff]
    intro s hs
    rw [Measure.smul_apply, Measure.restrict_apply hs, Measure.restrict_apply hs,
      withDensity_apply _ (hs.inter hB), smul_eq_mul, ← setLIntegral_const]
    refine setLIntegral_mono' (hs.inter hB) fun x hx => (hw x hx.2).2.trans_eq ?_
    rw [show (4 : ℝ≥0∞) * (w p / 2) = 2 * (w p / 2 * 2) by ring,
      ENNReal.div_mul_cancel (by norm_num) (by norm_num)]

/-- The singular weight `|x|^{-γα₀}` is flat on balls far from the origin: comparability of `μ_h` with
`μ_{h^ℂ}` on `B_R(x₀)` from the Weyl identity on `ℂ \ {0}`. -/
theorem isComparableOn_ball_of_weight {μ₀ : Measure ℂ} {e R : ℝ} {x₀ : ℂ} (hR : 0 < R)
    (h2R : 2 * R ≤ ‖x₀‖) (he : |e| * (4 * R / ‖x₀‖) ≤ Real.log 2)
    (hμ : μ.restrict {0}ᶜ = (μ₀.withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)).restrict {0}ᶜ) :
    IsComparableOn μ μ₀ (ball x₀ R) (ENNReal.ofReal (‖x₀‖ ^ e) / 2) := by
  have hx₀ : x₀ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at h2R; linarith
  have hB0 : ball x₀ R ⊆ {0}ᶜ := by
    intro x hx h0
    rw [mem_singleton_iff] at h0
    rw [h0, mem_ball, dist_comm, dist_zero_right] at hx
    linarith
  have hBμ : μ.restrict (ball x₀ R) =
      (μ₀.withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)).restrict (ball x₀ R) := by
    rw [← Measure.restrict_restrict_of_subset hB0, hμ, Measure.restrict_restrict_of_subset hB0]
  have hpos : 0 < ‖x₀‖ ^ e := Real.rpow_pos_of_pos (norm_pos_iff.2 hx₀) e
  refine isComparableOn_of_withDensity (p := x₀) isOpen_ball.measurableSet hBμ
    (ENNReal.ofReal_pos.2 hpos).ne' ENNReal.ofReal_ne_top fun x hx => ?_
  obtain ⟨h1, h2⟩ := rpow_norm_flat hR.le h2R hx₀ he hx
  constructor
  · rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_div_of_pos (by norm_num)]
    exact ENNReal.ofReal_le_ofReal h1
  · rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal h2

end Section6

end HarmonicBalls
