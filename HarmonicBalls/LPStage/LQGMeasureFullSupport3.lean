import Mathlib
import HarmonicBalls.LPStage.GFF
import HarmonicBalls.LPStage.LQGMeasure
import HarmonicBalls.LPStage.LQGMeasureFullSupport2

/-!
# LP stage: full support of the LQG measure, part 3 (z3, task `fp-lpstage-lqg-full-support-then-square-positive`, R57)

LP port of the elementary closure properties of `PolyHighProb` used by the full-support chain
(`HarmonicBalls/Proofs/Sec2/PolyHighProb.lean`): monotonicity, linear reparametrization of the scale, finite intersections,
the union bound over dyadic scales (`dyadic_tail`) and the Borel-Cantelli lemma along the dyadic scales.
All statements use the LP predicate `LatticeProb.Gauss.PolyHighProb`.
-/

open MeasureTheory ProbabilityTheory Metric Filter Set Topology
open scoped ENNReal
open LatticeProb.Gauss

namespace LatticeProb.LQG

section PolyHighProbAlgebra

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E F : ℝ → Set Ω}

/-- An event containing, at all small scales, an event of polynomially high probability has polynomially high
probability (`Proofs/Sec2/PolyHighProb.lean:23`). -/
theorem polyHighProb_mono_of_small_lp (h : PolyHighProb P E) {r₁ : ℝ} (hr₁ : 0 < r₁)
    (hEF : ∀ r, 0 < r → r < r₁ → E r ⊆ F r) : PolyHighProb P F := by
  obtain ⟨p, hp, C, r₀, hr₀, hE⟩ := h
  refine ⟨p, hp, C, min r₀ r₁, lt_min hr₀ hr₁, fun r hr hrr => ?_⟩
  calc P (F r)ᶜ ≤ P (E r)ᶜ :=
        measure_mono (compl_subset_compl.2 (hEF r hr (hrr.trans_le (min_le_right _ _))))
    _ ≤ _ := hE r hr (hrr.trans_le (min_le_left _ _))

theorem polyHighProb_mono_lp (h : PolyHighProb P E) (hEF : ∀ r, E r ⊆ F r) : PolyHighProb P F :=
  polyHighProb_mono_of_small_lp h one_pos fun r _ _ => hEF r

/-- Linear reparametrization of the scale: `ε ↦ E(c ε)` for a constant `c > 0`. -/
theorem polyHighProb_comp_mul_lp (h : PolyHighProb P E) {c : ℝ} (hc : 0 < c) :
    PolyHighProb P fun r => E (c * r) := by
  obtain ⟨p, hp, C, r₀, hr₀, hE⟩ := h
  refine ⟨p, hp, C * c ^ p, r₀ / c, div_pos hr₀ hc, fun r hr hrr => ?_⟩
  have hcr : c * r < r₀ := by rwa [lt_div_iff₀ hc, mul_comm] at hrr
  calc P (E (c * r))ᶜ ≤ ENNReal.ofReal (C * (c * r) ^ p) := hE _ (mul_pos hc hr) hcr
    _ = ENNReal.ofReal (C * c ^ p * r ^ p) := by rw [Real.mul_rpow hc.le hr.le, mul_assoc]

/-- The intersection of two events of polynomially high probability. -/
theorem polyHighProb_inter_lp (hE : PolyHighProb P E) (hF : PolyHighProb P F) :
    PolyHighProb P fun r => E r ∩ F r := by
  obtain ⟨p, hp, C, r₀, hr₀, hE⟩ := hE
  obtain ⟨q, hq, D, s₀, hs₀, hF⟩ := hF
  refine ⟨min p q, lt_min hp hq, max C 0 + max D 0, min (min r₀ s₀) 1,
    lt_min (lt_min hr₀ hs₀) one_pos, fun r hr hrr => ?_⟩
  have hr₀' : r < r₀ := hrr.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hs₀' : r < s₀ := hrr.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hr1 : r < 1 := hrr.trans_le (min_le_right _ _)
  have hpr : r ^ p ≤ r ^ min p q := Real.rpow_le_rpow_of_exponent_ge hr hr1.le (min_le_left _ _)
  have hqr : r ^ q ≤ r ^ min p q := Real.rpow_le_rpow_of_exponent_ge hr hr1.le (min_le_right _ _)
  have hC : C * r ^ p ≤ max C 0 * r ^ min p q :=
    mul_le_mul (le_max_left _ _) hpr (by positivity) (le_max_right _ _)
  have hD : D * r ^ q ≤ max D 0 * r ^ min p q :=
    mul_le_mul (le_max_left _ _) hqr (by positivity) (le_max_right _ _)
  rw [compl_inter]
  calc P ((E r)ᶜ ∪ (F r)ᶜ) ≤ P (E r)ᶜ + P (F r)ᶜ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (C * r ^ p) + ENNReal.ofReal (D * r ^ q) :=
        add_le_add (hE r hr hr₀') (hF r hr hs₀')
    _ ≤ ENNReal.ofReal (max C 0 * r ^ min p q) + ENNReal.ofReal (max D 0 * r ^ min p q) :=
        add_le_add (ENNReal.ofReal_le_ofReal hC) (ENNReal.ofReal_le_ofReal hD)
    _ = ENNReal.ofReal ((max C 0 + max D 0) * r ^ min p q) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_mul]

/-- **Borel-Cantelli along the dyadic scales** (`Proofs/Sec2/PolyHighProb.lean:70`). If `E` has polynomially high
probability, then almost surely `ω ∈ E(2^{-k})` for all large `k`. -/
theorem polyHighProb_ae_eventually_dyadic_lp (h : PolyHighProb P E) :
    ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop, ω ∈ E ((2 : ℝ)⁻¹ ^ k) := by
  obtain ⟨p, hp, C, r₀, hr₀, hE⟩ := h
  obtain ⟨k₀, hk₀⟩ := exists_pow_lt_of_lt_one hr₀ (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hq : (2 : ℝ)⁻¹ ^ p < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hp
  have hterm : ∀ n : ℕ, P (E ((2 : ℝ)⁻¹ ^ (n + k₀)))ᶜ ≤
      ENNReal.ofReal (max C 0) * ENNReal.ofReal ((2 : ℝ)⁻¹ ^ p) ^ n := by
    intro n
    have hpos : 0 < (2 : ℝ)⁻¹ ^ (n + k₀) := by positivity
    have hlt : (2 : ℝ)⁻¹ ^ (n + k₀) < r₀ :=
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_left k₀ n)).trans_lt hk₀
    have hle : ((2 : ℝ)⁻¹ ^ (n + k₀)) ^ p ≤ ((2 : ℝ)⁻¹ ^ p) ^ n := by
      rw [← Real.rpow_pow_comm (by norm_num)]
      exact pow_le_pow_of_le_one (Real.rpow_nonneg (by norm_num) _) hq.le (Nat.le_add_right n k₀)
    calc P (E ((2 : ℝ)⁻¹ ^ (n + k₀)))ᶜ ≤ ENNReal.ofReal (C * ((2 : ℝ)⁻¹ ^ (n + k₀)) ^ p) :=
          hE _ hpos hlt
      _ ≤ ENNReal.ofReal (max C 0 * ((2 : ℝ)⁻¹ ^ p) ^ n) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul (le_max_left _ _) hle
            (by positivity) (le_max_right _ _))
      _ = _ := by
          rw [ENNReal.ofReal_mul (le_max_right _ _), ENNReal.ofReal_pow (by positivity)]
  have hsum : ∑' n : ℕ, P (E ((2 : ℝ)⁻¹ ^ (n + k₀)))ᶜ ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hterm)
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.2 ?_)
    exact (tsub_pos_of_lt (ENNReal.ofReal_lt_one.2 hq)).ne'
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  rw [eventually_atTop] at hω ⊢
  obtain ⟨N, hN⟩ := hω
  refine ⟨N + k₀, fun k hk => ?_⟩
  have h' := hN (k - k₀) (by omega)
  rw [Nat.sub_add_cancel (by omega : k₀ ≤ k)] at h'
  simpa using h'

/-- If `b < a`, then `C ε^a ≤ ε^b` for all small `ε > 0` (`Proofs/Sec2/PolyHighProb.lean:112`). -/
theorem eventually_mul_rpow_le_lp (C : ℝ) {a b : ℝ} (hab : b < a) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), C * ε ^ a ≤ ε ^ b := by
  have hC1 : (0 : ℝ) < max C 0 + 1 := by positivity
  obtain ⟨r₁, hr₁, h⟩ := exists_pos_forall_rpow_le_lp (sub_pos.2 hab) (inv_pos.2 hC1)
  filter_upwards [Ioo_mem_nhdsGT hr₁] with ε hε
  have hε0 : 0 < ε := hε.1
  have h1 : ε ^ (a - b) ≤ (max C 0 + 1)⁻¹ := h ε hε.1 hε.2
  have hsplit : ε ^ a = ε ^ (a - b) * ε ^ b := by rw [← Real.rpow_add hε0, sub_add_cancel]
  have hb : 0 < ε ^ b := Real.rpow_pos_of_pos hε0 _
  have hab' : 0 < ε ^ (a - b) := Real.rpow_pos_of_pos hε0 _
  rw [hsplit]
  calc C * (ε ^ (a - b) * ε ^ b) ≤ (max C 0 + 1) * (ε ^ (a - b) * ε ^ b) := by
        gcongr; exact (le_max_left C 0).trans (le_add_of_nonneg_right zero_le_one)
    _ ≤ (max C 0 + 1) * ((max C 0 + 1)⁻¹ * ε ^ b) := by gcongr
    _ = ε ^ b := by rw [← mul_assoc, mul_inv_cancel₀ hC1.ne', one_mul]

/-- If `a < b` and `c > 0`, then `ε^b ≤ c ε^a` for all small `ε > 0` (`Proofs/Sec2/PolyHighProb.lean:129`). -/
theorem eventually_rpow_le_mul_lp {c : ℝ} (hc : 0 < c) {a b : ℝ} (hab : a < b) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ b ≤ c * ε ^ a := by
  filter_upwards [eventually_mul_rpow_le_lp c⁻¹ hab] with ε hε
  calc ε ^ b = c * (c⁻¹ * ε ^ b) := by rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
    _ ≤ c * ε ^ a := by gcongr

/-- A property holding at all small scales along `𝓝[>] 0` holds on some interval `(0, r₁)`
(`Proofs/Sec2/PolyHighProb.lean:136`). -/
theorem exists_pos_of_eventually_nhdsGT_lp {p : ℝ → Prop} (h : ∀ᶠ r in 𝓝[>] (0 : ℝ), p r) :
    ∃ r₁ > 0, ∀ r : ℝ, 0 < r → r < r₁ → p r := by
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h
  exact ⟨u, hu, fun r hr hru => hsub ⟨hr, hru⟩⟩

/-- Monotonicity for events compared only at small scales, in filter form (`PolyHighProb.lean:142`). -/
theorem polyHighProb_mono_of_eventually_lp (h : PolyHighProb P E)
    (hEF : ∀ᶠ r in 𝓝[>] (0 : ℝ), E r ⊆ F r) : PolyHighProb P F := by
  obtain ⟨r₁, hr₁, h'⟩ := exists_pos_of_eventually_nhdsGT_lp hEF
  exact polyHighProb_mono_of_small_lp h hr₁ h'

/-- Intersecting with an almost sure event does not change the failure probabilities (`PolyHighProb.lean:148`). -/
theorem polyHighProb_inter_ae_lp (h : PolyHighProb P E) {W : Set Ω} (hW : ∀ᵐ ω ∂P, ω ∈ W) :
    PolyHighProb P fun r => E r ∩ W := by
  obtain ⟨p, hp, C, r₀, hr₀, hE⟩ := h
  have hW0 : P Wᶜ = 0 := ae_iff.1 hW
  refine ⟨p, hp, C, r₀, hr₀, fun r hr hrr => ?_⟩
  rw [compl_inter]
  calc P ((E r)ᶜ ∪ Wᶜ) ≤ P (E r)ᶜ + P Wᶜ := measure_union_le _ _
    _ = P (E r)ᶜ := by rw [hW0, add_zero]
    _ ≤ _ := hE r hr hrr

end PolyHighProbAlgebra

/-! ### Ding-Gwynne Lemma 3.8 on `closedBall 0 R` from the affine image (`Proofs/Sec2/RescaledUniform.lean:118`) -/

/-- Ding-Gwynne Lemma 3.8 on `closedBall 0 R`, from the bound on the unit square for the affine image of the
field. The additive constant `h_{2R}(-R(1+i))` is centred Gaussian, so `e^{γ h_{2R}(-R(1+i))} ∈ [r^{γc₀}, r^{-γc₀}]`
with polynomially high probability; the slack `β⁺ < β⁺'`, `β⁻' < β⁻` absorbs it and the constants. -/
theorem polyHighProb_closedBall_of_square_lp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {γ R βp βm βp' βm' : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hR : 0 < R)
    (hpp : βp < βp') (hmm : βm' < βm) (hβp' : 0 < βp') (hβm' : 0 < βm')
    (hDG : PolyHighProb P fun ε => {ω | (∀ z ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1,
          ENNReal.ofReal ε ≤ affineMeasure γ hcirc μ (squareA R) (squareB R) ω (ball z (ε ^ (1 / βm')))) ∧
        ∀ z ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1,
          affineMeasure γ hcirc μ (squareA R) (squareB R) ω (ball z (ε ^ (1 / βp'))) ≤ ENNReal.ofReal ε}) :
    PolyHighProb P fun r => {ω | ∀ w ∈ closedBall (0 : ℂ) R,
      ENNReal.ofReal (r ^ βm) ≤ μ ω (ball w r) ∧ μ ω (ball w r) ≤ ENNReal.ofReal (r ^ βp)} := by
  have hP := hGFF.isProbabilityMeasure
  have ha := squareA_ne_zero hR
  have han := norm_squareA hR
  set Y : Ω → ℝ := fun ω => hcirc ω ‖squareA R‖ (squareB R) with hY_def
  have hapos : 0 < ‖squareA R‖ := by rw [han]; positivity
  have hYG : HasGaussianLaw Y P := hGFF.hasGaussianLaw_circle hapos _
  have hYm : ∫ ω, Y ω ∂P = 0 := hGFF.integral_eq_zero (.circle ‖squareA R‖ (squareB R)) hapos
  set V := Var[Y; P] + 1 with hV
  have hV0 : 0 < V := by have := variance_nonneg Y P; linarith
  set c₀ := min (βm - βm') (βp' - βp) / (2 * γ) with hc₀_def
  have hmin0 : 0 < min (βm - βm') (βp' - βp) := lt_min (by linarith) (by linarith)
  have hc₀ : 0 < c₀ := div_pos hmin0 (by positivity)
  have hγc₀ : γ * c₀ = min (βm - βm') (βp' - βp) / 2 := by rw [hc₀_def]; field_simp
  have hγc₀m : γ * c₀ < βm - βm' := by
    rw [hγc₀]; linarith [min_le_left (βm - βm') (βp' - βp)]
  have hγc₀p : γ * c₀ < βp' - βp := by
    rw [hγc₀]; linarith [min_le_right (βm - βm') (βp' - βp)]
  -- the Gaussian additive constant
  set GY : ℝ → Set Ω := fun r => {ω | |Y ω| < c₀ * Real.log r⁻¹} with hGY_def
  have hGY : PolyHighProb P GY := by
    have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), P (GY r)ᶜ ≤ ENNReal.ofReal (2 * r ^ (1 : ℝ)) := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < Real.exp (-(2 * V / c₀ ^ 2)) by positivity)]
        with r hr
      obtain ⟨hr0, hrexp⟩ := hr
      set ℓ := Real.log r⁻¹ with hℓ
      have hℓV : 2 * V / c₀ ^ 2 ≤ ℓ := by
        have := Real.log_lt_log hr0 hrexp
        rw [Real.log_exp] at this
        rw [hℓ, Real.log_inv]; linarith
      have hℓ0 : 0 ≤ ℓ := le_trans (by positivity) hℓV
      have hcompl : (GY r)ᶜ = {ω | c₀ * ℓ ≤ |Y ω|} := by
        ext ω; simp only [hGY_def, mem_compl_iff, mem_ofPred_eq, not_lt, hℓ]
      rw [hcompl]
      refine (measure_le_abs_le_of_hasGaussianLaw_lp hYG hYm (by linarith : Var[Y; P] ≤ V) hV0
        (by positivity)).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [Real.rpow_one]
      have h2V : 2 * V ≤ ℓ * c₀ ^ 2 := (div_le_iff₀ (by positivity)).1 hℓV
      have : Real.exp (-((c₀ * ℓ) ^ 2) / (2 * V)) ≤ r := by
        calc Real.exp (-((c₀ * ℓ) ^ 2) / (2 * V)) ≤ Real.exp (-ℓ) := by
              apply Real.exp_le_exp.2
              rw [neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]
              nlinarith [mul_nonneg hℓ0 (sub_nonneg.2 h2V)]
          _ = r := by rw [hℓ, Real.log_inv, neg_neg, Real.exp_log hr0]
      linarith
    obtain ⟨r₁, hr₁, h'⟩ := exists_pos_of_eventually_nhdsGT_lp hev
    exact ⟨1, one_pos, 2, r₁, hr₁, h'⟩
  -- the bound of Ding-Gwynne at the scales `ε = ((2R)⁻¹ r)^{β}`
  have hl := polyHighProb_comp_mul_lp (polyHighProb_comp_rpow_lp hDG hβm') (c := (2 * R)⁻¹) (by positivity)
  have hu := polyHighProb_comp_mul_lp (polyHighProb_comp_rpow_lp hDG hβp') (c := (2 * R)⁻¹) (by positivity)
  set K₁ := (2 * R) ^ (γ * lqgQ γ) * ((2 * R) ^ βm')⁻¹ with hK₁
  set K₂ := (2 * R) ^ (γ * lqgQ γ) * ((2 * R) ^ βp')⁻¹ with hK₂
  refine polyHighProb_mono_of_eventually_lp (polyHighProb_inter_lp (polyHighProb_inter_lp hl hu) hGY) ?_
  filter_upwards [Ioo_mem_nhdsGT one_pos,
    eventually_rpow_le_mul_lp (c := K₁) (by positivity) (a := γ * c₀ + βm') (b := βm) (by linarith),
    eventually_mul_rpow_le_lp K₂ (a := βp' - γ * c₀) (b := βp) (by linarith)] with r hr hK₁r hK₂r
  obtain ⟨hr0, hr1⟩ := hr
  rintro ω ⟨⟨⟨hlow, -⟩, ⟨-, hup⟩⟩, hYω⟩ w hw
  obtain ⟨z, hz, hzw⟩ := exists_square_preimage hR hw
  have hρ0 : 0 < (2 * R)⁻¹ * r := by positivity
  have hρl : (((2 * R)⁻¹ * r) ^ βm') ^ (1 / βm') = (2 * R)⁻¹ * r := by
    rw [← Real.rpow_mul hρ0.le, mul_one_div_cancel hβm'.ne', Real.rpow_one]
  have hρu : (((2 * R)⁻¹ * r) ^ βp') ^ (1 / βp') = (2 * R)⁻¹ * r := by
    rw [← Real.rpow_mul hρ0.le, mul_one_div_cancel hβp'.ne', Real.rpow_one]
  have hball : affineMeasure γ hcirc μ (squareA R) (squareB R) ω (ball z ((2 * R)⁻¹ * r)) =
      ENNReal.ofReal (Real.exp (γ * (-(Y ω + lqgQ γ * Real.log ‖squareA R‖)))) * μ ω (ball w r) := by
    have hrad : ‖squareA R‖ * ((2 * R)⁻¹ * r) = r := by
      rw [han, mul_inv_cancel_left₀ (by positivity : (2 * R) ≠ 0)]
    rw [affineMeasure_ball _ _ _ ha, hzw, hrad]
  have hl' := hlow z hz
  rw [hρl, hball] at hl'
  have hu' := hup z hz
  rw [hρu, hball] at hu'
  set E1 := ENNReal.ofReal (Real.exp (γ * (-(Y ω + lqgQ γ * Real.log ‖squareA R‖)))) with hE1
  set F := ENNReal.ofReal (Real.exp (γ * (Y ω + lqgQ γ * Real.log ‖squareA R‖))) with hF
  have hFE : F * E1 = 1 := by
    rw [hF, hE1, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    rw [show γ * (Y ω + lqgQ γ * Real.log ‖squareA R‖) + γ * (-(Y ω + lqgQ γ * Real.log ‖squareA R‖)) = 0
      by ring, Real.exp_zero, ENNReal.ofReal_one]
  have hYb := abs_lt.1 (show |Y ω| < c₀ * Real.log r⁻¹ from hYω)
  have hlogr : Real.log r = -Real.log r⁻¹ := by rw [Real.log_inv, neg_neg]
  have hexpY1 : r ^ (γ * c₀) ≤ Real.exp (γ * Y ω) := by
    rw [Real.rpow_def_of_pos hr0]
    apply Real.exp_le_exp.2
    have := mul_lt_mul_of_pos_left hYb.1 hγ
    rw [hlogr]; linarith
  have hexpY2 : Real.exp (γ * Y ω) ≤ r ^ (-(γ * c₀)) := by
    rw [Real.rpow_def_of_pos hr0]
    apply Real.exp_le_exp.2
    have := mul_lt_mul_of_pos_left hYb.2 hγ
    rw [hlogr]; linarith
  have hFval : Real.exp (γ * (Y ω + lqgQ γ * Real.log ‖squareA R‖)) =
      Real.exp (γ * Y ω) * (2 * R) ^ (γ * lqgQ γ) := by
    rw [han, mul_add, Real.exp_add, Real.rpow_def_of_pos (by positivity)]
    ring_nf
  have hρm : ((2 * R)⁻¹ * r) ^ βm' = ((2 * R) ^ βm')⁻¹ * r ^ βm' := by
    rw [Real.mul_rpow (by positivity) hr0.le, Real.inv_rpow (by positivity)]
  have hρp : ((2 * R)⁻¹ * r) ^ βp' = ((2 * R) ^ βp')⁻¹ * r ^ βp' := by
    rw [Real.mul_rpow (by positivity) hr0.le, Real.inv_rpow (by positivity)]
  constructor
  · calc ENNReal.ofReal (r ^ βm) ≤ F * ENNReal.ofReal (((2 * R)⁻¹ * r) ^ βm') := by
          rw [hF, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
          apply ENNReal.ofReal_le_ofReal
          rw [hFval, hρm]
          calc r ^ βm ≤ K₁ * r ^ (γ * c₀ + βm') := hK₁r
            _ = r ^ (γ * c₀) * (2 * R) ^ (γ * lqgQ γ) * (((2 * R) ^ βm')⁻¹ * r ^ βm') := by
                rw [Real.rpow_add hr0, hK₁]; ring
            _ ≤ Real.exp (γ * Y ω) * (2 * R) ^ (γ * lqgQ γ) * (((2 * R) ^ βm')⁻¹ * r ^ βm') := by
                gcongr
      _ ≤ F * (E1 * μ ω (ball w r)) := by gcongr
      _ = μ ω (ball w r) := by rw [← mul_assoc, hFE, one_mul]
  · calc μ ω (ball w r) = F * (E1 * μ ω (ball w r)) := by rw [← mul_assoc, hFE, one_mul]
      _ ≤ F * ENNReal.ofReal (((2 * R)⁻¹ * r) ^ βp') := by gcongr
      _ = ENNReal.ofReal (Real.exp (γ * (Y ω + lqgQ γ * Real.log ‖squareA R‖)) *
            ((2 * R)⁻¹ * r) ^ βp') := by rw [hF, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
      _ ≤ ENNReal.ofReal (r ^ βp) := by
          apply ENNReal.ofReal_le_ofReal
          rw [hFval, hρp]
          calc Real.exp (γ * Y ω) * (2 * R) ^ (γ * lqgQ γ) * (((2 * R) ^ βp')⁻¹ * r ^ βp')
              ≤ r ^ (-(γ * c₀)) * (2 * R) ^ (γ * lqgQ γ) * (((2 * R) ^ βp')⁻¹ * r ^ βp') := by gcongr
            _ = K₂ * r ^ (βp' - γ * c₀) := by
                rw [sub_eq_add_neg, Real.rpow_add hr0, hK₂]; ring
            _ ≤ r ^ βp := hK₂r

end LatticeProb.LQG
