import HarmonicBalls.FirstPass.Frozen.S11f
import HarmonicBalls.Proofs.Sec11.DyadicIntermediateSquare

/-!
# Discrete dyadic square tail from the DDDF tail

Converts the uniform-on-compacts square tail `DDDFSquareDiameterTailFrozen` (DDDF20 Lemma 3.19 (3.63)) into the discrete
tail `hbound` of the Section 11 dyadic seeds (`exists_dyadic_intermediate_square_seed`,
`condExp_pinch_mass_diameter_pos_of_dyadic_cores`, paper lines 3392-3405, 3539-3541).

* The dyadic intermediate square `complexIntermediateGridSquare a r i` is the closed square of side `3r/2` with lower-left
  corner `intermediateCorner a r i`.
* The dyadic internal diameter uses the internal metric of the LARGER open square `complexOpenEnlargedGridSquare`, so it is
  bounded by the internal diameter of the closed square (`internalMetric_anti`).
* The exponent `(3r/2)^{p+ε} = (1/2)^{(p+e_n) n}` with `e_n = ε(ℓ_n) - (p+ε(ℓ_n)) log₂(3L/2)/n → 0` (exact identity).
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- The lower-left corner `a + ((i₁ - 1/4) r, (i₂ - 1/4) r)` of the intermediate grid square of index `i` at scale `r`. -/
noncomputable def intermediateCorner {N : ℕ} (a : ℂ) (r : ℝ) (i : Fin N × Fin N) : ℂ :=
  ⟨a.re + ((i.1.val : ℝ) - 1 / 4) * r, a.im + ((i.2.val : ℝ) - 1 / 4) * r⟩

/-- The intermediate grid square is the closed square of side `3r/2` with corner `intermediateCorner a r i`. -/
theorem complexIntermediateGridSquare_eq_closedSquare {N : ℕ} (a : ℂ) (r : ℝ) (i : Fin N × Fin N) :
    complexIntermediateGridSquare a r i = closedSquare (intermediateCorner a r i) (3 * r / 2) := by
  ext z
  simp only [complexIntermediateGridSquare, closedSquare, intermediateCorner, Complex.mem_reProdIm,
    mem_ofPred_eq, mem_Icc]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The closed intermediate square lies in the enlarged open square (for `r > 0`). -/
theorem closedSquare_intermediate_subset_enlarged {N : ℕ} (a : ℂ) {r : ℝ} (hr : 0 < r) (i : Fin N × Fin N) :
    closedSquare (intermediateCorner a r i) (3 * r / 2) ⊆ complexOpenEnlargedGridSquare a r i := by
  intro z hz
  simp only [closedSquare, Complex.mem_reProdIm, mem_Icc, intermediateCorner] at hz
  simp only [complexOpenEnlargedGridSquare, mem_ofPred_eq]
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hz
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The dyadic internal diameter is at most the internal diameter of the closed intermediate square, for the same
metric `D ω` (`internalMetric_anti`: a larger open set has a smaller internal metric). -/
theorem dyadicIntermediateInternalDiameter_le_closedSquare {Ω : Type*} (D : Ω → ℂ → ℂ → ℝ) (a : ℂ) {L : ℝ}
    (hL : 0 < L) (n : ℕ) (i : Fin (2 ^ n) × Fin (2 ^ n)) (ω : Ω) :
    dyadicIntermediateInternalDiameter D a L n i ω ≤
      ⨆ u ∈ closedSquare (intermediateCorner a (L / 2 ^ n) i) (3 * (L / 2 ^ n) / 2),
        ⨆ v ∈ closedSquare (intermediateCorner a (L / 2 ^ n) i) (3 * (L / 2 ^ n) / 2),
          internalMetric (D ω) (closedSquare (intermediateCorner a (L / 2 ^ n) i) (3 * (L / 2 ^ n) / 2)) u v := by
  have hr : 0 < L / 2 ^ n := div_pos hL (by positivity)
  unfold dyadicIntermediateInternalDiameter
  rw [complexIntermediateGridSquare_eq_closedSquare]
  exact iSup₂_mono fun x _ => iSup₂_mono fun y _ =>
    internalMetric_anti (D ω) (closedSquare_intermediate_subset_enlarged a hr i) x y

/-- The intermediate corners lie in the fixed compact square `closedSquare (z - ⟨L, L⟩) (3L)`. -/
theorem intermediateCorner_mem_closedSquare (z : ℂ) {L : ℝ} (hL : 0 < L) (n : ℕ) (i : Fin (2 ^ n) × Fin (2 ^ n)) :
    intermediateCorner z (L / 2 ^ n) i ∈ closedSquare (z - ⟨L, L⟩) (3 * L) := by
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  have hr : 0 < L / 2 ^ n := div_pos hL hpos
  have hrL : L / 2 ^ n ≤ L := div_le_self hL.le (one_le_pow₀ (by norm_num))
  have hi1 : ((i.1.val : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ n := by
    have : i.1.val + 1 ≤ 2 ^ n := i.1.isLt
    exact_mod_cast this
  have hi2 : ((i.2.val : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ n := by
    have : i.2.val + 1 ≤ 2 ^ n := i.2.isLt
    exact_mod_cast this
  have hprod : (L / 2 ^ n) * 2 ^ n = L := div_mul_cancel₀ L hpos.ne'
  have k1 : ((i.1.val : ℕ) : ℝ) * (L / 2 ^ n) ≤ ((2 : ℝ) ^ n - 1) * (L / 2 ^ n) :=
    mul_le_mul_of_nonneg_right (by linarith) hr.le
  have k2 : ((i.2.val : ℕ) : ℝ) * (L / 2 ^ n) ≤ ((2 : ℝ) ^ n - 1) * (L / 2 ^ n) :=
    mul_le_mul_of_nonneg_right (by linarith) hr.le
  have i1nn : (0 : ℝ) ≤ ((i.1.val : ℕ) : ℝ) := Nat.cast_nonneg _
  have i2nn : (0 : ℝ) ≤ ((i.2.val : ℕ) : ℝ) := Nat.cast_nonneg _
  simp only [closedSquare, Complex.mem_reProdIm, mem_Icc, intermediateCorner, Complex.sub_re, Complex.sub_im]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> nlinarith

/-- Exponent identity: `(3 r_n/2)^x = (1/2)^(x n - x log₂(3L/2))` for every `n`, with `r_n = L / 2^n`. -/
theorem dyadic_side_rpow_eq {L : ℝ} (hL : 0 < L) (x : ℝ) (n : ℕ) :
    (3 * (L / 2 ^ n) / 2) ^ x = (1 / 2 : ℝ) ^ (x * n - x * Real.logb 2 (3 * L / 2)) := by
  have hL32 : 0 < 3 * L / 2 := by linarith
  have hside : 0 < 3 * (L / 2 ^ n) / 2 := by positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  rw [Real.rpow_def_of_pos hside, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  congr 1
  have hlogside : Real.log (3 * (L / 2 ^ n) / 2) = Real.log (3 * L / 2) - n * Real.log 2 := by
    rw [show 3 * (L / 2 ^ n) / 2 = (3 * L / 2) / 2 ^ n by ring,
      Real.log_div hL32.ne' (by positivity), Real.log_pow]
  have hloghalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  rw [hlogside, hloghalf, Real.logb]
  field_simp
  ring

/-- Algebra of the exponent `e_n = q - (p + q) λ / n`: `(p + e_n) n = (p + q) n - (p + q) λ` for `n ≥ 1`. -/
theorem exponent_rewrite_aux (p q lam : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (p + (q - (p + q) * lam / n)) * n = (p + q) * n - (p + q) * lam := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  field_simp
  ring

/-- The main conversion: the DDDF tail gives the discrete dyadic tail `hbound` (with `b_n = (3r_n/2)^s c₁` and the exponent
`p = (ξQ - s)²/(2ξ²) > 2`, which needs `s < ξ(Q - 2)`). -/
theorem dddf_dyadic_tail {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hfr : DDDFSquareDiameterTailFrozen) {γ ξ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hξ : 0 < ξ) (h𝔇 : IsLQGMetric γ ξ 𝔇) (z : ℂ) {L : ℝ} (hL : 0 < L) {s : ℝ} (hs : 0 < s)
    (hs2 : s < ξ * (lqgQ γ - 2)) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∃ p : ℝ, 2 < p ∧
      ∀ᶠ n in atTop, ∀ i : Fin (2 ^ n) × Fin (2 ^ n),
        P {ω | ENNReal.ofReal ((3 * (L / 2 ^ n) / 2) ^ s * c₁) *
            ENNReal.ofReal (Real.exp (ξ * hcirc ω 1 0)) <
          dyadicIntermediateInternalDiameter (fun ω => 𝔇 (hC ω)) z L n i ω} ≤
          ENNReal.ofReal ((1 / 2 : ℝ) ^ ((p + e n) * n)) := by
  have hsQ : s < ξ * lqgQ γ := by nlinarith
  obtain ⟨c₁, hc₁, ε, hε, hev⟩ := hfr γ ξ Ω P hC hcirc 𝔇 hgff hγ hγ2 hξ h𝔇
    (closedSquare (z - ⟨L, L⟩) (3 * L))
    (by unfold closedSquare; exact IsCompact.reProdIm isCompact_Icc isCompact_Icc) s hs hsQ
  have hp : 2 < (ξ * lqgQ γ - s) ^ 2 / (2 * ξ ^ 2) := by
    rw [lt_div_iff₀ (mul_pos two_pos (pow_pos hξ 2))]
    have ht : 2 * ξ < ξ * lqgQ γ - s := by nlinarith
    nlinarith [mul_pos (sub_pos.2 ht) (by linarith : (0 : ℝ) < ξ * lqgQ γ - s + 2 * ξ)]
  set p : ℝ := (ξ * lqgQ γ - s) ^ 2 / (2 * ξ ^ 2) with hpdef
  set lam : ℝ := Real.logb 2 (3 * L / 2) with hlamdef
  have hℓpos : ∀ n : ℕ, 0 < 3 * (L / 2 ^ n) / 2 := fun n => by positivity
  have hℓlim : Tendsto (fun n : ℕ => 3 * (L / 2 ^ n) / 2) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => 3 * L / 2 * (1 / 2 : ℝ) ^ n) atTop (𝓝 (3 * L / 2 * 0)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul _
    rw [mul_zero] at h
    refine Tendsto.congr (fun n => ?_) h
    rw [one_div_pow]
    ring
  have hℓW : Tendsto (fun n : ℕ => 3 * (L / 2 ^ n) / 2) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hℓlim, Eventually.of_forall hℓpos⟩
  refine ⟨c₁, hc₁, fun n => ε (3 * (L / 2 ^ n) / 2) - (p + ε (3 * (L / 2 ^ n) / 2)) * lam / n, ?_, p, hp, ?_⟩
  · have h1 : Tendsto (fun n : ℕ => ε (3 * (L / 2 ^ n) / 2)) atTop (𝓝 0) := hε.comp hℓW
    have h2 : Tendsto (fun n : ℕ => (p + ε (3 * (L / 2 ^ n) / 2)) * lam / (n : ℝ)) atTop (𝓝 0) :=
      Tendsto.div_atTop ((tendsto_const_nhds.add h1).mul_const lam) tendsto_natCast_atTop_atTop
    have h3 := h1.sub h2
    rw [sub_zero] at h3
    exact h3
  · have hevn := hℓW.eventually hev
    filter_upwards [hevn, eventually_ge_atTop 1] with n hn hn1
    intro i
    have hw := hn _ (intermediateCorner_mem_closedSquare z hL n i)
    refine le_trans (measure_mono ?_) (le_trans hw (le_of_eq ?_))
    · intro ω hω
      refine lt_of_eq_of_lt (ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (hℓpos n).le _) hc₁.le)) ?_
      exact lt_of_lt_of_le hω (dyadicIntermediateInternalDiameter_le_closedSquare (fun ω => 𝔇 (hC ω)) z hL n i ω)
    · rw [dyadic_side_rpow_eq hL _ n, exponent_rewrite_aux p _ lam hn1]


end HarmonicBalls
