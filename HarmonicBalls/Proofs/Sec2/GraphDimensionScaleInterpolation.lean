import HarmonicBalls.Defs.LQGGraphDistance

/-!
# Interpolation of Liouville graph-distance scales

This develops the scale interpolation for the graph-distance definition.
We acknowledge Leonardo Bonanno's contributions to this formalization.
-/

namespace HarmonicBalls

open MeasureTheory Set Filter Topology

/-- A positive threshold has finite graph distance when finite dyadic distances occur
arbitrarily far along the dyadic sequence. -/
theorem liouvilleGraphDistance_ne_top_of_dyadic_eventually
    {μ : Measure ℂ} {z w : ℂ}
    (h : ∀ᶠ n : ℕ in atTop, liouvilleGraphDistance μ (dyadicScale n) z w ≠ ⊤)
    {ε : ℝ} (hε : 0 < ε) : liouvilleGraphDistance μ ε z w ≠ ⊤ := by
  have hscale : Tendsto dyadicScale atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hex : ∀ᶠ n : ℕ in atTop, dyadicScale n < ε :=
    hscale.eventually (Iio_mem_nhds hε)
  obtain ⟨n, hn, hne⟩ := (hex.and h).exists
  exact ne_top_of_le_ne_top hne ((liouvilleGraphDistance_antitone μ z w) hn.le)

/-- Dyadic finite-distance control implies finite distance at every positive mass threshold. -/
theorem IsLiouvilleGraphDimension.graphDistance_ne_top {μ : Measure ℂ} {z w : ℂ}
    {dimension : ℝ} (h : IsLiouvilleGraphDimension μ z w dimension)
    {ε : ℝ} (hε : 0 < ε) : liouvilleGraphDistance μ ε z w ≠ ⊤ :=
  liouvilleGraphDistance_ne_top_of_dyadic_eventually h.2.1 hε

/-- Any path cover uses at least one ball. -/
theorem one_le_liouvilleGraphDistance (μ : Measure ℂ) (ε : ℝ) (z w : ℂ) :
    1 ≤ liouvilleGraphDistance μ ε z w := by
  apply le_sInf
  rintro x ⟨count, rfl, balls, hballs, path, hpath⟩
  have hcount : 0 < count := by
    obtain ⟨i, hi⟩ := hpath ⟨0, by constructor <;> norm_num⟩
    exact Nat.pos_of_ne_zero (fun hzero => by subst count; exact Fin.elim0 i)
  exact_mod_cast hcount

/-- Logarithmic graph distance is monotone as the allowed positive mass decreases. -/
theorem log_graphDistance_le_of_le {μ : Measure ℂ} {z w : ℂ} {ε δ : ℝ}
    (hδε : δ ≤ ε)
    (hfinite : liouvilleGraphDistance μ δ z w ≠ ⊤) :
    Real.log (liouvilleGraphDistance μ ε z w).toNat ≤
      Real.log (liouvilleGraphDistance μ δ z w).toNat := by
  have hle := (liouvilleGraphDistance_antitone μ z w) hδε
  have hnat := ENat.toNat_le_toNat hle hfinite
  have hpos : 0 < (liouvilleGraphDistance μ ε z w).toNat := by
    have hfin : liouvilleGraphDistance μ ε z w ≠ ⊤ := ne_top_of_le_ne_top hfinite hle
    have hone := one_le_liouvilleGraphDistance μ ε z w
    have := ENat.toNat_le_toNat hone hfin
    have : 1 ≤ (liouvilleGraphDistance μ ε z w).toNat := by simpa using this
    omega
  exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hnat)

/-- Every positive threshold at most one lies between consecutive dyadic scales. -/
theorem exists_dyadicScale_bracket {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ n : ℕ, dyadicScale (n + 1) < ε ∧ ε ≤ dyadicScale n := by
  simpa only [dyadicScale, one_div] using
    exists_nat_pow_near_of_lt_one hε hε1 (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)

/-- The logarithm of the reciprocal threshold is bracketed by adjacent dyadic indices. -/
theorem log_inv_bracket {ε : ℝ} {n : ℕ} (hε : 0 < ε)
    (hlower : dyadicScale (n + 1) ≤ ε) (hupper : ε ≤ dyadicScale n) :
    (n : ℝ) * Real.log 2 ≤ Real.log ε⁻¹ ∧
      Real.log ε⁻¹ ≤ ((n + 1 : ℕ) : ℝ) * Real.log 2 := by
  have hlog (k : ℕ) : Real.log (dyadicScale k)⁻¹ = (k : ℝ) * Real.log 2 := by
    simp [dyadicScale, ← inv_pow, Real.log_pow]
  constructor
  · rw [← hlog n]
    exact Real.log_le_log (inv_pos.mpr (dyadicScale_pos n))
      ((inv_le_inv₀ (dyadicScale_pos n) hε).2 hupper)
  · rw [← hlog (n + 1)]
    exact Real.log_le_log (inv_pos.mpr hε)
      ((inv_le_inv₀ hε (dyadicScale_pos (n + 1))).2 hlower)

/-- The full-scale exponent is trapped between two adjacent dyadic numerators,
with their denominators shifted in the conservative direction. -/
theorem graphExponent_bracket {μ : Measure ℂ} {z w : ℂ} {dimension ε : ℝ} {n : ℕ}
    (h : IsLiouvilleGraphDimension μ z w dimension) (hn : 0 < n) (hε : 0 < ε)
    (hlower : dyadicScale (n + 1) ≤ ε) (hupper : ε ≤ dyadicScale n) :
    Real.log (liouvilleGraphDistance μ (dyadicScale n) z w).toNat /
        (((n + 1 : ℕ) : ℝ) * Real.log 2) ≤
      Real.log (liouvilleGraphDistance μ ε z w).toNat / Real.log ε⁻¹ ∧
    Real.log (liouvilleGraphDistance μ ε z w).toNat / Real.log ε⁻¹ ≤
      Real.log (liouvilleGraphDistance μ (dyadicScale (n + 1)) z w).toNat /
        ((n : ℝ) * Real.log 2) := by
  have hnpos : 0 < (n : ℝ) * Real.log 2 := mul_pos (by exact_mod_cast hn) (Real.log_pos (by norm_num))
  have hden := log_inv_bracket hε hlower hupper
  have hdenpos : 0 < Real.log ε⁻¹ := lt_of_lt_of_le hnpos hden.1
  have hlognonneg (δ : ℝ) (hδ : 0 < δ) :
      0 ≤ Real.log (liouvilleGraphDistance μ δ z w).toNat := by
    apply Real.log_nonneg
    have h1 := ENat.toNat_le_toNat (one_le_liouvilleGraphDistance μ δ z w)
      (h.graphDistance_ne_top hδ)
    exact_mod_cast h1
  have hA := log_graphDistance_le_of_le hupper (h.graphDistance_ne_top hε)
  have hB := log_graphDistance_le_of_le hlower (h.graphDistance_ne_top (dyadicScale_pos (n+1)))
  constructor
  · exact (div_le_div_of_nonneg_left (hlognonneg _ (dyadicScale_pos n)) hdenpos hden.2).trans
      (div_le_div_of_nonneg_right hA hdenpos.le)
  · exact (div_le_div_of_nonneg_right hB hdenpos.le).trans
      (div_le_div_of_nonneg_left (hlognonneg _ (dyadicScale_pos (n+1))) hnpos hden.1)

/-- An index of a dyadic interval containing a positive threshold at most one. -/
noncomputable def dyadicIntervalIndex (ε : ℝ) : ℕ :=
  if h : 0 < ε ∧ ε ≤ 1 then Classical.choose (exists_dyadicScale_bracket h.1 h.2) else 0

theorem dyadicIntervalIndex_spec {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    dyadicScale (dyadicIntervalIndex ε + 1) < ε ∧ ε ≤ dyadicScale (dyadicIntervalIndex ε) := by
  simp only [dyadicIntervalIndex, dite_eq_left (show 0 < ε ∧ ε ≤ 1 from ⟨hε, hε1⟩)]
  exact Classical.choose_spec (exists_dyadicScale_bracket hε hε1)

theorem tendsto_dyadicIntervalIndex :
    Tendsto dyadicIntervalIndex (𝓝[>] (0 : ℝ)) atTop := by
  apply tendsto_atTop.2
  intro N
  filter_upwards [Ioo_mem_nhdsGT (dyadicScale_pos N),
    Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε hε1
  have hb := dyadicIntervalIndex_spec hε.1 hε1.2.le
  by_contra hnot
  have hn : dyadicIntervalIndex ε + 1 ≤ N := by omega
  have hscale : dyadicScale N ≤ dyadicScale (dyadicIntervalIndex ε + 1) := by
    unfold dyadicScale
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  linarith [hε.2, hb.1]

/-- The dyadic point-to-point exponent extends to every positive mass scale. -/
theorem IsLiouvilleGraphDimension.fullScale {μ : Measure ℂ} {z w : ℂ} {dimension : ℝ}
    (h : IsLiouvilleGraphDimension μ z w dimension) :
    Tendsto (fun ε : ℝ =>
      Real.log (liouvilleGraphDistance μ ε z w).toNat / Real.log ε⁻¹)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / dimension)) := by
  let lower : ℕ → ℝ := fun n =>
    Real.log (liouvilleGraphDistance μ (dyadicScale n) z w).toNat /
      (((n + 1 : ℕ) : ℝ) * Real.log 2)
  let upper : ℕ → ℝ := fun n =>
    Real.log (liouvilleGraphDistance μ (dyadicScale (n + 1)) z w).toNat /
      ((n : ℝ) * Real.log 2)
  have hratio : Tendsto (fun n : ℕ => (n : ℝ) / (n + 1)) atTop (𝓝 1) :=
    tendsto_natCast_div_add_atTop 1
  have hlower : Tendsto lower atTop (𝓝 (1 / dimension)) := by
    have hh := h.2.2.mul hratio
    simp only [mul_one] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    dsimp [lower, liouvilleGraphExponent]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    push_cast
    field_simp
  have hshift : Tendsto (fun n : ℕ => liouvilleGraphExponent μ z w (n + 1))
      atTop (𝓝 (1 / dimension)) := h.2.2.comp (tendsto_add_atTop_nat 1)
  have hupper : Tendsto upper atTop (𝓝 (1 / dimension)) := by
    have hh := hshift.mul (hratio.inv₀ (by norm_num))
    simp only [inv_one, mul_one] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    dsimp [upper, liouvilleGraphExponent]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    push_cast
    field_simp
  apply (hlower.comp tendsto_dyadicIntervalIndex).squeeze'
    (hupper.comp tendsto_dyadicIntervalIndex)
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num),
      tendsto_dyadicIntervalIndex.eventually (eventually_ge_atTop 1)] with ε hε hn
    have hb := dyadicIntervalIndex_spec hε.1 hε.2.le
    exact (graphExponent_bracket h (by omega) hε.1 hb.1.le hb.2).1
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num),
      tendsto_dyadicIntervalIndex.eventually (eventually_ge_atTop 1)] with ε hε hn
    have hb := dyadicIntervalIndex_spec hε.1 hε.2.le
    exact (graphExponent_bracket h (by omega) hε.1 hb.1.le hb.2).2


end HarmonicBalls
