import Mathlib

/-! # Comparison of two normalizer families for one random scale observable

Task `weak-metric-normalizer-family-comparison` (worker z6).

Let `X r : Ω → ℝ≥0∞` be random observables indexed by the scale `r > 0`, and let `c r`, `c' r > 0` be two deterministic
normalizers. Assume that the normalized observable `X r / c r` is uniformly tight together with its reciprocal over `r > 0`,
in the window form of Pfeffer's Axiom V (arXiv:2104.04020v3, Definition 1.6, p. 6): for every `ε ∈ (0,1)` there is `M > 0`
with `P(M⁻¹ ≤ X_r / c_r ≤ M) ≥ 1 - ε` for all `r > 0`. The same is assumed for `X r / c' r`, with the same `X`.

Proved here, on an arbitrary probability space, with no further hypothesis:
* `normalizer_ratio_bounded`: one constant `K` satisfies `K⁻¹ ≤ c' r / c r ≤ K` for all `r > 0`. At level `ε = 1/4` the two
  windows have probability at least `3/4` each, so they meet (`nonempty_inter_of_prob_ge`). At a point of the intersection the
  observable is positive and finite (`toReal_window`), and `c' r / c r = (X_r / c_r) / (X_r / c'_r)` is a quotient of two
  numbers in `[M⁻¹, M]` (`ratio_bounds`).
* `uniformLogExponent_of_comparison`, `uniformLogExponent_stable`, `uniformLogExponent_iff`: the uniform logarithmic exponent
  `a` of (1.10), that is `log (c (δ r) / c r) / log δ → a` as `δ → 0` uniformly in `r > 0`, is the same for `c` and `c'`.
  The difference of the two logarithmic quotients is `log ρ(δ r) - log ρ(r)` with `ρ = c' / c`, bounded by `2 |log K|`
  uniformly in `r`; dividing by `|log δ|` makes it vanish as `δ → 0`.

Nothing here is a literature input or a derived target. There is no law of an LQG metric, no Pfeffer Proposition and no
physical dimension identity among the hypotheses. The observables are assumed measurable; positivity and finiteness of
`X r ω` are derived on the windows, not assumed. The file imports Mathlib only.

Credit: the whole-plane GFF and LQG carriers to which this comparison is applied are due to Leonardo Bonanno, through his
Lattice-Probability library (the `lean-v4.35` line pinned in `lakefile.lean`). This file consumes no declaration from it.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Set
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The normalized window `{M⁻¹ ≤ X_r / c_r ≤ M}` in `ℝ≥0∞`, as a subset of `Ω`. -/
def normWindow (X : ℝ → Ω → ℝ≥0∞) (c : ℝ → ℝ) (M : ℝ) (r : ℝ) : Set Ω :=
  {ω | ENNReal.ofReal M⁻¹ ≤ X r ω / ENNReal.ofReal (c r) ∧
    X r ω / ENNReal.ofReal (c r) ≤ ENNReal.ofReal M}

/-- Uniform tightness of `X_r / c_r` together with its reciprocal, in the window form of Pfeffer's Axiom V: for every
`ε ∈ (0,1)` there is `M > 0` with `P(M⁻¹ ≤ X_r / c_r ≤ M) ≥ 1 - ε` for all `r > 0`. The window is invariant under
`x ↦ x⁻¹`, so this is the tightness of the laws of `X_r / c_r` and of `c_r / X_r` in `(0, ∞)`. -/
def NormWindowTight (P : Measure Ω) (X : ℝ → Ω → ℝ≥0∞) (c : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ M : ℝ, 0 < M ∧ ∀ r : ℝ, 0 < r →
    ENNReal.ofReal (1 - ε) ≤ P (normWindow X c M r)

/-- The uniform logarithmic exponent `a` of the normalizers `c`: the uniform form of (1.10) in Pfeffer (arXiv:2104.04020v3,
Proposition 1.9), `c_{δr} / c_r = δ^{a + o_δ(1)}` with the `o(1)` uniform over `r > 0`. Explicitly, for every `η > 0` there
is `δ₀ > 0` such that `|log (c (δ r) / c r) / log δ - a| ≤ η` for all `δ ∈ (0, δ₀)` with `δ < 1` and all `r > 0`. -/
def UniformLogExponent (c : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < 1 → δ < δ₀ → ∀ r : ℝ, 0 < r →
    |Real.log (c (δ * r) / c r) / Real.log δ - a| ≤ η

/-- A normalized window is measurable when the observable is measurable. -/
theorem measurableSet_normWindow {X : ℝ → Ω → ℝ≥0∞} {c : ℝ → ℝ} (M r : ℝ) (hX : Measurable (X r)) :
    MeasurableSet (normWindow X c M r) := by
  have hf : Measurable fun ω => X r ω / ENNReal.ofReal (c r) := by
    simp only [div_eq_mul_inv]
    exact hX.mul measurable_const
  have h1 : MeasurableSet {ω | ENNReal.ofReal M⁻¹ ≤ X r ω / ENNReal.ofReal (c r)} :=
    measurableSet_le measurable_const hf
  have h2 : MeasurableSet {ω | X r ω / ENNReal.ofReal (c r) ≤ ENNReal.ofReal M} :=
    measurableSet_le hf measurable_const
  exact h1.inter h2

/-- An `ℝ≥0∞` window for `x / c` with `c > 0` forces `x ≠ ∞` and is the real window `M⁻¹ ≤ x.toReal / c ≤ M`. -/
theorem toReal_window {x : ℝ≥0∞} {c M : ℝ} (hc : 0 < c) (hM : 0 < M)
    (h : ENNReal.ofReal M⁻¹ ≤ x / ENNReal.ofReal c ∧ x / ENNReal.ofReal c ≤ ENNReal.ofReal M) :
    M⁻¹ ≤ x.toReal / c ∧ x.toReal / c ≤ M := by
  obtain ⟨h1, h2⟩ := h
  have hx : x ≠ ⊤ := by
    intro hxt
    rw [hxt, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top, top_le_iff] at h2
    exact ENNReal.ofReal_ne_top h2
  have hxeq : x / ENNReal.ofReal c = ENNReal.ofReal (x.toReal / c) := by
    rw [ENNReal.ofReal_div_of_pos hc, ENNReal.ofReal_toReal hx]
  rw [hxeq] at h1 h2
  exact ⟨(ENNReal.ofReal_le_ofReal_iff (div_nonneg ENNReal.toReal_nonneg hc.le)).mp h1,
    (ENNReal.ofReal_le_ofReal_iff hM.le).mp h2⟩

/-- Two events, each of probability at least `1 - ε` with `ε < 1/2`, meet. -/
theorem nonempty_inter_of_prob_ge {P : Measure Ω} [IsProbabilityMeasure P] {A B : Set Ω}
    (hA : MeasurableSet A) {ε : ℝ} (hε : ε < 1 / 2)
    (hPA : ENNReal.ofReal (1 - ε) ≤ P A) (hPB : ENNReal.ofReal (1 - ε) ≤ P B) :
    (A ∩ B).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have hsub : B ⊆ Aᶜ := fun ω hωB hωA => by
    have hmem : ω ∈ A ∩ B := ⟨hωA, hωB⟩
    rw [hne] at hmem
    exact hmem
  have h1 : P B ≤ P Aᶜ := measure_mono hsub
  have h2 : P A + P Aᶜ = 1 := prob_add_prob_compl hA
  have h0 : (0 : ℝ) ≤ 1 - ε := by linarith
  have h3 : ENNReal.ofReal (1 - ε) + ENNReal.ofReal (1 - ε) ≤ 1 :=
    calc ENNReal.ofReal (1 - ε) + ENNReal.ofReal (1 - ε) ≤ P A + P B := add_le_add hPA hPB
      _ ≤ P A + P Aᶜ := by gcongr
      _ = 1 := h2
  rw [← ENNReal.ofReal_add h0 h0, ← ENNReal.ofReal_one,
    ENNReal.ofReal_le_ofReal_iff zero_le_one] at h3
  linarith

/-- Elementary bound: if `u ∈ [M₁⁻¹, M₁]` and `v ∈ [M₂⁻¹, M₂]`, then `u / v ∈ [(M₁ M₂)⁻¹, M₁ M₂]`. -/
theorem ratio_bounds {u v M₁ M₂ : ℝ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hu : M₁⁻¹ ≤ u ∧ u ≤ M₁) (hv : M₂⁻¹ ≤ v ∧ v ≤ M₂) :
    (M₁ * M₂)⁻¹ ≤ u / v ∧ u / v ≤ M₁ * M₂ := by
  have hvpos : 0 < v := lt_of_lt_of_le (inv_pos.mpr hM₂) hv.1
  have hM₂v : 1 ≤ M₂ * v := by
    have h := mul_le_mul_of_nonneg_left hv.1 hM₂.le
    rwa [mul_inv_cancel₀ hM₂.ne'] at h
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ hvpos]
    calc (M₁ * M₂)⁻¹ * v ≤ (M₁ * M₂)⁻¹ * M₂ :=
          mul_le_mul_of_nonneg_left hv.2 (inv_nonneg.mpr (mul_pos hM₁ hM₂).le)
      _ = M₁⁻¹ := by rw [mul_inv, mul_assoc, inv_mul_cancel₀ hM₂.ne', mul_one]
      _ ≤ u := hu.1
  · rw [div_le_iff₀ hvpos]
    calc u ≤ M₁ := hu.2
      _ = M₁ * 1 := (mul_one M₁).symm
      _ ≤ M₁ * (M₂ * v) := mul_le_mul_of_nonneg_left hM₂v hM₁.le
      _ = M₁ * M₂ * v := (mul_assoc _ _ _).symm

/-- **Comparison of normalizers.** If `X_r / c_r` and `X_r / c'_r` are both uniformly tight together with their reciprocals,
then one constant `K` bounds the ratio `c'_r / c_r` from above and below, uniformly in `r > 0`. -/
theorem normalizer_ratio_bounded {P : Measure Ω} [IsProbabilityMeasure P] {X : ℝ → Ω → ℝ≥0∞}
    {c c' : ℝ → ℝ} (hX : ∀ r : ℝ, Measurable (X r))
    (hc : ∀ r : ℝ, 0 < r → 0 < c r) (hc' : ∀ r : ℝ, 0 < r → 0 < c' r)
    (ht : NormWindowTight P X c) (ht' : NormWindowTight P X c') :
    ∃ K : ℝ, 0 < K ∧ ∀ r : ℝ, 0 < r → K⁻¹ ≤ c' r / c r ∧ c' r / c r ≤ K := by
  obtain ⟨M₁, hM₁, hW₁⟩ := ht (1 / 4) (by norm_num) (by norm_num)
  obtain ⟨M₂, hM₂, hW₂⟩ := ht' (1 / 4) (by norm_num) (by norm_num)
  refine ⟨M₁ * M₂, mul_pos hM₁ hM₂, fun r hr => ?_⟩
  obtain ⟨ω, hω₁, hω₂⟩ := nonempty_inter_of_prob_ge (measurableSet_normWindow M₁ r (hX r))
    (by norm_num) (hW₁ r hr) (hW₂ r hr)
  have hω₁' : ENNReal.ofReal M₁⁻¹ ≤ X r ω / ENNReal.ofReal (c r) ∧
      X r ω / ENNReal.ofReal (c r) ≤ ENNReal.ofReal M₁ := hω₁
  have hω₂' : ENNReal.ofReal M₂⁻¹ ≤ X r ω / ENNReal.ofReal (c' r) ∧
      X r ω / ENNReal.ofReal (c' r) ≤ ENNReal.ofReal M₂ := hω₂
  obtain ⟨hu₁, hu₂⟩ := toReal_window (hc r hr) hM₁ hω₁'
  obtain ⟨hv₁, hv₂⟩ := toReal_window (hc' r hr) hM₂ hω₂'
  have hx0 : (X r ω).toReal ≠ 0 := by
    intro h0
    rw [h0, zero_div] at hu₁
    exact absurd hu₁ (not_le.mpr (inv_pos.mpr hM₁))
  have hcr : c r ≠ 0 := (hc r hr).ne'
  have hcr' : c' r ≠ 0 := (hc' r hr).ne'
  have hratio : c' r / c r = ((X r ω).toReal / c r) / ((X r ω).toReal / c' r) := by
    field_simp
  rw [hratio]
  exact ratio_bounds hM₁ hM₂ ⟨hu₁, hu₂⟩ ⟨hv₁, hv₂⟩

/-- If `K⁻¹ ≤ ρ ≤ K` then `|log ρ| ≤ |log K|`. -/
theorem abs_log_le_abs_log_of_bounds {ρ K : ℝ} (hρ : 0 < ρ) (hK : 0 < K) (h : K⁻¹ ≤ ρ ∧ ρ ≤ K) :
    |Real.log ρ| ≤ |Real.log K| := by
  have h1 : Real.log K⁻¹ ≤ Real.log ρ := Real.log_le_log (inv_pos.mpr hK) h.1
  have h2 : Real.log ρ ≤ Real.log K := Real.log_le_log hρ h.2
  rw [Real.log_inv] at h1
  exact abs_le.mpr ⟨by linarith [le_abs_self (Real.log K)], by linarith [le_abs_self (Real.log K)]⟩

/-- **Stability of the uniform logarithmic exponent under a uniform comparison of normalizers.** If `K⁻¹ ≤ c'_r / c_r ≤ K`
for all `r > 0`, then a uniform logarithmic exponent `a` of `c` is also one of `c'`. -/
theorem uniformLogExponent_of_comparison {c c' : ℝ → ℝ} {a K : ℝ} (hK : 0 < K)
    (hc : ∀ r : ℝ, 0 < r → 0 < c r) (hc' : ∀ r : ℝ, 0 < r → 0 < c' r)
    (hcomp : ∀ r : ℝ, 0 < r → K⁻¹ ≤ c' r / c r ∧ c' r / c r ≤ K) (h : UniformLogExponent c a) :
    UniformLogExponent c' a := by
  intro η hη
  obtain ⟨δ₀, hδ₀, hδ⟩ := h (η / 2) (half_pos hη)
  have hL0 : 0 ≤ |Real.log K| := abs_nonneg _
  refine ⟨min δ₀ (Real.exp (-(4 * |Real.log K| / η))), lt_min hδ₀ (Real.exp_pos _),
    fun δ hδpos hδ1 hδlt r hr => ?_⟩
  have hδ₀' : δ < δ₀ := lt_of_lt_of_le hδlt (min_le_left _ _)
  have hδ₁' : δ < Real.exp (-(4 * |Real.log K| / η)) := lt_of_lt_of_le hδlt (min_le_right _ _)
  have hlogδ : Real.log δ < -(4 * |Real.log K| / η) := by
    have h' := Real.log_lt_log hδpos hδ₁'
    rwa [Real.log_exp] at h'
  have hq : 0 ≤ 4 * |Real.log K| / η := div_nonneg (by linarith) hη.le
  have hlogneg : Real.log δ < 0 := by linarith
  have hlogne : Real.log δ ≠ 0 := hlogneg.ne
  -- once `|log δ| ≥ 4 |log K| / η`, the comparison error `2 |log K| / |log δ|` is at most `η / 2`
  have hbig : 2 * |Real.log K| ≤ η / 2 * |Real.log δ| := by
    rw [abs_of_neg hlogneg]
    have h4 : η / 2 * (4 * |Real.log K| / η) = 2 * |Real.log K| := by
      field_simp
      ring
    have h5 : η / 2 * (4 * |Real.log K| / η) ≤ η / 2 * -Real.log δ :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  have hcδ : 0 < c (δ * r) := hc _ (mul_pos hδpos hr)
  have hcδ' : 0 < c' (δ * r) := hc' _ (mul_pos hδpos hr)
  have hcr : 0 < c r := hc r hr
  have hcr' : 0 < c' r := hc' r hr
  have hcδ0 : c (δ * r) ≠ 0 := hcδ.ne'
  have hcδ'0 : c' (δ * r) ≠ 0 := hcδ'.ne'
  have hcr0 : c r ≠ 0 := hcr.ne'
  have hcr'0 : c' r ≠ 0 := hcr'.ne'
  -- the ratio identity `c'_{δr} / c'_r = (c_{δr} / c_r) · (ρ(δr) / ρ(r))` with `ρ = c' / c`
  have hid : c' (δ * r) / c' r = (c (δ * r) / c r) * ((c' (δ * r) / c (δ * r)) / (c' r / c r)) := by
    field_simp
  have hlogid : Real.log (c' (δ * r) / c' r) = Real.log (c (δ * r) / c r)
      + (Real.log (c' (δ * r) / c (δ * r)) - Real.log (c' r / c r)) := by
    rw [hid, Real.log_mul (div_pos hcδ hcr).ne' (div_pos (div_pos hcδ' hcδ) (div_pos hcr' hcr)).ne',
      Real.log_div (div_pos hcδ' hcδ).ne' (div_pos hcr' hcr).ne']
  have hρ1 := abs_le.mp (abs_log_le_abs_log_of_bounds (div_pos hcδ' hcδ) hK
    (hcomp (δ * r) (mul_pos hδpos hr)))
  have hρ2 := abs_le.mp (abs_log_le_abs_log_of_bounds (div_pos hcr' hcr) hK (hcomp r hr))
  have hDbd : |Real.log (c' (δ * r) / c (δ * r)) - Real.log (c' r / c r)| ≤ 2 * |Real.log K| :=
    abs_le.mpr ⟨by linarith [hρ1.1, hρ1.2, hρ2.1, hρ2.2], by linarith [hρ1.1, hρ1.2, hρ2.1, hρ2.2]⟩
  have hsplit : Real.log (c' (δ * r) / c' r) / Real.log δ - a
      = (Real.log (c (δ * r) / c r) / Real.log δ - a)
        + (Real.log (c' (δ * r) / c (δ * r)) - Real.log (c' r / c r)) / Real.log δ := by
    rw [hlogid]
    ring
  have hA := hδ δ hδpos hδ1 hδ₀' r hr
  have hB : |(Real.log (c' (δ * r) / c (δ * r)) - Real.log (c' r / c r)) / Real.log δ| ≤ η / 2 := by
    rw [abs_div, div_le_iff₀ (abs_pos.mpr hlogne)]
    linarith [hDbd, hbig]
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  linarith [hA, hB]

/-- The reverse comparison `K⁻¹ ≤ c_r / c'_r ≤ K`. -/
theorem comparison_symm {c c' : ℝ → ℝ} {K : ℝ} (hK : 0 < K) (hc : ∀ r : ℝ, 0 < r → 0 < c r)
    (hc' : ∀ r : ℝ, 0 < r → 0 < c' r)
    (hcomp : ∀ r : ℝ, 0 < r → K⁻¹ ≤ c' r / c r ∧ c' r / c r ≤ K) :
    ∀ r : ℝ, 0 < r → K⁻¹ ≤ c r / c' r ∧ c r / c' r ≤ K := by
  intro r hr
  have hy : 0 < c' r / c r := div_pos (hc' r hr) (hc r hr)
  obtain ⟨h1, h2⟩ := hcomp r hr
  rw [← inv_div]
  refine ⟨inv_anti₀ hy h2, ?_⟩
  have h3 := inv_anti₀ (inv_pos.mpr hK) h1
  rwa [inv_inv] at h3

/-- **Stability of the uniform logarithmic exponent.** Two normalizer families making the same observable `X` uniformly
tight together with its reciprocal (window form) have the same uniform logarithmic exponents. -/
theorem uniformLogExponent_stable {P : Measure Ω} [IsProbabilityMeasure P] {X : ℝ → Ω → ℝ≥0∞}
    {c c' : ℝ → ℝ} {a : ℝ} (hX : ∀ r : ℝ, Measurable (X r))
    (hc : ∀ r : ℝ, 0 < r → 0 < c r) (hc' : ∀ r : ℝ, 0 < r → 0 < c' r)
    (ht : NormWindowTight P X c) (ht' : NormWindowTight P X c') (h : UniformLogExponent c a) :
    UniformLogExponent c' a := by
  obtain ⟨K, hK, hcomp⟩ := normalizer_ratio_bounded hX hc hc' ht ht'
  exact uniformLogExponent_of_comparison hK hc hc' hcomp h

/-- The uniform logarithmic exponent does not depend on the choice of valid normalizer for the same observable. -/
theorem uniformLogExponent_iff {P : Measure Ω} [IsProbabilityMeasure P] {X : ℝ → Ω → ℝ≥0∞}
    {c c' : ℝ → ℝ} {a : ℝ} (hX : ∀ r : ℝ, Measurable (X r))
    (hc : ∀ r : ℝ, 0 < r → 0 < c r) (hc' : ∀ r : ℝ, 0 < r → 0 < c' r)
    (ht : NormWindowTight P X c) (ht' : NormWindowTight P X c') :
    UniformLogExponent c a ↔ UniformLogExponent c' a := by
  obtain ⟨K, hK, hcomp⟩ := normalizer_ratio_bounded hX hc hc' ht ht'
  exact ⟨uniformLogExponent_of_comparison hK hc hc' hcomp,
    uniformLogExponent_of_comparison hK hc' hc (comparison_symm hK hc hc' hcomp)⟩

end HarmonicBalls

#print axioms HarmonicBalls.normalizer_ratio_bounded
#print axioms HarmonicBalls.uniformLogExponent_of_comparison
#print axioms HarmonicBalls.uniformLogExponent_stable
#print axioms HarmonicBalls.uniformLogExponent_iff
