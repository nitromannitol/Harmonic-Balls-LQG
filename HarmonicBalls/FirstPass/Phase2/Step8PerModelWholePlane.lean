import HarmonicBalls.FirstPass.Phase2.Step8PerModelFrequency
import HarmonicBalls.FirstPass.S11i.Step8ZoomFrequency

/-!
# The per-model certificate frequency from the whole-plane frequency at dyadic radii

Step 8 of Lemma 11.13 (paper, `eq:dyadic-frequency`) for one model: the window frequency of the certificate events at
the radii `2⁻ⁿ` about `μ`-almost every point of the plane tends to a number `q > 0`. This file shows that this
whole-plane statement at the radii `2⁻ⁿ` gives the per-model statement `Step8CertificateFrequencyPerModelStmt` with the
dyadic zoom families of unit constants (`zoomMeasure`, `zoomMetric`), and with the same `q` at every scale `2^k`.

The zoom at scale `2^k` is a change of coordinates of the same model: the window certificate at radius `2⁻ⁿ` about
`w ∈ B₁(0)` is the certificate of `(μ, D)` at radius `2^k 2⁻ⁿ = 2^{-(n-k)}` about `2^k w ∈ B_{2^k}(0)`
(`step8_zoom_family_of_ae_frequency`). The window counts at the radii `2^{-(n-k)}` and `2⁻ⁿ` differ by at most `k`
(`ncard_window_shift_le`, `ncard_window_unshift_le`), so the two frequencies have the same limit.

## Main results

* `tendsto_window_frequency_shift`: a shift of the index by `k` does not change the limit of the window frequency.
* `Step8CertificateFrequencyWholePlaneStmt`: for every model, the whole-plane window frequency at the radii `2⁻ⁿ`.
* `step8CertificateFrequencyPerModel_of_wholePlane`: it implies `Step8CertificateFrequencyPerModelStmt`.
-/

universe u

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HarmonicBalls

/-- Shifting the index by `k` adds at most `k` to the window count. -/
lemma ncard_window_shift_le (A : ℕ → Prop) (k N : ℕ) :
    {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ A (n - k)}.ncard ≤
      {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ A n}.ncard + k := by
  have hfin : {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ A n}.Finite :=
    (Set.finite_Icc (N + 1) (2 * N)).subset fun n hn => ⟨hn.1, hn.2.1⟩
  have hsub : {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ A (n - k)} ⊆
      (fun m => m + k) '' {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ A n} ∪ Set.Ico (N + 1) (N + 1 + k) := by
    rintro n ⟨h1, h2, hA⟩
    by_cases hnk : N + 1 + k ≤ n
    · exact Or.inl ⟨n - k, ⟨by omega, by omega, hA⟩, Nat.sub_add_cancel (by omega)⟩
    · exact Or.inr ⟨h1, by omega⟩
  have hIco : (Set.Ico (N + 1) (N + 1 + k)).ncard = k := by
    rw [← Finset.coe_Ico, Set.ncard_coe_finset, Nat.card_Ico]
    omega
  calc {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ A (n - k)}.ncard
      ≤ ((fun m => m + k) '' {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ A n} ∪ Set.Ico (N + 1) (N + 1 + k)).ncard :=
        Set.ncard_le_ncard hsub ((hfin.image _).union (Set.finite_Ico _ _))
    _ ≤ ((fun m => m + k) '' {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ A n}).ncard +
          (Set.Ico (N + 1) (N + 1 + k)).ncard := Set.ncard_union_le _ _
    _ ≤ {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ A n}.ncard + k := by
        rw [hIco]
        exact Nat.add_le_add_right (Set.ncard_image_le hfin) k

/-- Undoing the shift of the index by `k` adds at most `k` to the window count. -/
lemma ncard_window_unshift_le (A : ℕ → Prop) (k N : ℕ) :
    {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ A n}.ncard ≤
      {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ A (n - k)}.ncard + k := by
  have hfin : {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ A (n - k)}.Finite :=
    (Set.finite_Icc (N + 1) (2 * N)).subset fun n hn => ⟨hn.1, hn.2.1⟩
  have hsub : {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ A n} ⊆
      (fun m => m - k) '' {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ A (n - k)} ∪ Set.Ico (2 * N + 1 - k) (2 * N + 1) := by
    rintro n ⟨h1, h2, hA⟩
    by_cases hnk : n + k ≤ 2 * N
    · refine Or.inl ⟨n + k, ⟨by omega, hnk, ?_⟩, (by show n + k - k = n; omega)⟩
      rw [Nat.add_sub_cancel]
      exact hA
    · exact Or.inr ⟨by omega, by omega⟩
  have hIco : (Set.Ico (2 * N + 1 - k) (2 * N + 1)).ncard ≤ k := by
    rw [← Finset.coe_Ico, Set.ncard_coe_finset, Nat.card_Ico]
    omega
  calc {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ A n}.ncard
      ≤ ((fun m => m - k) '' {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ A (n - k)} ∪
          Set.Ico (2 * N + 1 - k) (2 * N + 1)).ncard :=
        Set.ncard_le_ncard hsub ((hfin.image _).union (Set.finite_Ico _ _))
    _ ≤ ((fun m => m - k) '' {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ A (n - k)}).ncard +
          (Set.Ico (2 * N + 1 - k) (2 * N + 1)).ncard := Set.ncard_union_le _ _
    _ ≤ {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ A (n - k)}.ncard + k :=
        Nat.add_le_add (Set.ncard_image_le hfin) hIco

/-- **Index shift of the window frequency.** If the window frequency of the events `A n`, `n ∈ [N + 1, 2N]`, tends to
`q`, so does the window frequency of the events `A (n - k)`. -/
lemma tendsto_window_frequency_shift (A : ℕ → Prop) (k : ℕ) {q : ℝ}
    (h : Tendsto (fun N : ℕ => ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ A n}.ncard : ℝ) / (N : ℝ)) atTop (𝓝 q)) :
    Tendsto (fun N : ℕ => ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ A (n - k)}.ncard : ℝ) / (N : ℝ)) atTop (𝓝 q) := by
  have hbound : ∀ N : ℕ, |({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ A (n - k)}.ncard : ℝ) -
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ A n}.ncard : ℝ)| ≤ k := by
    intro N
    have h1 : (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ A (n - k)}.ncard : ℕ) : ℝ) ≤
        (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ A n}.ncard : ℕ) : ℝ) + k := by
      exact_mod_cast ncard_window_shift_le A k N
    have h2 : (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ A n}.ncard : ℕ) : ℝ) ≤
        (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ A (n - k)}.ncard : ℕ) : ℝ) + k := by
      exact_mod_cast ncard_window_unshift_le A k N
    rw [abs_le]
    constructor <;> linarith
  have hdiff : Tendsto (fun N : ℕ => ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ A (n - k)}.ncard : ℝ) / (N : ℝ) -
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ A n}.ncard : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun N => ?_) (tendsto_const_div_atTop_nhds_zero_nat (k : ℝ))
    rw [Real.norm_eq_abs, ← sub_div, abs_div, Nat.abs_cast]
    gcongr
    exact hbound N
  have hsum := h.add hdiff
  rw [add_zero] at hsum
  exact hsum.congr fun N => by ring

/-- `2^k 2⁻ⁿ = 2^{-(n-k)}` for `k ≤ n`. -/
lemma two_pow_mul_inv_two_pow_eq {k n : ℕ} (h : k ≤ n) :
    (2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ n = (2 : ℝ)⁻¹ ^ (n - k) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, pow_add, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ (two_ne_zero), one_pow, one_mul]

/-- **Step 8 of Lemma 11.13, whole-plane form at the radii `2⁻ⁿ`.** For every buffered geometry, `0 < γ < 2`,
`α₀ < Q_γ`, `M > 0`, and every whole-plane model `(P, hC, hcirc, μ, D)` with insertion `α₀` on `Ω : Type u`, there is
`q > 0` such that, almost surely and for `μ`-almost every `z ∈ ℂ`, the window frequency of the certificate events
(`O_* = pinchOmegaGeom W Q δ₀`, `η = δ₀`) at the radii `2⁻ⁿ` about `z` tends to `q` (paper, `eq:dyadic-frequency`). -/
def Step8CertificateFrequencyWholePlaneStmt : Prop :=
  ∀ (U V W T Q' Q : Set ℂ) (δ₀ : ℝ), IsBufferedPinchGeometry U V W T Q' Q δ₀ →
  ∀ γ α₀ M : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ → 0 < M →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    IsLQGMetricOfField P γ (lqgXi γ) α₀ hC D →
    ∃ q : ℝ, 0 < q ∧ ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω),
      Tendsto (fun N : ℕ => ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        FirstPassS11i.CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ₀) U V W T Q' Q δ₀ M ((2 : ℝ)⁻¹ ^ n) z}.ncard
          : ℝ) / (N : ℝ)) atTop (𝓝 q)

/-- **The per-model certificate frequency from the whole-plane frequency.** The zoom families are those of unit
constants, and the limit `q` is the same at every scale. -/
theorem step8CertificateFrequencyPerModel_of_wholePlane (hWP : Step8CertificateFrequencyWholePlaneStmt.{u}) :
    Step8CertificateFrequencyPerModelStmt.{u} := by
  intro U V W T Q' Q δ₀ hgeom γ α₀ M hγ0 hγ2 hα hM Ω _ P hC hcirc μ D hG hμ hD
  obtain ⟨q, hq, hfreq⟩ := hWP U V W T Q' Q δ₀ hgeom γ α₀ M hγ0 hγ2 hα hM Ω P hC hcirc μ D hG hμ hD
  refine ⟨q, hq, HarmonicBalls.FirstPassS11iStep8Zoom.step8_zoom_family_of_ae_frequency P U V W T Q' Q δ₀ M q μ D
    fun k => ?_⟩
  filter_upwards [hfreq] with ω hω
  filter_upwards [hω] with z hz _
  refine (tendsto_window_frequency_shift (fun m => FirstPassS11i.CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ₀)
    U V W T Q' Q δ₀ M ((2 : ℝ)⁻¹ ^ m) z) k hz).congr' ?_
  filter_upwards [eventually_ge_atTop k] with N hN
  have hset : {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ FirstPassS11i.CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ₀)
      U V W T Q' Q δ₀ M ((2 : ℝ)⁻¹ ^ (n - k)) z} =
      {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ FirstPassS11i.CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ₀)
      U V W T Q' Q δ₀ M ((2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ n) z} := by
    ext n
    simp only [Set.mem_ofPred_eq]
    refine and_congr_right fun h1 => and_congr_right fun _ => ?_
    rw [two_pow_mul_inv_two_pow_eq (by omega : k ≤ n)]
  exact congrArg (fun s : Set ℕ => ((s.ncard : ℕ) : ℝ) / (N : ℝ)) hset

end HarmonicBalls
