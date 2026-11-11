import HarmonicBalls.Steps.Sec11.PinchStationaryMean
import HarmonicBalls.Steps.Sec11.PinchPositiveDensity
import HarmonicBalls.Proposed.Birkhoff

/-!
# Frozen pinch block density from a certificate family at the origin

Written argument draft lines 515-552 (dilation stationarity, the pointwise
ergodic theorem, and the passage from prefix averages to block averages `2 A_{2N} - A_N`).

The indicator sequence `X n` is the indicator of the scale-`2^{-n}` certificate event `E n`. Each `E n` is a
sufficient event for the frozen pinch event `pinchPointEvent … M (2⁻¹ ^ n) z` (draft 515-530, `E_r(z;M) ⊂ Ĝ_r(z;M)`).
The certificate is local, so the frozen metric-ball event does not have to be local (the internal-bounds event is not
used here).

Proved in this file:
* `sum_Icc_prefix_add_block`, `tendsto_block_average_of_prefix_average`: prefix Cesàro limits give block Cesàro limits.
* `frozen_block_density_of_certificate_family`: a stationary, germ-trivial family of local certificate events with
  positive mean gives the frozen block density at `z` with a deterministic `δ ∈ (0,1)`.

Explicit hypotheses (open steps of the written argument, not literature inputs): the scale family `E`, its
sufficiency for the frozen event, the germ-measurability (locality) of `E n` (`hXgerm`), the germ triviality
(`htrivial`, draft 515-534) and the stationarity of the indicator law (`hstat`, draft 515-530).

The pointwise ergodic theorem is LatticeProb's `LatticeProb.Prob.Birkhoff` (Leonardo Bonanno), used through
`HarmonicBalls.Proposed.Birkhoff` (`pointwiseBirkhoff_of_latticeProb`, a theorem, not an assumption).
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- Prefix and block sums of a real sequence over `Finset.Icc` add up:
`∑_{n ∈ Icc 1 a} x n + ∑_{n ∈ Icc (a+1) (a+b)} x n = ∑_{n ∈ Icc 1 (a+b)} x n`. -/
theorem sum_Icc_prefix_add_block (x : ℕ → ℝ) (a : ℕ) :
    ∀ b : ℕ, ∑ n ∈ Finset.Icc 1 a, x n + ∑ n ∈ Finset.Icc (a + 1) (a + b), x n =
      ∑ n ∈ Finset.Icc 1 (a + b), x n := by
  intro b
  induction b with
  | zero => simp
  | succ b ih =>
    have h1 : a + (b + 1) = (a + b) + 1 := by omega
    rw [h1, Finset.sum_Icc_succ_top (by omega : a + 1 ≤ a + b + 1),
      Finset.sum_Icc_succ_top (by omega : 1 ≤ a + b + 1)]
    linarith

/-- Draft 536-552, the subtraction step: if the prefix averages `(∑_{n ∈ Icc 1 N} x n) / N` converge to `L`, then the
block averages `(∑_{n ∈ Icc (N+1) (2N)} x n) / N` converge to `L`, since the block equals `2 A_{2N} - A_N`. -/
theorem tendsto_block_average_of_prefix_average (x : ℕ → ℝ) {L : ℝ}
    (h : Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, x n) / (N : ℝ)) atTop (𝓝 L)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc (N + 1) (2 * N), x n) / (N : ℝ)) atTop (𝓝 L) := by
  have h2 : Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 (2 * N), x n) / ((2 * N : ℕ) : ℝ))
      atTop (𝓝 L) :=
    h.comp (tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩)
  have h3 : Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 (2 * N), x n) / (N : ℝ)) atTop
      (𝓝 (2 * L)) := by
    refine Filter.Tendsto.congr (fun N => ?_) (h2.const_mul 2)
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      simp
    · have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      push_cast
      field_simp
  have h4 := h3.sub h
  rw [show 2 * L - L = L by ring] at h4
  refine Filter.Tendsto.congr (fun N => ?_) h4
  have hid := sum_Icc_prefix_add_block x N N
  rw [show N + N = 2 * N by ring] at hid
  rw [← sub_div]
  congr 1
  linarith

open Classical in
/-- Lemma 11.13 at the origin, certificate form (draft lines 515-552). Let `E n` be the scale-`2^{-n}` certificate
events at `z`, with indicator sequence `X n`. Assume:
* `hsub`: each `E n` is contained in the frozen pinch event at scale `2^{-n}` (sufficiency, draft 515-530);
* `hXgerm`: each `X n` is measurable for a germ σ-algebra `germ ε` for all large `n` (locality of the certificates);
* `htrivial`: the germ σ-algebra is trivial (draft 515-534, mixing and ergodicity);
* `hstat`: the indicator law is stationary under the shift (draft 515-530, scale invariance);
* `hpos`: the certificate event at scale `2^{-1}` has positive probability (the mean is positive, Lemma 11.12).
Then there is a deterministic `δ ∈ (0,1)`, chosen before the probability space, with `δ N ≤` the frozen block count
eventually, almost surely. -/
theorem frozen_block_density_of_certificate_family
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ) (U T Q' Q : Set ℂ) (M : ℝ) (z : ℂ)
    (E : ℕ → Set Ω) (X : ℕ → Ω → ℝ) (germ : ℝ → MeasurableSpace Ω)
    (hgle : ∀ ε, 0 < ε → germ ε ≤ mΩ)
    (hEm : ∀ n, MeasurableSet (E n))
    (hX : ∀ n ω, X n ω = if ω ∈ E n then (1 : ℝ) else 0)
    (hsub : ∀ n, E n ⊆ {ω | pinchPointEvent (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z})
    (hXgerm : ∀ ε, 0 < ε → ∃ K, ∀ n, K ≤ n → @Measurable Ω ℝ (germ ε) _ (X n))
    (htrivial : ∀ A : Set Ω, (∀ ε, 0 < ε → MeasurableSet[germ ε] A) → P A = 0 ∨ P A = 1)
    (hstat : P.map (fun ω n => X (n + 2) ω) = P.map (fun ω n => X (n + 1) ω))
    (hpos : 0 < P (E 1)) :
    ∃ δ ∈ Ioo (0 : ℝ) 1, ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop,
      δ * N ≤ ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        pinchPointEvent (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z}.ncard : ℝ) := by
  classical
  have hXm : ∀ n, Measurable (X n) := by
    intro n
    have hfun : X n = fun ω => if ω ∈ E n then (1 : ℝ) else 0 := funext (hX n)
    rw [hfun]
    exact Measurable.ite (hEm n) measurable_const measurable_const
  have hXbound : ∀ n ω, X n ω ∈ Set.Icc (0 : ℝ) 1 := by
    intro n ω
    rw [hX n ω]
    split_ifs <;> norm_num
  have : IsFiniteMeasure (P.map (fun ω n => X (n + 1) ω)) := P.isFiniteMeasure_map _
  have hBirk : PointwiseBirkhoff (P.map (fun ω n => X (n + 1) ω))
      (fun x n => x (n + 1)) (fun x => x 0) :=
    pointwiseBirkhoff_of_latticeProb _ _ _
  have hlim := ae_tendsto_initialScaleAverage_of_stationary_tail_trivial_germ P X germ hgle hXgerm
    htrivial hXm hXbound hBirk hstat
  have hmean : ∫ ω, X 1 ω ∂P = (P (E 1)).toReal := by
    have hfun : (fun ω => X 1 ω) = fun ω => if ω ∈ E 1 then (1 : ℝ) else 0 := funext (hX 1)
    rw [hfun]
    exact integral_event_indicator_eq_measureReal P (E 1) (hEm 1)
  have hm : 0 < (P (E 1)).toReal := ENNReal.toReal_pos (ne_of_gt hpos) (measure_ne_top P _)
  have hδm : min ((P (E 1)).toReal / 2) (1 / 2) < (P (E 1)).toReal :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith)
  refine ⟨min ((P (E 1)).toReal / 2) (1 / 2),
    ⟨lt_min (half_pos hm) (by norm_num), lt_of_le_of_lt (min_le_right _ _) (by norm_num)⟩, ?_⟩
  filter_upwards [hlim] with ω hω
  have hω' : Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, X n ω) / (N : ℝ)) atTop
      (𝓝 (P (E 1)).toReal) := by
    rw [← hmean]
    exact hω
  have hblock := tendsto_block_average_of_prefix_average (fun n => X n ω) hω'
  have hev := (tendsto_order.1 hblock).1 _ hδm
  filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hsum : min ((P (E 1)).toReal / 2) (1 / 2) * N <
      ∑ n ∈ Finset.Icc (N + 1) (2 * N), X n ω := (lt_div_iff₀ hNpos).1 hN
  have hcount : ∑ n ∈ Finset.Icc (N + 1) (2 * N), X n ω ≤ ∑ n ∈ Finset.Icc (N + 1) (2 * N),
      (if pinchPointEvent (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z then (1 : ℝ) else 0) := by
    apply Finset.sum_le_sum
    intro n _
    rw [hX n ω]
    by_cases h1 : ω ∈ E n
    · have h2 : pinchPointEvent (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z := hsub n h1
      simp only [h1, h2, ↓reduceIte, le_refl]
    · simp only [h1, ↓reduceIte]
      split_ifs <;> norm_num
  have hset : ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        pinchPointEvent (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z}) =
      ↑((Finset.Icc (N + 1) (2 * N)).filter
        (fun n => pinchPointEvent (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z)) := by
    ext n
    simp [Finset.mem_Icc, and_assoc]
  have hcard : (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        pinchPointEvent (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z}).ncard : ℝ) =
      ∑ n ∈ Finset.Icc (N + 1) (2 * N),
        (if pinchPointEvent (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z then (1 : ℝ) else 0) := by
    rw [hset, Set.ncard_coe_finset, Finset.sum_boole]
  rw [hcard]
  linarith

end HarmonicBalls
