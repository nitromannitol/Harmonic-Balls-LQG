import HarmonicBalls.Proposed.Birkhoff
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Proposition 11.7, the ergodic frequency of visits (fp-S11c, owner n1)

FIRST-PASS NEW (general measure theory). For an ergodic measure-preserving map `T` of a probability space and a
measurable set `E`, almost every orbit visits `E` with frequency `P(E)`: `#{n < N : T^[n] ω ∈ E} / N → P(E)` for almost
every `ω`. Proof: the repo's pointwise Birkhoff theorem `pointwiseBirkhoff_of_latticeProb` (Proposed/Birkhoff.lean) gives an
almost-sure limit `L`; `L` is invariant (the Birkhoff averages of `T ω` differ from those of `ω` by `O(1/n)`), hence
a.s. constant by Mathlib's ergodic constancy lemma; dominated convergence identifies the constant with `P(E)`.
This is the abstract step behind the frequency of good scales at the origin in the paper's proof of
`lemma:mu_h-bad-and-harnack` (Lemma 11.7, corrected `[C39]`). The stationarity of the scale events is not part of this file.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Set Finset

open Classical in
theorem ae_visit_frequency_tendsto {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : Ω → Ω} (herg : Ergodic T P) {E : Set Ω} (hE : MeasurableSet E) :
    ∀ᵐ ω ∂P, Tendsto (fun N : ℕ => (((range N).filter (fun n => T^[n] ω ∈ E)).card : ℝ) / (N : ℝ)) atTop
      (𝓝 (P E).toReal) := by
  classical
  have hT : MeasurePreserving T P P := herg.toMeasurePreserving
  set f : Ω → ℝ := E.indicator fun _ => (1 : ℝ) with hf_def
  have hf_meas : Measurable f := measurable_const.indicator hE
  have hf_bd : ∀ x, 0 ≤ f x ∧ f x ≤ 1 := by
    intro x
    by_cases hx : x ∈ E <;> simp [hf_def, hx]
  have hf_int : Integrable f P := Integrable.of_bound hf_meas.aestronglyMeasurable 1
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hf_bd x).1]; exact (hf_bd x).2)
  set g : ℕ → Ω → ℝ := fun n x => birkhoffSum T f n x / (n : ℝ) with hg_def
  -- the visit count is the Birkhoff sum
  have hsum : ∀ n x, birkhoffSum T f n x = (((range n).filter (fun k => T^[k] x ∈ E)).card : ℝ) := by
    intro n x
    simp only [birkhoffSum, hf_def, Set.indicator_apply, Finset.sum_boole]
  -- the successor identity for Birkhoff sums
  have hsucc : ∀ n x, birkhoffSum T f (n + 1) x = birkhoffSum T f n (T x) + f x := by
    intro n x
    simp only [birkhoffSum]
    rw [Finset.sum_range_succ', Function.iterate_zero_apply]
    simp only [Function.iterate_succ_apply]
  have hg_meas : ∀ n, Measurable (g n) := by
    intro n
    have : Measurable fun x => birkhoffSum T f n x := by
      unfold birkhoffSum
      exact Finset.measurable_sum _ fun k _ => hf_meas.comp (hT.measurable.iterate k)
    exact this.div_const _
  have hg_bd : ∀ n x, 0 ≤ g n x ∧ g n x ≤ 1 := by
    intro n x
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hg_def, birkhoffSum]
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      have hS0 : 0 ≤ birkhoffSum T f n x := Finset.sum_nonneg fun k _ => (hf_bd _).1
      have hS1 : birkhoffSum T f n x ≤ n := by
        calc birkhoffSum T f n x ≤ ∑ _k ∈ range n, (1 : ℝ) :=
              Finset.sum_le_sum fun k _ => (hf_bd _).2
          _ = n := by simp
      exact ⟨div_nonneg hS0 hnpos.le, (div_le_one hnpos).2 hS1⟩
  -- the pointwise Birkhoff limit
  have hbirk0 := pointwiseBirkhoff_of_latticeProb P T f hT hf_meas hf_int
  set L : Ω → ℝ := fun x => limUnder atTop (fun n => g n x) with hL_def
  have hbirk : ∀ᵐ x ∂P, Tendsto (fun n => g n x) atTop (𝓝 (L x)) := by
    filter_upwards [hbirk0] with x hx
    exact tendsto_nhds_limUnder hx
  -- measurability of the limit
  have hLmeas : AEStronglyMeasurable L P :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hg_meas n).aestronglyMeasurable) hbirk
  -- invariance of the limit under the map
  have hTgood : ∀ᵐ x ∂P, Tendsto (fun n => g n (T x)) atTop (𝓝 (L (T x))) :=
    hT.quasiMeasurePreserving.ae hbirk
  have hinv : ∀ᵐ x ∂P, L (T x) = L x := by
    filter_upwards [hbirk, hTgood] with x hx hTx
    have key : Tendsto (fun n => g n (T x)) atTop (𝓝 (L x)) := by
      have h1 : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 1) := by
        simpa using (tendsto_const_nhds (x := (1 : ℝ))).add tendsto_one_div_atTop_nhds_zero_nat
      have h2 : Tendsto (fun n : ℕ => g (n + 1) x) atTop (𝓝 (L x)) :=
        hx.comp (tendsto_add_atTop_nat 1)
      have h3 : Tendsto (fun n : ℕ => f x * (1 / (n : ℝ))) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds (x := f x)).mul tendsto_one_div_atTop_nhds_zero_nat
      have h4 := (h1.mul h2).sub h3
      rw [one_mul, sub_zero] at h4
      refine Tendsto.congr' ?_ h4
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
      simp only [hg_def]
      rw [hsucc n x]
      push_cast
      field_simp
      ring
    exact tendsto_nhds_unique hTx key
  -- the limit is a.s. constant by ergodicity
  have hLnull : NullMeasurable L P := (AEStronglyMeasurable.aemeasurable hLmeas).nullMeasurable
  obtain ⟨c, hc⟩ := herg.ae_eq_const_of_ae_eq_comp₀ hLnull hinv
  -- identification of the constant with the probability of `E`
  have hm : ∫ x, f x ∂P = (P E).toReal := by
    rw [hf_def, integral_indicator_const _ hE, smul_eq_mul, mul_one, Measure.real]
  have hfi : ∀ k : ℕ, Integrable (fun x => f (T^[k] x)) P := fun k =>
    Integrable.of_bound ((hf_meas.comp (hT.measurable.iterate k)).aestronglyMeasurable) 1
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf_bd _).1]; exact (hf_bd _).2)
  have hcomp : ∀ k : ℕ, ∫ x, f (T^[k] x) ∂P = (P E).toReal := by
    intro k
    have hmp : MeasurePreserving (T^[k]) P P := hT.iterate k
    calc ∫ x, f (T^[k] x) ∂P = ∫ y, f y ∂(P.map (T^[k])) :=
          (integral_map hmp.measurable.aemeasurable hf_meas.aestronglyMeasurable).symm
      _ = (P E).toReal := by rw [hmp.map_eq, hm]
  have hgint : ∀ n : ℕ, 1 ≤ n → ∫ x, g n x ∂P = (P E).toReal := by
    intro n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    simp only [hg_def]
    rw [integral_div]
    have : ∫ x, birkhoffSum T f n x ∂P = (n : ℝ) * (P E).toReal := by
      unfold birkhoffSum
      rw [integral_finsetSum (range n) (fun k _ => hfi k)]
      simp [hcomp]
    rw [this]
    field_simp
  have hDCT : Tendsto (fun n => ∫ x, g n x ∂P) atTop (𝓝 (∫ x, L x ∂P)) :=
    tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun n => (hg_meas n).aestronglyMeasurable) (integrable_const (1 : ℝ))
      (fun n => Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hg_bd n x).1]; exact (hg_bd n x).2)
      hbirk
  have hconst : Tendsto (fun n => ∫ x, g n x ∂P) atTop (𝓝 ((P E).toReal)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (hgint n hn).symm
  have hLint : ∫ x, L x ∂P = c := by
    rw [integral_congr_ae hc]
    simp
  have hDCT' : Tendsto (fun n => ∫ x, g n x ∂P) atTop (𝓝 c) := by
    rw [← hLint]
    exact hDCT
  have hcm : c = (P E).toReal := tendsto_nhds_unique hDCT' hconst
  filter_upwards [hbirk, hc] with ω hω hcω
  have hωc : L ω = c := hcω
  have hlim : Tendsto (fun n => g n ω) atTop (𝓝 c) := by
    rw [← hωc]
    exact hω
  rw [hcm] at hlim
  exact hlim.congr fun n => by simp only [hg_def, hsum]

end HarmonicBalls
