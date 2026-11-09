import HarmonicBalls.FirstPass.S8c.PhaseTail
import HarmonicBalls.FirstPass.Frozen.S8c

/-! # Block frequencies from Cesàro averages (FIRST-PASS fp-S8c-8-2-local, deterministic step of G-8-2 section 3)

If the Cesàro averages `(1/k) Σ_{n<k} x n` of a real sequence converge to `q > 1 - ζ`, then the block sums
`Σ_{n ∈ [N+1, 2N]} x n` eventually exceed `(1 - ζ) N`. This is the deterministic step after the pointwise ergodic
theorem in G-8-2 section 3 (the block sum over `(N, 2N]` is the difference of two partial sums, and each partial sum
is asymptotically its Cesàro average times its length). Purely real analysis; no probability.
-/

open Filter Topology Finset

universe u

namespace HarmonicBalls

/-- The block sum over `[N+1, 2N]` is the difference of two initial sums. -/
theorem sum_Icc_block_eq (x : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Icc (N + 1) (2 * N), x n =
      ∑ n ∈ range (2 * N + 1), x n - ∑ n ∈ range (N + 1), x n := by
  have h1 : Icc (N + 1) (2 * N) = Ico (N + 1) (2 * N + 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [h1, Finset.range_eq_Ico, Finset.range_eq_Ico]
  rw [← Finset.sum_Ico_consecutive x (Nat.zero_le (N + 1)) (by omega : N + 1 ≤ 2 * N + 1)]
  ring

/-- Block frequencies: Cesàro averages converging to `q > 1 - ζ` give eventually `(1 - ζ) N` ones in each block. -/
theorem eventually_block_sum_ge_of_average_tendsto (x : ℕ → ℝ) (q ζ : ℝ) (hq : 1 - ζ < q)
    (hlim : Tendsto (fun k : ℕ => (∑ n ∈ range k, x n) / (k : ℝ)) atTop (𝓝 q)) :
    ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤ ∑ n ∈ Icc (N + 1) (2 * N), x n := by
  have hA2 : Tendsto (fun N : ℕ => (∑ n ∈ range (2 * N + 1), x n) / ((2 * N + 1 : ℕ) : ℝ))
      atTop (𝓝 q) :=
    hlim.comp (tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩)
  have hA1 : Tendsto (fun N : ℕ => (∑ n ∈ range (N + 1), x n) / ((N + 1 : ℕ) : ℝ))
      atTop (𝓝 q) :=
    hlim.comp (tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩)
  have hL : Tendsto (fun N : ℕ =>
      (2 + 1 / (N : ℝ)) * ((∑ n ∈ range (2 * N + 1), x n) / ((2 * N + 1 : ℕ) : ℝ)) -
      (1 + 1 / (N : ℝ)) * ((∑ n ∈ range (N + 1), x n) / ((N + 1 : ℕ) : ℝ)))
      atTop (𝓝 ((2 + 0) * q - (1 + 0) * q)) := by
    apply Tendsto.sub
    · exact (tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat).mul hA2
    · exact (tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat).mul hA1
  have hval : (2 + 0) * q - (1 + 0) * q = q := by ring
  rw [hval] at hL
  have hD : Tendsto (fun N : ℕ => (∑ n ∈ Icc (N + 1) (2 * N), x n) / (N : ℝ)) atTop (𝓝 q) := by
    refine hL.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpos : (N : ℝ) ≠ 0 := by
      have : (0 : ℝ) < N := by exact_mod_cast hN
      exact this.ne'
    rw [sum_Icc_block_eq x N]
    push_cast
    field_simp
  filter_upwards [hD.eventually (lt_mem_nhds hq), eventually_ge_atTop 1] with N hN hN1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  exact ((lt_div_iff₀ hNpos).mp hN).le

/-- Frequency almost surely from the pointwise ergodic theorem: if `f` has mean above `1 - ζ` under an ergodic
measure-preserving `T`, then almost every orbit has eventually `(1 - ζ) N` ones in each block `[N+1, 2N]`.
The ergodic theorem is the frozen input `BirkhoffPointwiseErgodic`. -/
theorem ae_eventually_frequency_of_birkhoff (hB : BirkhoffPointwiseErgodic.{u}) {Y : Type u}
    [MeasurableSpace Y] (ν : MeasureTheory.Measure Y) [MeasureTheory.IsProbabilityMeasure ν]
    (T : Y → Y) (f : Y → ℝ) (ζ : ℝ) (hT : MeasureTheory.MeasurePreserving T ν ν)
    (herg : Ergodic T ν) (hf : Measurable f) (hbd : ∀ y, |f y| ≤ 1)
    (hmean : 1 - ζ < ∫ z, f z ∂ν) :
    ∀ᵐ y ∂ν, ∀ᶠ N : ℕ in atTop,
      (1 - ζ) * (N : ℝ) ≤ ∑ n ∈ Finset.Icc (N + 1) (2 * N), f (T^[n] y) := by
  filter_upwards [hB Y ν T f hT herg hf hbd] with y hy
  exact eventually_block_sum_ge_of_average_tendsto (fun n => f (T^[n] y)) _ ζ hmean hy

#print axioms eventually_block_sum_ge_of_average_tendsto

end HarmonicBalls
