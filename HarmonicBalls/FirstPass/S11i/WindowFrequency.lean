import HarmonicBalls.FirstPass.S11i.MixingCanonical
import HarmonicBalls.FirstPass.Frozen.S8c

/-!
# Window frequencies of the canonical dilation (fp-S11i, owner n3; write-up Step 7.1, eqs. (16)-(17))

FIRST-PASS NEW (general measure theory, with one external input). For an ergodic measure-preserving map `T` of a
probability space `ν` and a measurable set `E`, the window frequency `#{n ∈ [N+1, 2N] : T^[n] y ∈ E} / N` tends to `ν E`
for almost every `y`. The external input is Birkhoff's pointwise ergodic theorem, the frozen Prop
`BirkhoffPointwiseErgodic` (`HarmonicBalls/FirstPass/Frozen/S8c.lean:72`; Birkhoff 1931; Walters, GTM 79, Thm 1.14),
which is reused and not re-frozen. The canonical instance uses the dilation `dilOp` of the canonical law of the whole-plane
field (`MixingCanonical.lean`), which is ergodic by `ergodic_dilOp`.

The window identity is the one of write-up eq. (17): `(1/N) ∑_{n=N+1}^{2N} a_n = 2 A_{2N} - A_N` with Cesàro means `A`.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Topology Finset

/-- If the Cesàro means `(1/k) ∑_{n<k} a n` tend to `p`, then so do the window means `(1/N) ∑_{n=N+1}^{2N} a n`
(write-up eq. (17)). -/
theorem tendsto_window_average_of_cesaro {a : ℕ → ℝ} {p : ℝ}
    (h : Tendsto (fun k : ℕ => (∑ n ∈ range k, a n) / (k : ℝ)) atTop (𝓝 p)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc (N + 1) (2 * N), a n) / (N : ℝ)) atTop (𝓝 p) := by
  have h1 : Tendsto (fun N : ℕ => (∑ n ∈ range (2 * N + 1), a n) / ((2 * N + 1 : ℕ) : ℝ)) atTop (𝓝 p) :=
    h.comp (tendsto_atTop_atTop.2 fun b => ⟨b, fun N hN => by omega⟩)
  have h2 : Tendsto (fun N : ℕ => (∑ n ∈ range (N + 1), a n) / ((N + 1 : ℕ) : ℝ)) atTop (𝓝 p) :=
    h.comp (tendsto_add_atTop_nat 1)
  have hI : ∀ N : ℕ, ∑ n ∈ Icc (N + 1) (2 * N), a n =
      ∑ n ∈ range (2 * N + 1), a n - ∑ n ∈ range (N + 1), a n := by
    intro N
    have hset : Icc (N + 1) (2 * N) = Ico (N + 1) (2 * N + 1) := by
      ext n; simp only [mem_Icc, mem_Ico]; omega
    have hc := Finset.sum_Ico_consecutive a (Nat.zero_le (N + 1)) (show N + 1 ≤ 2 * N + 1 by omega)
    rw [hset]
    simp only [Finset.range_eq_Ico]
    linarith
  have key : ∀ N : ℕ, 1 ≤ N → (∑ n ∈ Icc (N + 1) (2 * N), a n) / (N : ℝ) =
      (2 + 1 / (N : ℝ)) * ((∑ n ∈ range (2 * N + 1), a n) / ((2 * N + 1 : ℕ) : ℝ))
        - (1 + 1 / (N : ℝ)) * ((∑ n ∈ range (N + 1), a n) / ((N + 1 : ℕ) : ℝ)) := by
    intro N hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    have hN1 : (N : ℝ) + 1 ≠ 0 := by positivity
    rw [hI N]
    push_cast
    field_simp
  have hlim : Tendsto (fun N : ℕ => (2 + 1 / (N : ℝ)) * ((∑ n ∈ range (2 * N + 1), a n) / ((2 * N + 1 : ℕ) : ℝ))
      - (1 + 1 / (N : ℝ)) * ((∑ n ∈ range (N + 1), a n) / ((N + 1 : ℕ) : ℝ))) atTop
      (𝓝 ((2 + 0) * p - (1 + 0) * p)) := by
    refine Tendsto.sub (Tendsto.mul ?_ h1) (Tendsto.mul ?_ h2)
    · exact tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
    · exact tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
  have hp : (2 + 0 : ℝ) * p - (1 + 0) * p = p := by ring
  rw [hp] at hlim
  exact hlim.congr' (eventually_atTop.2 ⟨1, fun N hN => (key N hN).symm⟩)

/-- Window frequency of a measurable set for an ergodic measure-preserving map: for almost every `y`, the frequency of
the visits `T^[n] y ∈ E`, `n ∈ [N+1, 2N]`, divided by `N`, tends to `ν E`. Input: Birkhoff's theorem `hB`. -/
theorem ae_window_frequency_tendsto (hB : BirkhoffPointwiseErgodic.{0}) {Y : Type} [MeasurableSpace Y]
    (ν : Measure Y) [IsProbabilityMeasure ν] {T : Y → Y} (hT : MeasurePreserving T ν ν) (herg : Ergodic T ν)
    {E : Set Y} (hE : MeasurableSet E) :
    ∀ᵐ y ∂ν, Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc (N + 1) (2 * N), E.indicator (fun _ : Y => (1 : ℝ)) (T^[n] y)) / (N : ℝ))
      atTop (𝓝 (ν E).toReal) := by
  have hf : Measurable (E.indicator (fun _ : Y => (1 : ℝ))) := measurable_const.indicator hE
  have hbd : ∀ y, |E.indicator (fun _ : Y => (1 : ℝ)) y| ≤ 1 := by
    intro y
    by_cases hy : y ∈ E <;> simp [hy]
  have hA := hB Y ν T (E.indicator (fun _ : Y => (1 : ℝ))) hT herg hf hbd
  have hint : ∫ z, E.indicator (fun _ : Y => (1 : ℝ)) z ∂ν = (ν E).toReal := by
    rw [integral_indicator_const (1 : ℝ) hE]
    simp [measureReal_def]
  rw [hint] at hA
  filter_upwards [hA] with y hy
  exact tendsto_window_average_of_cesaro hy

/-- The canonical window frequency: for the canonical law of the whole-plane field (modulo constants, mean-zero tests)
and its dilation `dilOp` (write-up Step 7.1), almost every pairing `L` satisfies
`#{n ∈ [N+1,2N] : dilOp^[n] L ∈ E} / N → canonicalLaw E` for every measurable `E`. -/
theorem ae_canonical_window_frequency {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    (hB : BirkhoffPointwiseErgodic.{0})
    {E : Set (ModConstTestPairings (Set.univ : Set ℂ))} (hE : MeasurableSet E) :
    ∀ᵐ L ∂(canonicalLaw hC P), Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc (N + 1) (2 * N), E.indicator (fun _ => (1 : ℝ)) (dilOp^[n] L)) / (N : ℝ))
      atTop (𝓝 ((canonicalLaw hC P E).toReal)) := by
  have := isProbabilityMeasure_canonicalLaw hh
  exact ae_window_frequency_tendsto hB (canonicalLaw hC P) (measurePreserving_dilOp hh) (ergodic_dilOp hh) hE

end HarmonicBalls
