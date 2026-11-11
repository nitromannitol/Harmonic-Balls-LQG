import Mathlib
import HarmonicBalls.Proofs.Sec11.ClosureScales.CountableCircleDecoder
import HarmonicBalls.Proofs.Sec11.ClosureScales.PalmPairingMeasurable

/-! # Borel circle-limit decoder

Source: lines 1313-1323. For an arbitrary `T`, take the limits of the test
evaluations where they exist, decode the resulting countable circle values by the continuous-function decoder
`circleDecoder` (`CountableCircleDecoder`), and return zero on any invalid code. This file formalizes the Borel map `C`
of that passage on the positive-radius carrier `C(CircleDomain, ℝ)`.

Results.
* `exists_measurable_circle_limit_decoder`: for a countable index `I`, a dense family `q : I → CircleDomain`, and
  measurable observations `a i n : S → ℝ` on any measurable space `S`, there is a measurable `C : S → C(CircleDomain, ℝ)`
  with (i) `C s = F` whenever `F` is continuous and `n ↦ a i n s` tends to `F (q i)` for every `i`, and (ii) `C s = 0`
  whenever no continuous `F` has this property. Density of `q` makes such `F` unique (`injective_circleRestrict`), so
  (i) and (ii) determine `C` completely (`circleLimitDecoder_unique`).
* `exists_measurable_circle_limit_decoder_pairing`: the specialization to `S = (ℂ → ℝ) → ℝ` with the pairing
  σ-algebra `pairingMeasSpace` and `a i n T = T (psi i n)`, where each `psi i n` is a test function on `Set.univ`.

Only the countable decoder, Mathlib's measurable-limit lemmas (`measurableSet_exists_tendsto`,
`StronglyMeasurable.limUnder`) and the pairing σ-algebra `pairingMeasSpace` are used. No Gaussian convergence,
reconstruction, raw/profile equality or extra measurable decoder is assumed. The module does not prove the r10
identification of `C` with the circle profile on the conull event, and it does not touch `CanonicalProfile` or
`RawToProfileStep`.
-/

noncomputable section

open MeasureTheory Filter Topology Set

namespace HarmonicBalls

open scoped Classical in
/-- The limit of a real sequence where it exists, and `0` where it does not converge. -/
def seqLimitOrZero (u : ℕ → ℝ) : ℝ :=
  if ∃ l : ℝ, Tendsto u atTop (𝓝 l) then limUnder atTop u else 0

/-- A convergent real sequence takes its limit under `seqLimitOrZero` (uniqueness of limits in `ℝ`). -/
theorem seqLimitOrZero_eq_of_tendsto {u : ℕ → ℝ} {l : ℝ} (h : Tendsto u atTop (𝓝 l)) :
    seqLimitOrZero u = l := by
  have hex : ∃ l' : ℝ, Tendsto u atTop (𝓝 l') := ⟨l, h⟩
  simp only [seqLimitOrZero, hex, ↓reduceIte]
  exact h.limUnder_eq

/-- A real sequence without a limit takes the value `0` under `seqLimitOrZero`. -/
theorem seqLimitOrZero_of_not {u : ℕ → ℝ} (h : ¬ ∃ l : ℝ, Tendsto u atTop (𝓝 l)) :
    seqLimitOrZero u = 0 := by
  simp only [seqLimitOrZero, h, ↓reduceIte]

/-- **Measurability of the sequential limits.** For measurable `a n : S → ℝ`, the map `s ↦ lim_n a n s`, with value
`0` where the sequence does not converge, is measurable: it is the indicator of the convergence locus (measurable by
`measurableSet_exists_tendsto`) of the Mathlib measurable limit `limUnder` (`StronglyMeasurable.limUnder`). The zero
convention off the locus is the one of `measurable_circleTestLimit` (`RouteACodes`). -/
theorem measurable_seqLimitOrZero {S : Type*} [MeasurableSpace S] {a : ℕ → S → ℝ} (ha : ∀ n, Measurable (a n)) :
    Measurable (fun s : S => seqLimitOrZero (fun n => a n s)) := by
  have hG : MeasurableSet {s : S | ∃ l : ℝ, Tendsto (fun n => a n s) atTop (𝓝 l)} :=
    measurableSet_exists_tendsto ha
  have hL : Measurable (fun s : S => limUnder atTop (fun n => a n s)) :=
    (StronglyMeasurable.limUnder (l := atTop) fun n => (ha n).stronglyMeasurable).measurable
  have hfun : (fun s : S => seqLimitOrZero (fun n => a n s)) =
      {s : S | ∃ l : ℝ, Tendsto (fun n => a n s) atTop (𝓝 l)}.indicator
        (fun s : S => limUnder atTop (fun n => a n s)) := by
    funext s
    by_cases hs : ∃ l : ℝ, Tendsto (fun n => a n s) atTop (𝓝 l)
    · have hsG : s ∈ {s : S | ∃ l : ℝ, Tendsto (fun n => a n s) atTop (𝓝 l)} := hs
      obtain ⟨l, hl⟩ := hs
      simp only [indicator_of_mem hsG, seqLimitOrZero_eq_of_tendsto hl, hl.limUnder_eq]
    · have hsG : s ∉ {s : S | ∃ l : ℝ, Tendsto (fun n => a n s) atTop (𝓝 l)} := hs
      simp only [indicator_of_notMem hsG, seqLimitOrZero_of_not hs]
  rw [hfun]
  exact hL.indicator hG

open scoped Classical in
/-- **The Borel circle-limit decoder**. At `s`, if every test sequence
`n ↦ a i n s` converges, it decodes the vector of limits `(lim_n a i n s)_{i ∈ I}` by the countable circle decoder
`circleDecoder q`, which returns `0` on an invalid code; elsewhere it returns `0`. -/
def circleLimitDecoder {S I : Type*} (q : I → CircleDomain) (a : I → ℕ → S → ℝ) (s : S) :
    C(CircleDomain, ℝ) :=
  if ∀ i, ∃ l : ℝ, Tendsto (fun n => a i n s) atTop (𝓝 l) then
    circleDecoder q (fun i => seqLimitOrZero (fun n => a i n s))
  else 0

/-- Characterization (i) for the Borel circle-limit decoder: if `n ↦ a i n s` tends to `F (q i)` for every `i`,
the decoder returns `F`. -/
theorem circleLimitDecoder_of_tendsto {S I : Type*} {q : I → CircleDomain} (hq : DenseRange q)
    {a : I → ℕ → S → ℝ} {s : S} {F : C(CircleDomain, ℝ)}
    (hF : ∀ i, Tendsto (fun n => a i n s) atTop (𝓝 (F (q i)))) :
    circleLimitDecoder q a s = F := by
  have hlim : (fun i => seqLimitOrZero (fun n => a i n s)) = fun i => F (q i) :=
    funext fun i => seqLimitOrZero_eq_of_tendsto (hF i)
  unfold circleLimitDecoder
  split_ifs with h
  · exact (congrArg (circleDecoder q) hlim).trans (circleDecoder_restrict hq F)
  · exact (h fun i => ⟨F (q i), hF i⟩).elim

/-- Characterization (ii) for the Borel circle-limit decoder: if no continuous `F` has `n ↦ a i n s → F (q i)` for
every `i`, the decoder returns `0`. -/
theorem circleLimitDecoder_of_not_exists {S I : Type*} {q : I → CircleDomain} {a : I → ℕ → S → ℝ} {s : S}
    (hns : ¬ ∃ F : C(CircleDomain, ℝ), ∀ i, Tendsto (fun n => a i n s) atTop (𝓝 (F (q i)))) :
    circleLimitDecoder q a s = 0 := by
  unfold circleLimitDecoder
  split_ifs with hcode
  · choose L hL using hcode
    have hlim : (fun i => seqLimitOrZero (fun n => a i n s)) = L :=
      funext fun i => seqLimitOrZero_eq_of_tendsto (hL i)
    refine (congrArg (circleDecoder q) hlim).trans (circleDecoder_of_not_valid q L ?_)
    rintro ⟨F, hF⟩
    refine hns ⟨F, fun i => ?_⟩
    rw [hF i]
    exact hL i
  all_goals rfl

/-- **Existence of the Borel circle-limit decoder.** Let `I` be countable and `q : I → CircleDomain` have dense range.
For measurable observations `a i n : S → ℝ` there is a measurable `C : S → C(CircleDomain, ℝ)` such that
(i) `C s = F` whenever `F` is continuous and `n ↦ a i n s` tends to `F (q i)` for every `i`, and
(ii) `C s = 0` whenever no continuous `F` has this property. -/
theorem exists_measurable_circle_limit_decoder {S I : Type*} [MeasurableSpace S] [Countable I]
    (q : I → CircleDomain) (hq : DenseRange q) (a : I → ℕ → S → ℝ) (ha : ∀ i n, Measurable (a i n)) :
    ∃ C : S → C(CircleDomain, ℝ), Measurable C ∧
      (∀ (s : S) (F : C(CircleDomain, ℝ)),
        (∀ i, Tendsto (fun n => a i n s) atTop (𝓝 (F (q i)))) → C s = F) ∧
      (∀ s : S, (¬ ∃ F : C(CircleDomain, ℝ), ∀ i, Tendsto (fun n => a i n s) atTop (𝓝 (F (q i)))) →
        C s = 0) := by
  refine ⟨circleLimitDecoder q a, ?_, fun s F hF => circleLimitDecoder_of_tendsto hq hF,
    fun s hns => circleLimitDecoder_of_not_exists hns⟩
  have hG : MeasurableSet {s : S | ∀ i, ∃ l : ℝ, Tendsto (fun n => a i n s) atTop (𝓝 l)} := by
    have hset : {s : S | ∀ i, ∃ l : ℝ, Tendsto (fun n => a i n s) atTop (𝓝 l)} =
        ⋂ i, {s : S | ∃ l : ℝ, Tendsto (fun n => a i n s) atTop (𝓝 l)} := by
      ext s
      simp
    rw [hset]
    exact MeasurableSet.iInter fun i => measurableSet_exists_tendsto (ha i)
  have hA : Measurable (fun s : S => fun i => seqLimitOrZero (fun n => a i n s)) :=
    measurable_pi_iff.mpr fun i => measurable_seqLimitOrZero (ha i)
  unfold circleLimitDecoder
  exact Measurable.ite hG ((circleDecoder_measurable hq).comp hA) measurable_const

/-- The two characterizations determine the decoder: any map satisfying (i) and (ii) equals `circleLimitDecoder q a`.
This is the completeness of the characterization, since density of `q` makes the continuous `F` in (i) unique. -/
theorem circleLimitDecoder_unique {S I : Type*} {q : I → CircleDomain} (hq : DenseRange q)
    {a : I → ℕ → S → ℝ} {D : S → C(CircleDomain, ℝ)}
    (h1 : ∀ (s : S) (F : C(CircleDomain, ℝ)), (∀ i, Tendsto (fun n => a i n s) atTop (𝓝 (F (q i)))) → D s = F)
    (h2 : ∀ s : S, (¬ ∃ F : C(CircleDomain, ℝ), ∀ i, Tendsto (fun n => a i n s) atTop (𝓝 (F (q i)))) → D s = 0) :
    D = circleLimitDecoder q a := by
  funext s
  by_cases hex : ∃ F : C(CircleDomain, ℝ), ∀ i, Tendsto (fun n => a i n s) atTop (𝓝 (F (q i)))
  · obtain ⟨F, hF⟩ := hex
    rw [h1 s F hF, circleLimitDecoder_of_tendsto hq hF]
  · rw [h2 s hex, circleLimitDecoder_of_not_exists hex]

/-- Evaluation at a test function on `Set.univ` is measurable for the pairing σ-algebra `pairingMeasSpace`, which is
the supremum of the comaps of the evaluations at the test functions (`PalmPairingMeasurable`). -/
theorem measurable_pairing_eval {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) :
    @Measurable ((ℂ → ℝ) → ℝ) ℝ pairingMeasSpace _ (fun T => T φ) := by
  rw [measurable_iff_comap_le]
  unfold pairingMeasSpace pairingSigmaAlgebra
  exact le_iSup_of_le φ (le_iSup_of_le hφ le_rfl)

/-- **Borel circle-limit decoder on the raw pairing**. For test functions
`psi i n` on `Set.univ`, the map `C` on `(ℂ → ℝ) → ℝ` takes the limits of the test evaluations `T ↦ T (psi i n)`,
decodes them by `circleDecoder q`, and returns zero on an invalid code. It is measurable for the pairing σ-algebra and
has the characterizations (i) and (ii) with `a i n T = T (psi i n)`. -/
theorem exists_measurable_circle_limit_decoder_pairing {I : Type*} [Countable I]
    (q : I → CircleDomain) (hq : DenseRange q) (psi : I → ℕ → ℂ → ℝ)
    (hpsi : ∀ i n, IsTestFunction Set.univ (psi i n)) :
    ∃ C : ((ℂ → ℝ) → ℝ) → C(CircleDomain, ℝ), @Measurable _ _ pairingMeasSpace _ C ∧
      (∀ (T : (ℂ → ℝ) → ℝ) (F : C(CircleDomain, ℝ)),
        (∀ i, Tendsto (fun n => T (psi i n)) atTop (𝓝 (F (q i)))) → C T = F) ∧
      (∀ T : (ℂ → ℝ) → ℝ,
        (¬ ∃ F : C(CircleDomain, ℝ), ∀ i, Tendsto (fun n => T (psi i n)) atTop (𝓝 (F (q i)))) → C T = 0) :=
  @exists_measurable_circle_limit_decoder ((ℂ → ℝ) → ℝ) I pairingMeasSpace _ q hq
    (fun i n T => T (psi i n)) fun i n => measurable_pairing_eval (hpsi i n)

end HarmonicBalls

end
