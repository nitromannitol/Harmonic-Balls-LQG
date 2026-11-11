import Mathlib
import HarmonicBalls.LPStage.GFF

/-!
# Existence of the whole-plane GFF: named ingredients and the elementary moment bound (LP stage)

Owner: worker z6, task fp-phase2-gff-existence-row29. Statement target: `exists_isWholePlaneGFF` (general LP form of
`WholePlaneGFFExistsFrozen`, `HarmonicBalls/FirstPass/S11r/Frozen.lean:39`).

Route (MQ-lh-16 / MQ-lh-17 of `notes/fp-gaps/MATH-ANSWERS.md`):

* B1 (`KolmogorovExtensionStmt`): Kolmogorov extension on an arbitrary index set with the product σ-algebra. Absent from
  pinned Mathlib and from `LatticeProb`; a named hypothesis with its source, not a frozen input.
* B2 (`WholePlaneCovPSDStmt`): positive semidefiniteness of the whole-plane covariance on admissible observables.
  Only a sketch exists (log energy `= (2π)⁻¹ ∫ |∇U|²`, MQ-lh-17 (b)); a named hypothesis, reported as a gap.
* B4: the moment bound. Its elementary real-analysis core is `two_log_max_add_sub_log_le` below (proved). The covariance
  identity `Var(h_r(z) - h_s(w)) = -log r - log s + 2 ∫ log max(|x - w|, s) dρ_{z,r}(x)` is not yet formalized.
* B3: continuity. `LatticeProb.exists_continuous_modification_spaceTime_all`
  (`.lake/packages/lattice-probability/LatticeProb/Prob/ChentsovPiModification.lean:413`) is proved, not Bonanno code;
  the box gluing is not yet formalized.

Nothing here is a frozen input. The named Props below are hypotheses of the statements that use them.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace LatticeProb.Gauss

/-- Kolmogorov extension theorem for an arbitrary index type `ι`, real coordinates, product σ-algebra: a projective
family of probability measures on the finite-dimensional coordinate spaces has a projective limit.
Source: William J. Anderson, *Advanced Probability II Notes*, Theorem 6.0.6, p. 60
(<https://www.math.mcgill.ca/bill/589/589notes.pdf#page=60>); MQ-lh-16 B1 in `notes/fp-gaps/MATH-ANSWERS.md`.
Absent from pinned Mathlib: `Mathlib/MeasureTheory/Constructions/Projective.lean` has uniqueness only (`IsProjectiveLimit`
is defined there, no existence). -/
def KolmogorovExtensionStmt : Prop :=
  ∀ (ι : Type) (P : ∀ J : Finset ι, Measure (∀ _ : J, ℝ)),
    IsProjectiveMeasureFamily (α := fun _ : ι => ℝ) P → (∀ J : Finset ι, IsProbabilityMeasure (P J)) →
      ∃ μ : Measure (ι → ℝ), IsProbabilityMeasure μ ∧ IsProjectiveLimit (α := fun _ : ι => ℝ) μ P

/-- Positive semidefiniteness of the whole-plane covariance on admissible observables: for every finite family of
admissible observables `o_i` and real `c_i`, `∑ c_i c_j wholePlaneGFFCov o_i o_j ≥ 0`.
Sketch (not a written proof): with `σ = ∑ c_i σ_i` (signed smearing measures), `m = σ(ℂ)` and `ν = σ - m ρ` (ρ the uniform
probability on the unit circle), the form equals `-∬ log|x - y| dν dν = (2π)⁻¹ ∫ |∇U|²` with `U = -log|·| * ν`
(MQ-lh-17 (b), `notes/fp-gaps/MATH-ANSWERS.md`). The limit from smooth regularizations is not written out.
Named hypothesis: the operator must source it before any consumer is unconditional. -/
def WholePlaneCovPSDStmt : Prop :=
  ∀ (n : ℕ) (o : Fin n → GFFObservable.Admissible) (c : Fin n → ℝ),
    0 ≤ ∑ i, ∑ j, c i * c j * wholePlaneGFFCov (o i).1 (o j).1

/-- Elementary bound behind the moment estimate (MQ-lh-17 (b), B4): for `0 < a ≤ r`, `a ≤ s`, `0 ≤ d`,
`2 log (max r s + d) - log r - log s ≤ (|r - s| + 2 d) / a`. -/
theorem two_log_max_add_sub_log_le {a r s d : ℝ} (ha : 0 < a) (har : a ≤ r) (has : a ≤ s) (hd : 0 ≤ d) :
    2 * Real.log (max r s + d) - Real.log r - Real.log s ≤ (|r - s| + 2 * d) / a := by
  have hr0 : 0 < r := lt_of_lt_of_le ha har
  have hs0 : 0 < s := lt_of_lt_of_le ha has
  have hMa : a ≤ max r s := le_max_of_le_left har
  have hM0 : 0 < max r s := lt_of_lt_of_le ha hMa
  -- Step 1: `log (M + d) - log M ≤ d / M ≤ d / a` with `M = max r s`.
  have h1 : Real.log (max r s + d) - Real.log (max r s) ≤ d / a := by
    rw [← Real.log_div (by positivity) hM0.ne']
    have hlog := Real.log_le_sub_one_of_pos (show 0 < (max r s + d) / max r s by positivity)
    have h2 : (max r s + d) / max r s - 1 = d / max r s := by
      field_simp
      ring
    have h3 : d / max r s ≤ d / a := div_le_div_of_nonneg_left hd ha hMa
    linarith
  -- Step 2: `2 log M - log r - log s ≤ |r - s| / a`.
  have h4 : 2 * Real.log (max r s) - Real.log r - Real.log s ≤ |r - s| / a := by
    rcases le_total r s with hrs | hrs
    · have hM : max r s = s := max_eq_right hrs
      rw [hM]
      have hlog := Real.log_le_sub_one_of_pos (show 0 < s / r by positivity)
      rw [Real.log_div hs0.ne' hr0.ne'] at hlog
      have h5 : (s / r - 1) = (s - r) / r := by
        field_simp
      have h6 : (s - r) / r ≤ (s - r) / a := div_le_div_of_nonneg_left (by linarith) ha har
      have h7 : |r - s| = s - r := by
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      rw [h7]
      linarith
    · have hM : max r s = r := max_eq_left hrs
      rw [hM]
      have hlog := Real.log_le_sub_one_of_pos (show 0 < r / s by positivity)
      rw [Real.log_div hr0.ne' hs0.ne'] at hlog
      have h5 : (r / s - 1) = (r - s) / s := by
        field_simp
      have h6 : (r - s) / s ≤ (r - s) / a := div_le_div_of_nonneg_left (by linarith) ha has
      have h7 : |r - s| = r - s := abs_of_nonneg (by linarith)
      rw [h7]
      linarith
  -- Combine: `2 log (M + d) - log r - log s = 2 (log (M + d) - log M) + (2 log M - log r - log s)`.
  have h8 : (|r - s| + 2 * d) / a = |r - s| / a + 2 * d / a := by ring
  have h9 : 2 * d / a = 2 * (d / a) := by ring
  linarith

end LatticeProb.Gauss
