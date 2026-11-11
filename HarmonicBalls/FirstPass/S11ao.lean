import HarmonicBalls.FirstPass.S11ao.EuclideanBall

/-!
# P-a.s. modification of the local metric decoders

Device for Lemma 11.13. Given a family of local decoders `D ω : ℂ → ℂ → ℝ`, measurable in
`ω` for `x, y` in a disc `B = ball c R`, and an almost-sure statement that each `D ω` is a Euclidean length metric on `B`
(`FirstPassS11ah.IsLengthMetricOn B`), we build a modification `D'` such that:

* `D' ω` is a `IsLengthMetricOn B` metric for **every** `ω` (the input needed in `measurable_localCertLoc`,
  `S11ah/LocalMeasurable.lean`, and in `measurable_liftMetric_family`, `S11ah/LengthTransport.lean`);
* `D'` is measurable in `ω` for `x, y ∈ B` (the input `hDm`);
* there is a measurable set `H` with `P Hᶜ = 0` (full measure) inside the almost-sure set, on which `D' ω = D ω`;
  off `H`, `D' ω` is the Euclidean distance `dist`.

What this file does NOT do: it does not derive the almost-sure input `∀ᵐ ω, IsLengthMetricOn B (D ω)` from the
identities (18) and (20) of `LocalMetricReplacementStmt` (`S11r/LocalMetricReplacement.lean`). The identity fixes the
decoder only where the internal metric is positive, and the length axioms need more. The input is therefore a named hypothesis `hae`.
-/

open MeasureTheory Set Metric
noncomputable section

namespace FirstPassS11ao

/-- **Measurable full-measure subset of an almost-sure property.** If `Q ω` holds `P`-a.s., there is a measurable
set `H` with `P Hᶜ = 0` and `Q ω` for every `ω ∈ H`. (Pattern: `exists_measurable_superset_of_null` as in
`FirstPass/S11j/InnerMeasure.lean`.) -/
theorem exists_measurable_full_subset {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Q : Ω → Prop}
    (hQ : ∀ᵐ ω ∂P, Q ω) : ∃ H : Set Ω, MeasurableSet H ∧ P Hᶜ = 0 ∧ ∀ ω ∈ H, Q ω := by
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hQ)
  refine ⟨Nᶜ, hNm.compl, by simpa using hN0, fun ω hω => ?_⟩
  by_contra hq
  exact hω (hsub hq)

/-- **P-a.s. modification of the local metric decoders** (Lemma 11.13, Option A; pattern
`exists_measurable_lengthMetric_modification`, `Steps/Sec11/CountableClearanceChains.lean:164`).

Hypotheses: the disc (or any convex open set) `B`; the decoders `D` with `hDm` (measurable in `ω` at each pair of
points of `B`) and the almost-sure length-metric property `hae`. Conclusion: a measurable full-measure set `H`
inside the almost-sure set, a modification `D'` that is measurable in `ω` and an `IsLengthMetricOn B` metric for every
`ω`, equal to `D` on `H` and to the Euclidean distance off `H`. -/
theorem exists_measurable_localLengthModification {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : Set ℂ} (hB : Convex ℝ B) (hBo : IsOpen B)
    {D : Ω → ℂ → ℂ → ℝ} (hDm : ∀ x ∈ B, ∀ y ∈ B, Measurable fun ω => D ω x y)
    (hae : ∀ᵐ ω ∂P, FirstPassS11ah.IsLengthMetricOn B (D ω)) :
    ∃ H : Set Ω, MeasurableSet H ∧ P Hᶜ = 0 ∧ ∃ D' : Ω → ℂ → ℂ → ℝ,
      (∀ x ∈ B, ∀ y ∈ B, Measurable fun ω => D' ω x y) ∧
      (∀ ω, FirstPassS11ah.IsLengthMetricOn B (D' ω)) ∧
      (∀ ω ∈ H, FirstPassS11ah.IsLengthMetricOn B (D ω) ∧ D' ω = D ω) ∧
      (∀ ω ∉ H, D' ω = fun z w => dist z w) := by
  classical
  obtain ⟨H, hHm, hH0, hHgood⟩ := exists_measurable_full_subset hae
  refine ⟨H, hHm, hH0, fun ω z w => if ω ∈ H then D ω z w else dist z w, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    exact Measurable.ite hHm (hDm x hx y hy) measurable_const
  · intro ω
    dsimp only
    by_cases hω : ω ∈ H
    · have h := hHgood ω hω
      have hfun : (fun z w => if ω ∈ H then D ω z w else dist z w) = D ω := by
        funext z w
        simp [hω]
      rw [hfun]
      exact h
    · have hfun : (fun z w => if ω ∈ H then D ω z w else dist z w) = fun z w => dist z w := by
        funext z w
        simp [hω]
      rw [hfun]
      exact isLengthMetricOn_dist hB hBo
  · intro ω hω
    refine ⟨hHgood ω hω, ?_⟩
    funext z w
    simp [hω]
  · intro ω hω
    funext z w
    simp [hω]

end FirstPassS11ao

end
