import Mathlib
import HarmonicBalls.Defs.LQGMetric
import HarmonicBalls.FirstPass.S11ah.Radial

/-!
# Transport of a local length metric on a disc to the whole plane
(fp-S11ah-11-13-steps-4-5, owner n4; auxiliary to `S11ah/LocalMeasurable.lean`.)

`IsLengthMetricOn B D`: `D` is a Euclidean length metric on the open set `B` (the local analogue of
`IsEuclideanLengthMetric`; the internal metric is taken in `B`). For a disc `B = ball c R` and the radial
homeomorphism `radialLift c ρ R : ℂ ≃ₜ ball c R` (identity on `closedBall c ρ`), the lifted metric
`liftMetric D x y = D (radialLift x) (radialLift y)` is an `IsEuclideanLengthMetric` on `ℂ`
(`isEuclideanLengthMetric_liftMetric`), with `internalMetric (liftMetric D) univ = internalMetric D B ∘ radialLift`
(paths in `ℂ` and paths in `B` correspond through the homeomorphism and have equal `D`-lengths).
-/

open Metric Set Filter Topology HarmonicBalls

noncomputable section

namespace FirstPassS11ah

/-- `D` is a Euclidean length metric on the open set `B`: the metric axioms on `B`, continuity on `B × B`,
the `D`-open subsets of `B` are the Euclidean open ones, and `D = D(·,·; B)` (length property) on `B`. -/
structure IsLengthMetricOn (B : Set ℂ) (D : ℂ → ℂ → ℝ) : Prop where
  self_eq_zero : ∀ z ∈ B, D z z = 0
  eq_of_eq_zero : ∀ z ∈ B, ∀ w ∈ B, D z w = 0 → z = w
  symm : ∀ z ∈ B, ∀ w ∈ B, D z w = D w z
  triangle : ∀ x ∈ B, ∀ y ∈ B, ∀ z ∈ B, D x z ≤ D x y + D y z
  continuousOn : ContinuousOn (fun q : ℂ × ℂ => D q.1 q.2) (B ×ˢ B)
  isOpen_iff : ∀ U ⊆ B, (IsOpen U ↔ ∀ z ∈ U, ∃ ε > 0, ∀ w ∈ B, D z w < ε → w ∈ U)
  ofReal_eq_internalMetric : ∀ z ∈ B, ∀ w ∈ B, ENNReal.ofReal (D z w) = internalMetric D B z w

lemma IsLengthMetricOn.nonneg {B : Set ℂ} {D : ℂ → ℂ → ℝ} (hD : IsLengthMetricOn B D) {x y : ℂ}
    (hx : x ∈ B) (hy : y ∈ B) : 0 ≤ D x y := by
  have h1 := hD.triangle x hx y hy x hx
  rw [hD.self_eq_zero x hx, hD.symm y hy x hx] at h1
  linarith

section Lift

variable {c : ℂ} {ρ R : ℝ}

lemma radialLift_mem (hρ : 0 < ρ) (hR : ρ < R) (x : ℂ) : radialLift c ρ R x ∈ ball c R :=
  (radialHomeo c hρ hR x).2

lemma radialLiftInv_radialLift (hρ : 0 < ρ) (hR : ρ < R) (x : ℂ) :
    radialLiftInv c ρ R (radialLift c ρ R x) = x := by
  unfold radialLiftInv radialLift
  have h1 : c + radialOut ρ R (x - c) - c = radialOut ρ R (x - c) := by ring
  rw [h1, radialIn_radialOut hρ hR]
  ring

lemma radialLift_radialLiftInv (hρ : 0 < ρ) (hR : ρ < R) {y : ℂ} (hy : y ∈ ball c R) :
    radialLift c ρ R (radialLiftInv c ρ R y) = y := by
  have hy' : ‖y - c‖ < R := by
    rw [Metric.mem_ball, dist_eq_norm] at hy
    exact hy
  unfold radialLift radialLiftInv
  have h1 : c + radialIn ρ R (y - c) - c = radialIn ρ R (y - c) := by ring
  rw [h1, radialOut_radialIn hρ hR hy']
  ring

lemma radialLift_injective (hρ : 0 < ρ) (hR : ρ < R) :
    Function.Injective (radialLift c ρ R) :=
  Function.LeftInverse.injective (radialLiftInv_radialLift hρ hR)

lemma radialLift_continuous (hρ : 0 < ρ) (hR : ρ < R) : Continuous (radialLift c ρ R) :=
  continuous_const.add ((radialOut_continuous hρ hR).comp (continuous_id.sub continuous_const))

lemma radialLiftInv_continuousAt (hρ : 0 < ρ) (hR : ρ < R) {y : ℂ} (hy : y ∈ ball c R) :
    ContinuousAt (radialLiftInv c ρ R) y := by
  have hy' : ‖y - c‖ < R := by
    rw [Metric.mem_ball, dist_eq_norm] at hy
    exact hy
  have hsub : ContinuousAt (fun z : ℂ => z - c) y := continuousAt_id.sub continuousAt_const
  have hrad : ContinuousAt (radialIn ρ R) (y - c) := radialIn_continuousAt hρ hR hy'
  exact continuousAt_const.add (ContinuousAt.comp (f := fun z : ℂ => z - c) (x := y) hrad hsub)

lemma radialLiftInv_continuousOn (hρ : 0 < ρ) (hR : ρ < R) :
    ContinuousOn (radialLiftInv c ρ R) (ball c R) :=
  fun _ hy => (radialLiftInv_continuousAt hρ hR hy).continuousWithinAt

lemma isOpen_iff_image (hρ : 0 < ρ) (hR : ρ < R) (U : Set ℂ) :
    IsOpen U ↔ IsOpen (radialLift c ρ R '' U) := by
  constructor
  · intro hU
    have heq : radialLift c ρ R '' U = ball c R ∩ radialLiftInv c ρ R ⁻¹' U := by
      ext v
      constructor
      · rintro ⟨u, hu, rfl⟩
        refine ⟨radialLift_mem hρ hR u, ?_⟩
        simp only [mem_preimage, radialLiftInv_radialLift hρ hR]
        exact hu
      · rintro ⟨hv, hv'⟩
        exact ⟨radialLiftInv c ρ R v, hv', radialLift_radialLiftInv hρ hR hv⟩
    rw [heq]
    exact (radialLiftInv_continuousOn hρ hR).isOpen_inter_preimage isOpen_ball hU
  · intro hV
    have hpre : U = radialLift c ρ R ⁻¹' (radialLift c ρ R '' U) :=
      (preimage_image_eq U (radialLift_injective hρ hR)).symm
    rw [hpre]
    exact hV.preimage (radialLift_continuous hρ hR)

/-- The lifted metric `D (radialLift x) (radialLift y)` on the whole plane. -/
def liftMetric (c : ℂ) (ρ R : ℝ) (D : ℂ → ℂ → ℝ) : ℂ → ℂ → ℝ :=
  fun x y => D (radialLift c ρ R x) (radialLift c ρ R y)

lemma curveLength_congr {D₁ D₂ : ℂ → ℂ → ℝ} {p p' : ℝ → ℂ} {a b : ℝ}
    (h : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, D₁ (p s) (p t) = D₂ (p' s) (p' t)) :
    curveLength D₁ p a b = curveLength D₂ p' a b := by
  unfold curveLength
  refine iSup_congr fun q => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  exact congrArg ENNReal.ofReal (h _ (q.2.2.2 (i + 1)) _ (q.2.2.2 i))

lemma extend_eq_on {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : γ.extend s = γ ⟨s, hs⟩ :=
  Path.extend_extends' γ ⟨s, hs⟩

/-- Pull a path of `ball c R` back to a path of `ℂ` with the same `D`-length for the lifted metric. -/
lemma exists_path_pathLength_eq (hρ : 0 < ρ) (hR : ρ < R) {D : ℂ → ℂ → ℝ} {x y : ℂ}
    (Q : Path (radialLift c ρ R x) (radialLift c ρ R y)) (hQ : ∀ t, Q t ∈ ball c R) :
    ∃ P : Path x y, pathLength (liftMetric c ρ R D) P = pathLength D Q := by
  let P : Path x y :=
    { toFun := fun t => radialLiftInv c ρ R (Q t)
      continuous_toFun := (radialLiftInv_continuousOn hρ hR).comp_continuous Q.continuous hQ
      source' := by
        show radialLiftInv c ρ R (Q 0) = x
        rw [Q.source, radialLiftInv_radialLift hρ hR]
      target' := by
        show radialLiftInv c ρ R (Q 1) = y
        rw [Q.target, radialLiftInv_radialLift hρ hR] }
  refine ⟨P, ?_⟩
  unfold pathLength
  refine curveLength_congr fun s hs t ht => ?_
  have hPs : P.extend s = radialLiftInv c ρ R (Q.extend s) := by
    rw [extend_eq_on P hs, extend_eq_on Q hs]
    rfl
  have hPt : P.extend t = radialLiftInv c ρ R (Q.extend t) := by
    rw [extend_eq_on P ht, extend_eq_on Q ht]
    rfl
  have hQs : Q.extend s ∈ ball c R := by
    rw [extend_eq_on Q hs]
    exact hQ _
  have hQt : Q.extend t ∈ ball c R := by
    rw [extend_eq_on Q ht]
    exact hQ _
  unfold liftMetric
  rw [hPs, hPt, radialLift_radialLiftInv hρ hR hQs, radialLift_radialLiftInv hρ hR hQt]

/-- Push a path of `ℂ` forward to a path of `ball c R` with the same `D`-length. -/
lemma pathLength_map_eq (hρ : 0 < ρ) (hR : ρ < R) {D : ℂ → ℂ → ℝ} {x y : ℂ} (P : Path x y) :
    ∃ Q : Path (radialLift c ρ R x) (radialLift c ρ R y),
      (∀ t, Q t ∈ ball c R) ∧ pathLength (liftMetric c ρ R D) P = pathLength D Q := by
  let Q : Path (radialLift c ρ R x) (radialLift c ρ R y) := P.map (radialLift_continuous hρ hR)
  refine ⟨Q, fun t => radialLift_mem hρ hR (P t), ?_⟩
  unfold pathLength
  refine curveLength_congr fun s hs t ht => ?_
  have hQs : Q.extend s = radialLift c ρ R (P.extend s) := by
    rw [extend_eq_on Q hs, extend_eq_on P hs]
    rfl
  have hQt : Q.extend t = radialLift c ρ R (P.extend t) := by
    rw [extend_eq_on Q ht, extend_eq_on P ht]
    rfl
  rw [hQs, hQt]
  rfl

/-- The internal metric of the lifted metric on the whole plane is the internal metric of `D` on the disc. -/
theorem internalMetric_liftMetric_univ (hρ : 0 < ρ) (hR : ρ < R) (D : ℂ → ℂ → ℝ) (x y : ℂ) :
    internalMetric (liftMetric c ρ R D) univ x y
      = internalMetric D (ball c R) (radialLift c ρ R x) (radialLift c ρ R y) := by
  apply le_antisymm
  · refine le_iInf₂ fun Q hQ => ?_
    obtain ⟨P, hP⟩ := exists_path_pathLength_eq (c := c) hρ hR (D := D) Q hQ
    exact (iInf₂_le P (fun t => mem_univ _)).trans (le_of_eq hP)
  · refine le_iInf₂ fun P _ => ?_
    obtain ⟨Q, hQ, hP⟩ := pathLength_map_eq (c := c) hρ hR (D := D) P
    exact (iInf₂_le Q hQ).trans (le_of_eq hP.symm)

theorem isEuclideanLengthMetric_liftMetric (hρ : 0 < ρ) (hR : ρ < R) {D : ℂ → ℂ → ℝ}
    (hD : IsLengthMetricOn (ball c R) D) :
    IsEuclideanLengthMetric (liftMetric c ρ R D) where
  self_eq_zero z := hD.self_eq_zero _ (radialLift_mem hρ hR z)
  eq_of_eq_zero z w h := by
    have h' := hD.eq_of_eq_zero _ (radialLift_mem hρ hR z) _ (radialLift_mem hρ hR w) h
    have := congrArg (radialLiftInv c ρ R) h'
    rwa [radialLiftInv_radialLift hρ hR, radialLiftInv_radialLift hρ hR] at this
  symm z w := hD.symm _ (radialLift_mem hρ hR z) _ (radialLift_mem hρ hR w)
  triangle x y z :=
    hD.triangle _ (radialLift_mem hρ hR x) _ (radialLift_mem hρ hR y) _ (radialLift_mem hρ hR z)
  isOpen_iff U := by
    rw [isOpen_iff_image hρ hR U,
      hD.isOpen_iff _ (image_subset_iff.2 fun u _ => radialLift_mem hρ hR u)]
    constructor
    · intro H z hz
      obtain ⟨ε, hε, H'⟩ := H _ ⟨z, hz, rfl⟩
      refine ⟨ε, hε, fun w hw => ?_⟩
      obtain ⟨u, hu, hu'⟩ := H' _ (radialLift_mem hρ hR w) hw
      have huw : u = w := radialLift_injective hρ hR hu'
      rw [← huw]
      exact hu
    · rintro H _ ⟨u, hu, rfl⟩
      obtain ⟨ε, hε, H'⟩ := H u hu
      refine ⟨ε, hε, fun w hwB hw => ⟨radialLiftInv c ρ R w, ?_, radialLift_radialLiftInv hρ hR hwB⟩⟩
      apply H'
      show D (radialLift c ρ R u) (radialLift c ρ R (radialLiftInv c ρ R w)) < ε
      rw [radialLift_radialLiftInv hρ hR hwB]
      exact hw
  ofReal_eq_internalMetric z w := by
    rw [internalMetric_liftMetric_univ hρ hR]
    exact hD.ofReal_eq_internalMetric _ (radialLift_mem hρ hR z) _ (radialLift_mem hρ hR w)

theorem continuous_liftMetric (hρ : 0 < ρ) (hR : ρ < R) {D : ℂ → ℂ → ℝ}
    (hD : IsLengthMetricOn (ball c R) D) :
    Continuous fun q : ℂ × ℂ => liftMetric c ρ R D q.1 q.2 := by
  have hc : Continuous fun q : ℂ × ℂ => (radialLift c ρ R q.1, radialLift c ρ R q.2) :=
    ((radialLift_continuous hρ hR).comp continuous_fst).prodMk
      ((radialLift_continuous hρ hR).comp continuous_snd)
  have hmaps : ∀ q : ℂ × ℂ, (radialLift c ρ R q.1, radialLift c ρ R q.2) ∈ ball c R ×ˢ ball c R :=
    fun q => ⟨radialLift_mem hρ hR _, radialLift_mem hρ hR _⟩
  exact hD.continuousOn.comp_continuous hc hmaps

/-- Joint measurability of the lifted family, for a family of local length metrics measurable in `ω`. -/
theorem measurable_liftMetric_family {Ω : Type*} [MeasurableSpace Ω] (hρ : 0 < ρ) (hR : ρ < R)
    {D : Ω → ℂ → ℂ → ℝ} (hDm : ∀ x ∈ ball c R, ∀ y ∈ ball c R, Measurable fun ω => D ω x y)
    (hD : ∀ ω, IsLengthMetricOn (ball c R) (D ω)) :
    Measurable fun q : Ω × (ℂ × ℂ) => liftMetric c ρ R (D q.1) q.2.1 q.2.2 := by
  have hc : Continuous fun p : ℂ × ℂ => (radialLift c ρ R p.1, radialLift c ρ R p.2) :=
    ((radialLift_continuous hρ hR).comp continuous_fst).prodMk
      ((radialLift_continuous hρ hR).comp continuous_snd)
  have hmaps : ∀ p : ℂ × ℂ, (radialLift c ρ R p.1, radialLift c ρ R p.2) ∈ ball c R ×ˢ ball c R :=
    fun p => ⟨radialLift_mem hρ hR _, radialLift_mem hρ hR _⟩
  let u : ℂ × ℂ → Ω → ℝ := fun p ω => D ω (radialLift c ρ R p.1) (radialLift c ρ R p.2)
  have hu_cont : ∀ ω, Continuous fun p : ℂ × ℂ => u p ω := fun ω =>
    (hD ω).continuousOn.comp_continuous hc hmaps
  have hu_meas : ∀ p : ℂ × ℂ, Measurable (u p) := fun p =>
    hDm _ (radialLift_mem hρ hR p.1) _ (radialLift_mem hρ hR p.2)
  have hm := (MeasureTheory.measurable_uncurry_of_continuous_of_measurable hu_cont hu_meas).comp
    measurable_swap
  exact hm

end Lift

end FirstPassS11ah

end
