import HarmonicBalls.Proofs.Sec8.RootedLogarithmicShift

/-! # Equivalence under local smooth shifts

The Cameron–Martin theorem used here comes from Leonardo Bonanno's
whole-plane GFF development. The common insertion is allowed to be singular.
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ContDiff

namespace HarmonicBalls

/-- Smooth shifts preserve the null sets of local mean-zero pairing laws,
with an arbitrary common insertion. -/
theorem IsWholePlaneGFF.local_smooth_shift_pairing_equivalence
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {c : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) {g : ℂ → ℝ}
    (hg : ContDiffOn ℝ ∞ g (ball c R))
    (k : Section6.LocalTest (ball c r) → ℝ) :
    let A := P.map (fun o (φ : Section6.LocalTest (ball c r)) =>
      hC o φ.1.1 + (∫ x, φ.1.1 x * g x) + k φ)
    let B := P.map (fun o (φ : Section6.LocalTest (ball c r)) => hC o φ.1.1 + k φ)
    A ≪ B ∧ B ≪ A := by
  dsimp only
  refine ⟨hh.local_smooth_shift_pairing_law hr hrR hg k, ?_⟩
  let gneg : ℂ → ℝ := fun x => -g x
  let knew : Section6.LocalTest (ball c r) → ℝ := fun φ => (∫ x, φ.1.1 x * g x) + k φ
  have hrev := hh.local_smooth_shift_pairing_law hr hrR (g := gneg) hg.neg knew
  have hleft : (fun o (φ : Section6.LocalTest (ball c r)) =>
      hC o φ.1.1 + (∫ x, φ.1.1 x * gneg x) + knew φ) =
      (fun o (φ : Section6.LocalTest (ball c r)) => hC o φ.1.1 + k φ) := by
    funext o φ
    dsimp [gneg, knew]
    simp only [mul_neg, integral_neg]
    ring
  have hright : (fun o (φ : Section6.LocalTest (ball c r)) => hC o φ.1.1 + knew φ) =
      (fun o (φ : Section6.LocalTest (ball c r)) =>
        hC o φ.1.1 + (∫ x, φ.1.1 x * g x) + k φ) := by
    funext o φ
    dsimp [knew]
    ring
  rwa [hleft, hright] at hrev

/-- At a fixed root, an outside logarithmic singularity preserves the null
sets of local pairing laws with a common origin insertion. -/
theorem IsWholePlaneGFF.local_logarithmic_shift_pairing_equivalence
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {c z : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (a b : ℝ)
    (haway : ∀ x ∈ ball c R, z + x ≠ 0) :
    let A := P.map (fun o (φ : Section6.LocalTest (ball c r)) =>
      hC o φ.1.1 + ∫ x, φ.1.1 x * (a * Real.log ‖z + x‖ + b * Real.log ‖x‖))
    let B := P.map (fun o (φ : Section6.LocalTest (ball c r)) =>
      hC o φ.1.1 + ∫ x, φ.1.1 x * (b * Real.log ‖x‖))
    A ≪ B ∧ B ≪ A := by
  have hsmooth : ContDiffOn ℝ ∞ (fun x : ℂ => a * Real.log ‖z + x‖) (ball c R) :=
    contDiffOn_const.mul (contDiffOn_log_norm_add haway)
  have h := hh.local_smooth_shift_pairing_equivalence hr hrR hsmooth
    (fun φ => ∫ x, φ.1.1 x * (b * Real.log ‖x‖))
  simpa only [integral_test_mul_translated_log_add, add_assoc] using h

/-- A root-dependent smooth shift preserves the null sets of the joint local
field-and-root law, even with a common arbitrary insertion. -/
theorem IsWholePlaneGFF.rooted_local_smooth_shift_equivalence
    {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω] (ρ : Measure Z)
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {c : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (g : Z → ℂ → ℝ)
    (k : Z → Section6.LocalTest (ball c r) → ℝ)
    (hg : ∀ᵐ z ∂ρ, ContDiffOn ℝ ∞ (g z) (ball c R))
    (hshift : Measurable (fun p : Z × Ω =>
      fun φ : Section6.LocalTest (ball c r) =>
        hC p.2 φ.1.1 + (∫ x, φ.1.1 x * g p.1 x) + k p.1 φ))
    (hbase : Measurable (fun p : Z × Ω =>
      fun φ : Section6.LocalTest (ball c r) => hC p.2 φ.1.1 + k p.1 φ)) :
    let A := shiftedRootReferenceLaw ρ P (fun p =>
      fun φ : Section6.LocalTest (ball c r) =>
        hC p.2 φ.1.1 + (∫ x, φ.1.1 x * g p.1 x) + k p.1 φ)
    let B := shiftedRootReferenceLaw ρ P (fun p =>
      fun φ : Section6.LocalTest (ball c r) => hC p.2 φ.1.1 + k p.1 φ)
    A ≪ B ∧ B ≪ A := by
  dsimp only
  refine ⟨hh.rooted_local_smooth_shift_law ρ hr hrR g k hg hshift hbase, ?_⟩
  let negG : Z → ℂ → ℝ := fun z x => -g z x
  let newK : Z → Section6.LocalTest (ball c r) → ℝ := fun z φ =>
    (∫ x, φ.1.1 x * g z x) + k z φ
  have hneg : ∀ᵐ z ∂ρ, ContDiffOn ℝ ∞ (negG z) (ball c R) := by
    filter_upwards [hg] with z hz
    exact hz.neg
  have hleft : (fun p : Z × Ω => fun φ : Section6.LocalTest (ball c r) =>
      hC p.2 φ.1.1 + (∫ x, φ.1.1 x * negG p.1 x) + newK p.1 φ) =
      (fun p : Z × Ω => fun φ : Section6.LocalTest (ball c r) =>
        hC p.2 φ.1.1 + k p.1 φ) := by
    funext p φ
    dsimp [negG, newK]
    simp only [mul_neg, integral_neg]
    ring
  have hright : (fun p : Z × Ω => fun φ : Section6.LocalTest (ball c r) =>
      hC p.2 φ.1.1 + newK p.1 φ) =
      (fun p : Z × Ω => fun φ : Section6.LocalTest (ball c r) =>
        hC p.2 φ.1.1 + (∫ x, φ.1.1 x * g p.1 x) + k p.1 φ) := by
    funext p φ
    dsimp [newK]
    ring
  have hleftMeas : Measurable (fun p : Z × Ω =>
      fun φ : Section6.LocalTest (ball c r) =>
        hC p.2 φ.1.1 + (∫ x, φ.1.1 x * negG p.1 x) + newK p.1 φ) := by
    rw [hleft]
    exact hbase
  have hrightMeas : Measurable (fun p : Z × Ω =>
      fun φ : Section6.LocalTest (ball c r) => hC p.2 φ.1.1 + newK p.1 φ) := by
    rw [hright]
    exact hshift
  have h := hh.rooted_local_smooth_shift_law ρ hr hrR negG newK hneg hleftMeas hrightMeas
  rwa [hleft, hright] at h

/-- Jointly measurable insertion functions yield equivalent local rooted laws
whenever their difference is smooth on a buffered ball. -/
theorem IsWholePlaneGFF.rooted_local_smooth_insertion_equivalence
    {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω] (ρ : Measure Z)
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {c : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (g k : Z → ℂ → ℝ)
    (hg : Measurable (Function.uncurry g)) (hk : Measurable (Function.uncurry k))
    (hsmooth : ∀ᵐ z ∂ρ, ContDiffOn ℝ ∞ (g z) (ball c R)) :
    let A := shiftedRootReferenceLaw ρ P (fun p =>
      fun φ : Section6.LocalTest (ball c r) =>
        hC p.2 φ.1.1 + (∫ x, φ.1.1 x * g p.1 x) + ∫ x, φ.1.1 x * k p.1 x)
    let B := shiftedRootReferenceLaw ρ P (fun p =>
      fun φ : Section6.LocalTest (ball c r) => hC p.2 φ.1.1 + ∫ x, φ.1.1 x * k p.1 x)
    A ≪ B ∧ B ≪ A := by
  dsimp only
  apply hh.rooted_local_smooth_shift_equivalence ρ hr hrR g
    (fun z φ => ∫ x, φ.1.1 x * k z x) hsmooth
  · apply measurable_pi_iff.mpr
    intro φ
    have hm := measurable_local_pairing_add_root_integral (U := ball c r)
      (Section6.pairingProc hC) (Section6.measurable_pairingProc hh) g hg
    exact ((measurable_pi_apply φ).comp hm).add
      ((measurable_integral_test_mul_root_function k hk φ.1.1).comp measurable_fst)
  · exact measurable_local_pairing_add_root_integral
      (Section6.pairingProc hC) (Section6.measurable_pairingProc hh) k hk

/-- A logarithmic singularity outside the buffered observation ball does not
change the null sets of the joint rooted law, including in the presence of
an origin logarithmic singularity. -/
theorem IsWholePlaneGFF.rooted_local_logarithmic_shift_equivalence
    {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure ℂ)
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {c : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (a b : ℝ)
    (haway : ∀ᵐ z ∂ρ, ∀ x ∈ ball c R, z + x ≠ 0) :
    let A := shiftedRootReferenceLaw ρ P (fun p =>
      fun φ : Section6.LocalTest (ball c r) =>
        hC p.2 φ.1.1 + ∫ x, φ.1.1 x *
          (a * Real.log ‖p.1 + x‖ + b * Real.log ‖x‖))
    let B := shiftedRootReferenceLaw ρ P (fun p =>
      fun φ : Section6.LocalTest (ball c r) =>
        hC p.2 φ.1.1 + ∫ x, φ.1.1 x * (b * Real.log ‖x‖))
    A ≪ B ∧ B ≪ A := by
  have hg : Measurable (Function.uncurry (fun z x : ℂ => a * Real.log ‖z + x‖)) := by
    change Measurable (fun p : ℂ × ℂ => a * Real.log ‖p.1 + p.2‖)
    simpa only [zero_mul, add_zero] using measurable_translated_log_insertions a 0
  have hk : Measurable (Function.uncurry (fun _ x : ℂ => b * Real.log ‖x‖)) := by
    change Measurable (fun p : ℂ × ℂ => b * Real.log ‖p.2‖)
    simpa only [zero_mul, zero_add] using measurable_translated_log_insertions 0 b
  have hsmooth : ∀ᵐ z ∂ρ,
      ContDiffOn ℝ ∞ (fun x : ℂ => a * Real.log ‖z + x‖) (ball c R) := by
    filter_upwards [haway] with z hz
    exact contDiffOn_const.mul (contDiffOn_log_norm_add hz)
  have h := hh.rooted_local_smooth_insertion_equivalence ρ hr hrR
    (fun z x => a * Real.log ‖z + x‖) (fun _ x => b * Real.log ‖x‖) hg hk hsmooth
  simpa only [integral_test_mul_translated_log_add, add_assoc] using h

/-- For origin-centered observations, a lower bound on the root modulus
ensures the buffered logarithmic singularity condition. -/
theorem IsWholePlaneGFF.rooted_origin_logarithmic_shift_equivalence
    {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure ℂ)
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (a b : ℝ)
    (hroot : ∀ᵐ z ∂ρ, R ≤ ‖z‖) :
    let A := shiftedRootReferenceLaw ρ P (fun p =>
      fun φ : Section6.LocalTest (ball 0 r) =>
        hC p.2 φ.1.1 + ∫ x, φ.1.1 x *
          (a * Real.log ‖p.1 + x‖ + b * Real.log ‖x‖))
    let B := shiftedRootReferenceLaw ρ P (fun p =>
      fun φ : Section6.LocalTest (ball 0 r) =>
        hC p.2 φ.1.1 + ∫ x, φ.1.1 x * (b * Real.log ‖x‖))
    A ≪ B ∧ B ≪ A := by
  apply hh.rooted_local_logarithmic_shift_equivalence ρ hr hrR a b
  filter_upwards [hroot] with z hz x hx
  have hxnorm : ‖x‖ < R := by simpa [mem_ball, dist_eq_norm] using hx
  intro hzero
  have hxeq : x = -z := by linear_combination hzero
  rw [hxeq, norm_neg] at hxnorm
  exact (not_lt_of_ge hz) hxnorm

#print axioms IsWholePlaneGFF.local_smooth_shift_pairing_equivalence
#print axioms IsWholePlaneGFF.local_logarithmic_shift_pairing_equivalence
#print axioms IsWholePlaneGFF.rooted_local_smooth_shift_equivalence
#print axioms IsWholePlaneGFF.rooted_local_smooth_insertion_equivalence
#print axioms IsWholePlaneGFF.rooted_local_logarithmic_shift_equivalence
#print axioms IsWholePlaneGFF.rooted_origin_logarithmic_shift_equivalence

end HarmonicBalls
