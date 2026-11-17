import HarmonicBalls.Proofs.GFF.DMSInsertedMarkedEventTransfer
import HarmonicBalls.Proofs.Sec8.RootedSmoothShiftEquivalence

/-! # Local absolute continuity for inserted marked fields

A fixed nonzero root has a neighborhood where the inserted marked field has
an equivalent local law to the whole-plane field with a root singularity.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ContDiff

namespace HarmonicBalls

private def localTestIndex (U : Set ℂ)
    (φ : {φ : ℂ → ℝ // IsTestFunction U φ ∧ ∫ x, φ x = 0}) : Section6.LocalTest U :=
  ⟨⟨⟨φ.1, φ.2.1.1, φ.2.1.2.1, subset_univ _⟩, φ.2.2⟩, φ.2.1.2.2⟩

private def localPairingReindex (U : Set ℂ) (v : Section6.LocalTest U → ℝ) :
    ModConstTestPairings U := fun φ => v (localTestIndex U φ)

private theorem measurable_localPairingReindex (U : Set ℂ) :
    Measurable (localPairingReindex U) := by
  apply measurable_pi_iff.mpr
  intro φ
  exact measurable_pi_apply (localTestIndex U φ)

/-- The actual marked inserted field and the field with a root logarithmic
singularity have equivalent laws on any buffered disk avoiding the origin and
contained in the unit disk. -/
theorem IsWholePlaneGFF.inserted_marked_local_law_equivalence
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (α γ : ℝ) {z : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hz : R < ‖z‖) (hunit : ‖z‖ + R ≤ 1) :
    let U := ball z r
    let A := P.map (fun o => localModConstField α
      (fun _ : Unit => shiftedPairing γ z (hC o)) U ())
    let B := P.map (fun o (φ : {φ : ℂ → ℝ // IsTestFunction U φ ∧ ∫ x, φ x = 0}) =>
      hC o φ.1 + ∫ w, φ.1 w * (-γ * Real.log ‖w - z‖))
    A ≪ B ∧ B ≪ A := by
  dsimp only
  have haway : ∀ x ∈ ball z R, (0 : ℂ) + x ≠ 0 := by
    intro x hx hzero
    have hx0 : x = 0 := by simpa using hzero
    have hd : dist x z < R := hx
    rw [hx0, dist_zero_left] at hd
    linarith
  have hsm : ContDiffOn ℝ ∞ (fun x : ℂ => -α * Real.log ‖x‖) (ball z R) := by
    simpa only [zero_add] using (contDiffOn_const.mul (contDiffOn_log_norm_add haway) :
      ContDiffOn ℝ ∞ (fun x : ℂ => -α * Real.log ‖(0 : ℂ) + x‖) (ball z R))
  let k : Section6.LocalTest (ball z r) → ℝ := fun φ =>
    ∫ w, φ.1.1 w * (-γ * Real.log ‖w - z‖)
  have h := hh.local_smooth_shift_pairing_equivalence hr hrR hsm k
  have hm := measurable_localPairingReindex (ball z r)
  have ha := h.1.map hm
  have hb := h.2.map hm
  have hbase : Measurable (fun o (φ : Section6.LocalTest (ball z r)) => hC o φ.1.1 + k φ) := by
    apply measurable_pi_iff.mpr
    intro φ
    exact (hh.measurable_pairing φ.1.1 (Section6.isTestFunction_of_testC φ.1.1)).add_const _
  have hshift : Measurable (fun o (φ : Section6.LocalTest (ball z r)) =>
      hC o φ.1.1 + (∫ x, φ.1.1 x * (-α * Real.log ‖x‖)) + k φ) := by
    apply measurable_pi_iff.mpr
    intro φ
    exact ((hh.measurable_pairing φ.1.1 (Section6.isTestFunction_of_testC φ.1.1)).add_const _).add_const _
  rw [Measure.map_map hm hshift, Measure.map_map hm hbase] at ha
  rw [Measure.map_map hm hbase, Measure.map_map hm hshift] at hb
  simp only [Function.comp_def] at ha hb
  have heq (φ : {φ : ℂ → ℝ // IsTestFunction (ball z r) φ ∧ ∫ x, φ x = 0}) :
      (∫ w, dmsShift γ z w * φ.1 w) =
        ∫ w, φ.1 w * (-γ * Real.log ‖w - z‖) := by
    apply integral_congr_ae
    apply ae_of_all
    intro w
    by_cases hw : w ∈ tsupport φ.1
    · have hwball : w ∈ ball z r := φ.2.1.2.2 hw
      have hdist : ‖w - z‖ < r := by simpa [mem_ball, dist_eq_norm] using hwball
      have hn : ‖w‖ ≤ 1 := by
        have ht : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
          simpa only [sub_add_cancel] using norm_add_le (w - z) z
        linarith
      simp [dmsShift, max_eq_right hn, mul_comm]
    · have hw0 : φ.1 w = 0 := image_eq_zero_of_notMem_tsupport hw
      simp [hw0]
  have hA : (fun o => localPairingReindex (ball z r) (fun φ =>
      hC o φ.1.1 + (∫ x, φ.1.1 x * (-α * Real.log ‖x‖)) + k φ)) =
      (fun o => localModConstField α (fun _ : Unit => shiftedPairing γ z (hC o)) (ball z r) ()) := by
    funext o φ
    simp only [localPairingReindex, localTestIndex, localModConstField, fieldPairing, shiftedPairing, heq]
    change hC o φ.1 + (∫ x, φ.1 x * (-α * Real.log ‖x‖)) +
      (∫ w, φ.1 w * (-γ * Real.log ‖w - z‖)) =
      (hC o φ.1 + ∫ w, φ.1 w * (-γ * Real.log ‖w - z‖)) -
        α * ∫ x, φ.1 x * Real.log ‖x‖
    rw [show (∫ x, φ.1 x * (-α * Real.log ‖x‖)) =
        -α * ∫ x, φ.1 x * Real.log ‖x‖ by
          rw [← integral_const_mul]; congr 1; funext x; ring]
    ring
  have hB : (fun o => localPairingReindex (ball z r) (fun φ => hC o φ.1.1 + k φ)) =
      (fun o (φ : {φ : ℂ → ℝ // IsTestFunction (ball z r) φ ∧ ∫ x, φ x = 0}) =>
        hC o φ.1 + ∫ w, φ.1 w * (-γ * Real.log ‖w - z‖)) := by
    rfl
  rw [hA, hB] at ha hb
  exact ⟨ha, hb⟩


/-- The comparison holds at every positive radius whose closed disk avoids the
origin and the unit circle. -/
theorem IsWholePlaneGFF.inserted_marked_local_law_equivalence_of_radius
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (α γ : ℝ) {z : ℂ} {r : ℝ}
    (hr : 0 < r) (hz : r < ‖z‖) (hunit : ‖z‖ + r < 1) :
    let U := ball z r
    let A := P.map (fun o => localModConstField α
      (fun _ : Unit => shiftedPairing γ z (hC o)) U ())
    let B := P.map (fun o (φ : {φ : ℂ → ℝ // IsTestFunction U φ ∧ ∫ x, φ x = 0}) =>
      hC o φ.1 + ∫ w, φ.1 w * (-γ * Real.log ‖w - z‖))
    A ≪ B ∧ B ≪ A := by
  let R := (r + min ‖z‖ (1 - ‖z‖)) / 2
  have hrmin : r < min ‖z‖ (1 - ‖z‖) := lt_min hz (by linarith)
  have hrR : r < R := by dsimp [R]; linarith
  have hRz : R < ‖z‖ := by have := min_le_left ‖z‖ (1 - ‖z‖); dsimp [R]; linarith
  have hRunit : ‖z‖ + R ≤ 1 := by
    have := min_le_right ‖z‖ (1 - ‖z‖)
    dsimp [R]
    linarith
  exact hh.inserted_marked_local_law_equivalence α γ hr hrR hRz hRunit

end HarmonicBalls
