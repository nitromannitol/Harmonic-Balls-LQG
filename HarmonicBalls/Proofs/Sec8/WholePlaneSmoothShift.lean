import HarmonicBalls.Proofs.Sec8.LocalSmoothShiftLaw
import HarmonicBalls.Proofs.Sec8.MeanZeroTestEquivalence
import HarmonicBalls.Proofs.Sec8.RootedReferenceLawDomination
import LatticeProb.Bonanno.LQGMetric.Field.CameronMartin

/-! # Smooth shifts of whole-plane GFF pairing laws

We use Leonardo Bonanno's Gaussian-process Cameron–Martin theorem and his
Green-kernel identity for smooth compactly supported functions.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal ContDiff

namespace HarmonicBalls

/-- The mean-zero pairing law of a whole-plane GFF is equivalent to its
translation by a smooth compactly supported function. -/
theorem IsWholePlaneGFF.smooth_shift_pairing_laws
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (g : LQGMetric.TestC) :
    P.map (fun o (φ : LQGMetric.TestC0) => hC o φ.1 + ∫ x, φ.1 x * g x) ≪
        P.map (Section6.pairingProc hC) ∧
      P.map (Section6.pairingProc hC) ≪
        P.map (fun o (φ : LQGMetric.TestC0) => hC o φ.1 + ∫ x, φ.1 x * g x) := by
  let X : LQGMetric.TestC0 → Ω → ℝ := fun φ o => hC o φ.1
  let index : LQGMetric.TestC0 → GFFObservable.Admissible := fun φ =>
    ⟨.pairing φ.1, Section6.isTestFunction_of_testC φ.1⟩
  have hgauss : IsGaussianProcess X P := hh.isGaussianProcess.comp_right index
  have hmeas : ∀ φ, Measurable (X φ) := fun φ =>
    hh.measurable_pairing φ.1 (Section6.isTestFunction_of_testC φ.1)
  have hcent : ∀ φ, P[X φ] = 0 := fun φ =>
    hh.integral_eq_zero (.pairing φ.1) (Section6.isTestFunction_of_testC φ.1)
  let σ : LQGMetric.TestC0 →₀ ℝ := Finsupp.single (LQGMetric.cmTest0 g) 1
  have hshift (φ : LQGMetric.TestC0) :
      QuantumZipper.CameronMartin.covShift X P σ φ = ∫ x, φ.1 x * g x := by
    simp only [σ, QuantumZipper.CameronMartin.covShift, QuantumZipper.CameronMartin.covK,
      Finsupp.support_single _ one_ne_zero, Finset.sum_singleton,
      Finsupp.single_eq_same, one_mul]
    have hc := hh.covariance_eq (.pairing φ.1) (.pairing (LQGMetric.cmTest0 g).1)
      (Section6.isTestFunction_of_testC φ.1)
      (Section6.isTestFunction_of_testC (LQGMetric.cmTest0 g).1)
    change cov[X φ, X (LQGMetric.cmTest0 g); P] = _ at hc
    exact hc.trans ((Section6.wholePlaneGFFCov_pairing_eq_logCov _ _).trans
      (LQGMetric.logCov_cmTest_right g φ.1))
  have hpath : Measurable (fun o φ => X φ o) := measurable_pi_iff.mpr hmeas
  have hmap := QuantumZipper.CameronMartin.map_tiltMeasure_path hgauss hmeas hcent σ
  have hforward : QuantumZipper.CameronMartin.tiltMeasure X P σ ≪ P :=
    withDensity_absolutelyContinuous _ _
  have hback : P ≪ QuantumZipper.CameronMartin.tiltMeasure X P σ := by
    apply withDensity_absolutelyContinuous'
    · exact (ENNReal.measurable_ofReal.comp
        (QuantumZipper.CameronMartin.measurable_tiltDensity hgauss hmeas σ)).aemeasurable
    · exact ae_of_all _ fun o => (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hf := hforward.map hpath
  have hb := hback.map hpath
  rw [hmap] at hf hb
  change P.map (fun o (φ : LQGMetric.TestC0) => hC o φ.1 + ∫ x, φ.1 x * g x) ≪
      P.map (fun o (φ : LQGMetric.TestC0) => hC o φ.1) ∧
    P.map (fun o (φ : LQGMetric.TestC0) => hC o φ.1) ≪
      P.map (fun o (φ : LQGMetric.TestC0) => hC o φ.1 + ∫ x, φ.1 x * g x)
  simpa only [hshift, X] using And.intro hf hb

/-- The smooth-shift equivalence in the unbundled mean-zero test convention. -/
theorem IsWholePlaneGFF.smooth_shift_raw_pairing_laws
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {g : ℂ → ℝ} (hg : IsTestFunction univ g) :
    P.map (fun o (φ : RawMeanZeroTest) => hC o φ.1 + ∫ x, φ.1 x * g x) ≪
        P.map (fun o (φ : RawMeanZeroTest) => hC o φ.1) ∧
      P.map (fun o (φ : RawMeanZeroTest) => hC o φ.1) ≪
        P.map (fun o (φ : RawMeanZeroTest) => hC o φ.1 + ∫ x, φ.1 x * g x) := by
  let g' : LQGMetric.TestC := ⟨g, hg.1, hg.2.1, subset_univ _⟩
  have hm : Measurable (Section6.pairingProc hC) := Section6.measurable_pairingProc hh
  have hs : Measurable (fun o (φ : LQGMetric.TestC0) =>
      hC o φ.1 + ∫ x, φ.1 x * g x) :=
    measurable_pi_iff.mpr fun φ =>
      (hh.measurable_pairing φ.1 (Section6.isTestFunction_of_testC φ.1)).add_const _
  have h := hh.smooth_shift_pairing_laws g'
  change P.map (fun o (φ : LQGMetric.TestC0) => hC o φ.1 + ∫ x, φ.1 x * g x) ≪
      P.map (Section6.pairingProc hC) ∧
    P.map (Section6.pairingProc hC) ≪
      P.map (fun o (φ : LQGMetric.TestC0) => hC o φ.1 + ∫ x, φ.1 x * g x) at h
  have hf := h.1.map meanZeroFieldEquiv.symm.measurable
  have hb := h.2.map meanZeroFieldEquiv.symm.measurable
  rw [Measure.map_map meanZeroFieldEquiv.symm.measurable hs,
    Measure.map_map meanZeroFieldEquiv.symm.measurable hm] at hf hb
  exact ⟨hf, hb⟩

/-- A smooth perturbation on a larger ball gives an absolutely continuous
local pairing law, also in the presence of any common deterministic insertion. -/
theorem IsWholePlaneGFF.local_smooth_shift_pairing_law
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {c : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) {g : ℂ → ℝ}
    (hg : ContDiffOn ℝ ∞ g (ball c R))
    (k : Section6.LocalTest (ball c r) → ℝ) :
    P.map (fun o (φ : Section6.LocalTest (ball c r)) =>
      hC o φ.1.1 + (∫ x, φ.1.1 x * g x) + k φ) ≪
    P.map (fun o (φ : Section6.LocalTest (ball c r)) => hC o φ.1.1 + k φ) := by
  obtain ⟨f, hf, hlocal⟩ := exists_smooth_cutoff_for_local_pairing_law hr hrR hg
  let f' : LQGMetric.TestC := ⟨f, hf.1, hf.2.1, subset_univ _⟩
  exact hlocal P (Section6.pairingProc hC) (Section6.measurable_pairingProc hh)
    (hh.smooth_shift_pairing_laws f').1 k

/-- Fiberwise smooth shifts give domination of jointly measurable local
field-and-root laws; the insertion may depend measurably on the root. -/
theorem IsWholePlaneGFF.rooted_local_smooth_shift_law
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
    shiftedRootReferenceLaw ρ P (fun p =>
      fun φ : Section6.LocalTest (ball c r) =>
        hC p.2 φ.1.1 + (∫ x, φ.1.1 x * g p.1 x) + k p.1 φ) ≪
    shiftedRootReferenceLaw ρ P (fun p =>
      fun φ : Section6.LocalTest (ball c r) => hC p.2 φ.1.1 + k p.1 φ) := by
  have := hh.isProbabilityMeasure
  apply shiftedRootReferenceLaw_absolutelyContinuous_of_fiberwise ρ P P _ _ hshift hbase
  filter_upwards [hg] with z hz
  exact hh.local_smooth_shift_pairing_law hr hrR hz (k z)

#print axioms IsWholePlaneGFF.smooth_shift_pairing_laws
#print axioms IsWholePlaneGFF.smooth_shift_raw_pairing_laws
#print axioms IsWholePlaneGFF.local_smooth_shift_pairing_law
#print axioms IsWholePlaneGFF.rooted_local_smooth_shift_law

end HarmonicBalls
