import HarmonicBalls.FirstPass.S11h.LocalEvents
import HarmonicBalls.FirstPass.S11m.IntRule
import HarmonicBalls.FirstPass.S11m.E1Bounds
import HarmonicBalls.FirstPass.S11j.CertificateE1
import HarmonicBalls.Steps.Sec11.InternalMetricContinuity

/-!
# Countable forms of the local events (fp-S11ae, owner z7)

For a Euclidean length metric `d`, the local events `pinchFirstEventLocal` and `pinchThirdEventLocal`
(`FirstPass/S11h/LocalEvents.lean`) are countable formulas in the internal metrics `d(x, y; O)` (Armitage-Gardiner
internal distance) on fixed countable dense subsets of their endpoint sets. The formulas are written for an arbitrary
family of values `g W x y : ℝ≥0∞` indexed by open domains `W` and pairs of points, so that the same statement applies to
the internal metrics of the metric and to field-level decoders (Duplantier-Sheffield, Berestycki-Powell LQG metric).

Deterministic part: `pinchFirstEventLocal_iff_count`, `pinchThirdEventLocal_iff_count`. Measurable part: countable
suprema and infima of measurable decoders are measurable for `distributionMeasurableSpace`.
-/

namespace HarmonicBalls.S11ae

open MeasureTheory Set Metric Filter
open scoped ENNReal

/-- Every subset of `ℂ` has a countable dense subset. -/
theorem exists_countable_dense_sub (A : Set ℂ) : ∃ A' ⊆ A, A'.Countable ∧ A ⊆ closure A' :=
  TopologicalSpace.IsSeparable.exists_countable_dense_subset (TopologicalSpace.IsSeparable.of_separableSpace A)

/-- Countable form of the local first event at the values `g`: the supremum over the dense `Sp ⊆ ∂B₅` on the corridor
domain `O`, the infimum over the dense `Qp ⊆ closure Q'`, `Fp ⊆ ∂Q` on `univ` (the distance `L`), the internal diameter
over the dense `Cp` on the domain `Td`, and the infimum over the dense `Ep ⊆ ∂B_δ` on `univ` (the distance to `{0}`). -/
def localFirstCount (g : Set ℂ → ℂ → ℂ → ℝ≥0∞) (O Td Sp Qp Fp Cp Ep : Set ℂ) : Prop :=
  (⨆ y ∈ Sp, g O 0 y) < (⨅ a ∈ Qp, ⨅ b ∈ Fp, g univ a b) ∧
    (⨆ x ∈ Cp, ⨆ y ∈ Cp, g Td x y) < ⨅ b ∈ Ep, g univ 0 b

/-- Countable form of the local third event at the values `g`: the internal diameter over the dense `Cp` on the domain
`Td`, and the distance between the spheres `∂B_{2δ}` and `∂B_{3δ}` over the dense `Sp2`, `Sp3`. -/
def localThirdCount (g : Set ℂ → ℂ → ℂ → ℝ≥0∞) (Td Sp2 Sp3 Cp : Set ℂ) : Prop :=
  (⨆ x ∈ Cp, ⨆ y ∈ Cp, g Td x y) < ⨅ a ∈ Sp2, ⨅ b ∈ Sp3, g univ a b

/-- The countable local first event only depends on the values at the indices used. -/
theorem localFirstCount_congr {g h : Set ℂ → ℂ → ℂ → ℝ≥0∞} {O Td Sp Qp Fp Cp Ep : Set ℂ}
    (h1 : ∀ y ∈ Sp, g O 0 y = h O 0 y) (h2 : ∀ a ∈ Qp, ∀ b ∈ Fp, g univ a b = h univ a b)
    (h3 : ∀ x ∈ Cp, ∀ y ∈ Cp, g Td x y = h Td x y) (h4 : ∀ b ∈ Ep, g univ 0 b = h univ 0 b) :
    localFirstCount g O Td Sp Qp Fp Cp Ep ↔ localFirstCount h O Td Sp Qp Fp Cp Ep := by
  have e1 : (⨆ y ∈ Sp, g O 0 y) = ⨆ y ∈ Sp, h O 0 y :=
    iSup_congr fun y => iSup_congr fun hy => h1 y hy
  have e2 : (⨅ a ∈ Qp, ⨅ b ∈ Fp, g univ a b) = ⨅ a ∈ Qp, ⨅ b ∈ Fp, h univ a b :=
    iInf_congr fun a => iInf_congr fun ha => iInf_congr fun b => iInf_congr fun hb => h2 a ha b hb
  have e3 : (⨆ x ∈ Cp, ⨆ y ∈ Cp, g Td x y) = ⨆ x ∈ Cp, ⨆ y ∈ Cp, h Td x y :=
    iSup_congr fun x => iSup_congr fun hx => iSup_congr fun y => iSup_congr fun hy => h3 x hx y hy
  have e4 : (⨅ b ∈ Ep, g univ 0 b) = ⨅ b ∈ Ep, h univ 0 b :=
    iInf_congr fun b => iInf_congr fun hb => h4 b hb
  unfold localFirstCount
  rw [e1, e2, e3, e4]

/-- The countable local third event only depends on the values at the indices used. -/
theorem localThirdCount_congr {g h : Set ℂ → ℂ → ℂ → ℝ≥0∞} {Td Sp2 Sp3 Cp : Set ℂ}
    (h1 : ∀ x ∈ Cp, ∀ y ∈ Cp, g Td x y = h Td x y) (h2 : ∀ a ∈ Sp2, ∀ b ∈ Sp3, g univ a b = h univ a b) :
    localThirdCount g Td Sp2 Sp3 Cp ↔ localThirdCount h Td Sp2 Sp3 Cp := by
  have e1 : (⨆ x ∈ Cp, ⨆ y ∈ Cp, g Td x y) = ⨆ x ∈ Cp, ⨆ y ∈ Cp, h Td x y :=
    iSup_congr fun x => iSup_congr fun hx => iSup_congr fun y => iSup_congr fun hy => h1 x hx y hy
  have e2 : (⨅ a ∈ Sp2, ⨅ b ∈ Sp3, g univ a b) = ⨅ a ∈ Sp2, ⨅ b ∈ Sp3, h univ a b :=
    iInf_congr fun a => iInf_congr fun ha => iInf_congr fun b => iInf_congr fun hb => h2 a ha b hb
  unfold localThirdCount
  rw [e1, e2]

/-- Deterministic form of the local first event: for a Euclidean length metric `d` in the buffered pinch geometry,
`pinchFirstEventLocal` is the countable formula in the internal metrics of `d` on the dense subsets. -/
theorem pinchFirstEventLocal_iff_count {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d)
    (hnn : ∀ x y, 0 ≤ d x y) {U V W T Q' Q : Set ℂ} {δ : ℝ} (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    (hΩ : sphere (0 : ℂ) 5 ⊆ pinchOmegaGeom W Q δ)
    {Sp Qp Fp Cp Ep : Set ℂ} (hSp : Sp ⊆ sphere (0 : ℂ) 5) (hSpc : sphere (0 : ℂ) 5 ⊆ closure Sp)
    (hQp : Qp ⊆ closure Q') (hQpc : closure Q' ⊆ closure Qp)
    (hFp : Fp ⊆ frontier Q) (hFpc : frontier Q ⊆ closure Fp)
    (hCp : Cp ⊆ closure (T \ thickening (3 * δ) W)) (hCpc : closure (T \ thickening (3 * δ) W) ⊆ closure Cp)
    (hEp : Ep ⊆ sphere (0 : ℂ) δ) (hEpc : sphere (0 : ℂ) δ ⊆ closure Ep) :
    pinchFirstEventLocal d W T Q' Q δ ↔
      localFirstCount (fun O x y => internalMetric d O x y) (pinchOmegaGeom W Q δ)
        (thickening δ (closure (T \ thickening (3 * δ) W))) Sp Qp Fp Cp Ep := by
  have hδ : 0 < δ := hgeo.delta_pos
  have hO : IsOpen (pinchOmegaGeom W Q δ) := HarmonicBalls.S11m.E1Bounds.pinchOmegaGeom_isOpen W Q δ
  have hA : (closure Q').Nonempty := hgeo.isConnected_Q'.nonempty.closure
  have hB : (frontier Q).Nonempty := HarmonicBalls.S11m.IntRule.frontier_Q_nonempty hgeo
  have h1 : pinchLocalA d W Q δ = ⨆ y ∈ Sp, internalMetric d (pinchOmegaGeom W Q δ) 0 y := by
    unfold pinchLocalA
    exact iSup_eq_iSup_of_dense_of_continuousOn hO hΩ hSp hSpc (hd.continuousOn_internalMetric hnn hO 0)
  have h2 : ENNReal.ofReal (pinchLocalL d Q' Q) = ⨅ a ∈ Qp, ⨅ b ∈ Fp, internalMetric d univ a b := by
    unfold pinchLocalL
    exact ofReal_setDist_eq_countable hd hA hB hQp hFp hQpc hFpc
  have h3 : internalDiam d δ (closure (T \ thickening (3 * δ) W)) =
      ⨆ x ∈ Cp, ⨆ y ∈ Cp, internalMetric d (thickening δ (closure (T \ thickening (3 * δ) W))) x y :=
    internalDiam_eq_countable hd hnn hδ hCp hCpc
  have h4 : ENNReal.ofReal (setDist d {0} (sphere (0 : ℂ) δ)) = ⨅ b ∈ Ep, internalMetric d univ 0 b := by
    have h := ofReal_setDist_eq_countable hd (singleton_nonempty (0 : ℂ))
      (NormedSpace.sphere_nonempty.mpr hδ.le) (subset_refl ({0} : Set ℂ)) hEp subset_closure hEpc
    simpa only [Set.mem_singleton_iff, iInf_iInf_eq_left] using h
  simp only [pinchFirstEventLocal, localFirstCount]
  rw [h1, h2, h3, h4]

/-- Deterministic form of the local third event for a Euclidean length metric `d`. -/
theorem pinchThirdEventLocal_iff_count {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d)
    (hnn : ∀ x y, 0 ≤ d x y) {δ : ℝ} (hδ : 0 < δ) (V W : Set ℂ)
    {Sp2 Sp3 Cp : Set ℂ} (hS2 : Sp2 ⊆ sphere (0 : ℂ) (2 * δ)) (hS2c : sphere (0 : ℂ) (2 * δ) ⊆ closure Sp2)
    (hS3 : Sp3 ⊆ sphere (0 : ℂ) (3 * δ)) (hS3c : sphere (0 : ℂ) (3 * δ) ⊆ closure Sp3)
    (hCp : Cp ⊆ closure (thickening (3 * δ) W \ V)) (hCpc : closure (thickening (3 * δ) W \ V) ⊆ closure Cp) :
    pinchThirdEventLocal d V W δ ↔
      localThirdCount (fun O x y => internalMetric d O x y)
        (thickening δ (closure (thickening (3 * δ) W \ V))) Sp2 Sp3 Cp := by
  have h1 : internalDiam d δ (closure (thickening (3 * δ) W \ V)) =
      ⨆ x ∈ Cp, ⨆ y ∈ Cp, internalMetric d (thickening δ (closure (thickening (3 * δ) W \ V))) x y :=
    internalDiam_eq_countable hd hnn hδ hCp hCpc
  have h2 : ENNReal.ofReal (setDist d (sphere (0 : ℂ) (2 * δ)) (sphere (0 : ℂ) (3 * δ))) =
      ⨅ a ∈ Sp2, ⨅ b ∈ Sp3, internalMetric d univ a b :=
    ofReal_setDist_eq_countable hd (NormedSpace.sphere_nonempty.mpr (by linarith))
      (NormedSpace.sphere_nonempty.mpr (by linarith)) hS2 hS3 hS2c hS3c
  simp only [pinchThirdEventLocal, localThirdCount]
  rw [h1, h2]

/-- A countable supremum of a measurable family is measurable for `distributionMeasurableSpace`. -/
theorem measurable_sup_count {S : Set ℂ} (hS : S.Countable) {g : ℂ → ((ℂ → ℝ) → ℝ) → ℝ≥0∞}
    (hg : ∀ y, Measurable[distributionMeasurableSpace] (g y)) :
    Measurable[distributionMeasurableSpace] fun F => ⨆ y ∈ S, g y F :=
  @measurable_iSup_mem_of_countable ((ℂ → ℝ) → ℝ) distributionMeasurableSpace S hS g hg

/-- A countable infimum of a measurable family is measurable for `distributionMeasurableSpace`. -/
theorem measurable_inf_count {S : Set ℂ} (hS : S.Countable) {g : ℂ → ((ℂ → ℝ) → ℝ) → ℝ≥0∞}
    (hg : ∀ y, Measurable[distributionMeasurableSpace] (g y)) :
    Measurable[distributionMeasurableSpace] fun F => ⨅ y ∈ S, g y F :=
  @measurable_iInf_mem_of_countable ((ℂ → ℝ) → ℝ) distributionMeasurableSpace S hS g hg

/-- The field-level local first event is measurable for `distributionMeasurableSpace`, for measurable decoders. -/
theorem measurableSet_localFirstCount {Φ : Set ℂ → ℂ → ℂ → ((ℂ → ℝ) → ℝ) → ℝ≥0∞}
    (hΦ : ∀ W : Set ℂ, IsOpen W → ∀ x y : ℂ, Measurable[distributionMeasurableSpace] (Φ W x y))
    {O Td : Set ℂ} (hO : IsOpen O) (hTd : IsOpen Td) {Sp Qp Fp Cp Ep : Set ℂ}
    (hSp : Sp.Countable) (hQp : Qp.Countable) (hFp : Fp.Countable) (hCp : Cp.Countable) (hEp : Ep.Countable) :
    MeasurableSet[distributionMeasurableSpace]
      {F | localFirstCount (fun W x y => Φ W x y F) O Td Sp Qp Fp Cp Ep} := by
  have m1 : Measurable[distributionMeasurableSpace] fun F => ⨆ y ∈ Sp, Φ O 0 y F :=
    measurable_sup_count hSp (fun y => hΦ O hO 0 y)
  have m2 : Measurable[distributionMeasurableSpace] fun F => ⨅ a ∈ Qp, ⨅ b ∈ Fp, Φ univ a b F :=
    measurable_inf_count hQp (fun a => measurable_inf_count hFp (fun b => hΦ univ isOpen_univ a b))
  have m3 : Measurable[distributionMeasurableSpace] fun F => ⨆ x ∈ Cp, ⨆ y ∈ Cp, Φ Td x y F :=
    measurable_sup_count hCp (fun x => measurable_sup_count hCp (fun y => hΦ Td hTd x y))
  have m4 : Measurable[distributionMeasurableSpace] fun F => ⨅ b ∈ Ep, Φ univ 0 b F :=
    measurable_inf_count hEp (fun b => hΦ univ isOpen_univ 0 b)
  unfold localFirstCount
  rw [Set.ofPred_and]
  exact (measurableSet_lt m1 m2).inter (measurableSet_lt m3 m4)

/-- The field-level local third event is measurable for `distributionMeasurableSpace`, for measurable decoders. -/
theorem measurableSet_localThirdCount {Φ : Set ℂ → ℂ → ℂ → ((ℂ → ℝ) → ℝ) → ℝ≥0∞}
    (hΦ : ∀ W : Set ℂ, IsOpen W → ∀ x y : ℂ, Measurable[distributionMeasurableSpace] (Φ W x y))
    {Td : Set ℂ} (hTd : IsOpen Td) {Sp2 Sp3 Cp : Set ℂ}
    (hS2 : Sp2.Countable) (hS3 : Sp3.Countable) (hCp : Cp.Countable) :
    MeasurableSet[distributionMeasurableSpace] {F | localThirdCount (fun W x y => Φ W x y F) Td Sp2 Sp3 Cp} := by
  have m1 : Measurable[distributionMeasurableSpace] fun F => ⨆ x ∈ Cp, ⨆ y ∈ Cp, Φ Td x y F :=
    measurable_sup_count hCp (fun x => measurable_sup_count hCp (fun y => hΦ Td hTd x y))
  have m2 : Measurable[distributionMeasurableSpace] fun F => ⨅ a ∈ Sp2, ⨅ b ∈ Sp3, Φ univ a b F :=
    measurable_inf_count hS2 (fun a => measurable_inf_count hS3 (fun b => hΦ univ isOpen_univ a b))
  unfold localThirdCount
  exact measurableSet_lt m1 m2

end HarmonicBalls.S11ae
