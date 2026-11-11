import HarmonicBalls.FirstPass.S11i.CertMeasurable

/-!
# Measurability of the certificate event when the length property holds on a measurable set

The canonical decoders `d L` are Euclidean length metrics only on a measurable conull set `G` of canonical fields
(`LQGCanonicalDecodersMeasurableExistStmt`, `FirstPass/Frozen/S11n.lean:61`), whereas `measurableSet_certificateEvent`
(`CertMeasurable.lean`) assumes the length property for every parameter. The modification `modifiedMetric G D` agrees
with `D` on `G` and is the Euclidean metric `dist` off `G`; `dist` is an `IsEuclideanLengthMetric` by
`HarmonicBalls.isEuclideanLengthMetric_dist` (Defs/LQGMetric.lean:253).
-/

namespace FirstPassS11i

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal
open HarmonicBalls

/-- A Euclidean length metric is nonnegative (triangle inequality at `(x, x, y)` and symmetry). -/
lemma lengthMetric_nonneg {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (x y : ℂ) : 0 ≤ D x y := by
  have h := hD.triangle x y x
  rw [hD.self_eq_zero x, hD.symm y x] at h
  linarith

open Classical in
/-- `modifiedMetric G D ω` is `D ω` for `ω ∈ G` and the Euclidean metric `dist` for `ω ∉ G`. -/
noncomputable def modifiedMetric {Ω : Type*} (G : Set Ω) (D : Ω → ℂ → ℂ → ℝ) : Ω → ℂ → ℂ → ℝ :=
  fun ω x y => if ω ∈ G then D ω x y else dist x y

lemma modifiedMetric_of_mem {Ω : Type*} {G : Set Ω} {D : Ω → ℂ → ℂ → ℝ} {ω : Ω} (h : ω ∈ G) :
    modifiedMetric G D ω = D ω := by
  funext x y
  simp [modifiedMetric, h]

lemma modifiedMetric_of_notMem {Ω : Type*} {G : Set Ω} {D : Ω → ℂ → ℂ → ℝ} {ω : Ω} (h : ω ∉ G) :
    modifiedMetric G D ω = fun x y => dist x y := by
  funext x y
  simp [modifiedMetric, h]

/-- The certificate event of the canonical-type family `d ω`, restricted to the measurable set `G` on which `d ω` is
a Euclidean length metric, is measurable in `(ω, z)`. -/
theorem measurableSet_certificateEvent_on {Ω : Type*} [MeasurableSpace Ω]
    (κ : ProbabilityTheory.Kernel Ω ℂ) [ProbabilityTheory.IsSFiniteKernel κ]
    {d : Ω → C(ℂ × ℂ, ℝ)} (hd : Measurable d) {G : Set Ω} (hG : MeasurableSet G)
    (hmet : ∀ ω ∈ G, IsEuclideanLengthMetric (fun x y => d ω (x, y)))
    {Ostar U V W T Q' Q : Set ℂ} (hOstar : IsOpen Ostar) (h0 : (0 : ℂ) ∈ Ostar)
    (hsph : sphere (0 : ℂ) 5 ⊆ Ostar) (hU : MeasurableSet U) {η M : ℝ} (hη : 0 < η) {r : ℝ} (hr : 0 < r) :
    MeasurableSet {p : Ω × ℂ | p.1 ∈ G ∧
      CertificateEvent (κ p.1) (fun x y => d p.1 (x, y)) Ostar U V W T Q' Q η M r p.2} := by
  classical
  have hm1 : Measurable fun q : Ω × (ℂ × ℂ) => d q.1 q.2 := HarmonicBalls.PinchMeasurable.measurable_uncurry_of_continuousMap hd
  have hm2 : Measurable fun q : Ω × (ℂ × ℂ) => dist q.2.1 q.2.2 :=
    continuous_dist.measurable.comp measurable_snd
  have hDm : Measurable fun q : Ω × (ℂ × ℂ) => modifiedMetric G (fun ω x y => d ω (x, y)) q.1 q.2.1 q.2.2 :=
    Measurable.ite (p := fun q : Ω × (ℂ × ℂ) => q.1 ∈ G) (measurable_fst hG) hm1 hm2
  have hDc : ∀ ω, Continuous fun q : ℂ × ℂ => modifiedMetric G (fun ω x y => d ω (x, y)) ω q.1 q.2 := by
    intro ω
    by_cases h : ω ∈ G
    · rw [modifiedMetric_of_mem h]
      exact (d ω).continuous.comp (continuous_fst.prodMk continuous_snd)
    · rw [modifiedMetric_of_notMem h]
      exact continuous_dist
  have hD : ∀ ω, IsEuclideanLengthMetric (modifiedMetric G (fun ω x y => d ω (x, y)) ω) := by
    intro ω
    by_cases h : ω ∈ G
    · rw [modifiedMetric_of_mem h]
      exact hmet ω h
    · rw [modifiedMetric_of_notMem h]
      exact isEuclideanLengthMetric_dist
  have hnn : ∀ ω x y, 0 ≤ modifiedMetric G (fun ω x y => d ω (x, y)) ω x y :=
    fun ω x y => lengthMetric_nonneg (hD ω) x y
  have hm := measurableSet_certificateEvent (Ostar := Ostar) (U := U) (V := V) (W := W) (T := T) (Q' := Q')
    (Q := Q) (η := η) (M := M) (r := r) κ hDm hDc hD hnn hOstar h0 hsph hU hη hr
  have hset : {p : Ω × ℂ | p.1 ∈ G ∧
        CertificateEvent (κ p.1) (fun x y => d p.1 (x, y)) Ostar U V W T Q' Q η M r p.2}
      = {p : Ω × ℂ | p.1 ∈ G} ∩
        {p : Ω × ℂ | CertificateEvent (κ p.1) (modifiedMetric G (fun ω x y => d ω (x, y)) p.1)
          Ostar U V W T Q' Q η M r p.2} := by
    ext ⟨ω, z⟩
    by_cases h : ω ∈ G
    · simp only [mem_ofPred_eq, mem_inter_iff, h, true_and, modifiedMetric_of_mem h]
    · simp [h]
  rw [hset]
  exact (measurable_fst hG).inter hm

end FirstPassS11i

