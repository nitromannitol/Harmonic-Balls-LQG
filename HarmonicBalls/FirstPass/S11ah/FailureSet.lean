import HarmonicBalls.FirstPass.S11ah.LocalCert
import HarmonicBalls.FirstPass.S11i.ReferenceNull

/-!
# Step 5: the failure set and joint measurability

In the interface of `S11ai.lean`:
for a marked point `x = (z, ℓ) : ℂ × O` (`x.1 = z` is the centre of (J)) and a root set `A`, the failure set is

  `failureSet A c q = {x | x.1 ∈ A ∧ refWindowAverage c N x ↛ q}`,

where `refWindowAverage` is `HarmonicBalls.ReferenceNullS11i.refWindowAverage` (`FirstPass/S11i/ReferenceNull.lean:25`),
the window average `(∑_{n=N+1}^{2N} c_n x) / N` of formula (K).

* `measurableSet_failureSet`: `failureSet A c q` is measurable for any measurable `c n : ℂ × O → ℝ` (generic in `O`).
* `measurable_localCert_of_decoder`: joint measurability of `(z, ℓ) ↦ c_n(z, ℓ)` for whole-plane decoders
  `d : O → C(ℂ × ℂ, ℝ)` that are Euclidean length metrics on a measurable set `G`; uses `measurableSet_certificateEvent`
  (`FirstPass/S11i/CertMeasurable.lean`) and `modifiedMetric` (`FirstPass/S11i/CertCanonMeasurable.lean`).
  NOT covered: the local decoders `m_D : O → C(D_loc × D_loc, ℝ)` of `LocalMetricReplacementStmt`, which are not
  whole-plane metrics. This is the open gap of Step 5 (see the report).
-/

open MeasureTheory ProbabilityTheory Metric Set Filter Topology
open scoped ENNReal
open HarmonicBalls FirstPassS11i

namespace FirstPassS11ah

/-- The failure set `S` of (K) (Step 5): the marked points `x = (z, ℓ)` with centre `z ∈ A` at which the window averages of
the local certificate sequence `c n` do not converge to `q`. -/
def failureSet {O : Type*} (A : Set ℂ) (c : ℕ → ℂ × O → ℝ) (q : ℝ) : Set (ℂ × O) :=
  {x | x.1 ∈ A ∧ ¬ Tendsto (fun N : ℕ => HarmonicBalls.ReferenceNullS11i.refWindowAverage c N x) atTop (𝓝 q)}

lemma mem_failureSet_iff {O : Type*} {A : Set ℂ} {c : ℕ → ℂ × O → ℝ} {q : ℝ} (x : ℂ × O) :
    x ∈ failureSet A c q ↔
      x.1 ∈ A ∧ ¬ Tendsto (fun N : ℕ => HarmonicBalls.ReferenceNullS11i.refWindowAverage c N x) atTop (𝓝 q) :=
  Iff.rfl

/-- **The failure set is measurable (Step 5).** For measurable `c n` on `ℂ × O` and a measurable root set `A`. -/
theorem measurableSet_failureSet {O : Type*} [MeasurableSpace O] {A : Set ℂ} (hA : MeasurableSet A)
    {c : ℕ → ℂ × O → ℝ} (hc : ∀ n, Measurable (c n)) (q : ℝ) :
    MeasurableSet (failureSet A c q) := by
  unfold failureSet
  exact (measurable_fst hA).inter
    (HarmonicBalls.ReferenceNullS11i.measurableSet_refBadWindowSet c hc q)

/-- **Joint measurability of the local certificate sequence (J), for whole-plane decoders (Step 5).**
Let `d : Ω → C(ℂ × ℂ, ℝ)` be measurable, with `d ω` a Euclidean length metric for `ω ∈ G` (`G` measurable), and let
`κ` be an s-finite kernel. Then `(z, ℓ) ↦ c_n(z, ℓ)` is measurable on `ℂ × Ω`, where `c_n` is `localCert` with the
decoder `modifiedMetric G d` (equal to `d` on `G`, the Euclidean metric off `G`). -/
theorem measurable_localCert_of_decoder {Ω : Type*} [MeasurableSpace Ω]
    (Dloc : Set ℂ) (hDloc : IsOpen Dloc) (κ : Kernel Ω ℂ) [IsSFiniteKernel κ]
    {d : Ω → C(ℂ × ℂ, ℝ)} (hd : Measurable d) {G : Set Ω} (hG : MeasurableSet G)
    (hmet : ∀ ω ∈ G, IsEuclideanLengthMetric (fun x y => d ω (x, y)))
    {Ostar U V W T Q' Q : Set ℂ} (hOstar : IsOpen Ostar) (h0 : (0 : ℂ) ∈ Ostar)
    (hsph : sphere (0 : ℂ) 5 ⊆ Ostar) (hU : MeasurableSet U) {η M : ℝ} (hη : 0 < η) (n : ℕ) :
    Measurable fun q : ℂ × Ω =>
      localCert Dloc (fun ω => κ ω) (modifiedMetric G (fun ω x y => d ω (x, y)))
        Ostar U V W T Q' Q η M n q.2 q.1 := by
  classical
  have hm1 : Measurable fun q : Ω × (ℂ × ℂ) => d q.1 q.2 :=
    HarmonicBalls.PinchMeasurable.measurable_uncurry_of_continuousMap hd
  have hm2 : Measurable fun q : Ω × (ℂ × ℂ) => dist q.2.1 q.2.2 :=
    continuous_dist.measurable.comp measurable_snd
  have hDm : Measurable fun q : Ω × (ℂ × ℂ) =>
      modifiedMetric G (fun ω x y => d ω (x, y)) q.1 q.2.1 q.2.2 :=
    Measurable.ite (p := fun q : Ω × (ℂ × ℂ) => q.1 ∈ G) (measurable_fst hG) hm1 hm2
  have hDc : ∀ ω, Continuous fun q : ℂ × ℂ => modifiedMetric G (fun ω x y => d ω (x, y)) ω q.1 q.2 := by
    intro ω
    by_cases h : ω ∈ G
    · have hEq : modifiedMetric G (fun ω x y => d ω (x, y)) ω = fun x y => d ω (x, y) :=
        modifiedMetric_of_mem h
      rw [hEq]
      exact (d ω).continuous.comp (continuous_fst.prodMk continuous_snd)
    · have hEq : modifiedMetric G (fun ω x y => d ω (x, y)) ω = fun x y => dist x y :=
        modifiedMetric_of_notMem h
      rw [hEq]
      exact continuous_dist
  have hD : ∀ ω, IsEuclideanLengthMetric (modifiedMetric G (fun ω x y => d ω (x, y)) ω) := by
    intro ω
    by_cases h : ω ∈ G
    · have hEq : modifiedMetric G (fun ω x y => d ω (x, y)) ω = fun x y => d ω (x, y) :=
        modifiedMetric_of_mem h
      rw [hEq]
      exact hmet ω h
    · have hEq : modifiedMetric G (fun ω x y => d ω (x, y)) ω = fun x y => dist x y :=
        modifiedMetric_of_notMem h
      rw [hEq]
      exact isEuclideanLengthMetric_dist
  have hnn : ∀ ω x y, 0 ≤ modifiedMetric G (fun ω x y => d ω (x, y)) ω x y := by
    intro ω x y
    have hL := hD ω
    have htri := hL.triangle x y x
    rw [hL.self_eq_zero, hL.symm y x] at htri
    linarith
  have hE := measurableSet_certificateEvent (V := V) (W := W) (T := T) (Q' := Q') (Q := Q) (M := M)
    κ hDm hDc hD hnn hOstar h0 hsph hU hη (certScale_pos n)
  have hEsw : MeasurableSet {q : ℂ × Ω |
      CertificateEvent (κ q.2) (modifiedMetric G (fun ω x y => d ω (x, y)) q.2) Ostar U V W T Q' Q η M
        (certScale n) q.1} := measurable_swap hE
  have hcut : MeasurableSet {q : ℂ × Ω | closedBall q.1 (cutRadius n) ⊆ Dloc} :=
    measurable_fst (measurableSet_setOf_closedBall_subset hDloc _)
  unfold localCert
  exact Measurable.ite (p := fun q : ℂ × Ω => closedBall q.1 (cutRadius n) ⊆ Dloc) hcut
    (Measurable.ite (p := fun q : ℂ × Ω =>
      CertificateEvent (κ q.2) (modifiedMetric G (fun ω x y => d ω (x, y)) q.2) Ostar U V W T Q' Q η M
        (certScale n) q.1) hEsw measurable_const measurable_const)
    measurable_const

/-- **The failure set of Step 5 for whole-plane decoders** is measurable. -/
theorem measurableSet_failureSet_of_decoder {Ω : Type*} [MeasurableSpace Ω]
    (Dloc : Set ℂ) (hDloc : IsOpen Dloc) (κ : Kernel Ω ℂ) [IsSFiniteKernel κ]
    {d : Ω → C(ℂ × ℂ, ℝ)} (hd : Measurable d) {G : Set Ω} (hG : MeasurableSet G)
    (hmet : ∀ ω ∈ G, IsEuclideanLengthMetric (fun x y => d ω (x, y)))
    {Ostar U V W T Q' Q : Set ℂ} (hOstar : IsOpen Ostar) (h0 : (0 : ℂ) ∈ Ostar)
    (hsph : sphere (0 : ℂ) 5 ⊆ Ostar) (hU : MeasurableSet U) {η M : ℝ} (hη : 0 < η)
    {A : Set ℂ} (hA : MeasurableSet A) (q : ℝ) :
    MeasurableSet (failureSet A
      (fun n (x : ℂ × Ω) => localCert Dloc (fun ω => κ ω)
        (modifiedMetric G (fun ω x y => d ω (x, y))) Ostar U V W T Q' Q η M n x.2 x.1) q) :=
  measurableSet_failureSet hA
    (fun n => measurable_localCert_of_decoder Dloc hDloc κ hd hG hmet hOstar h0 hsph hU hη n) q

end FirstPassS11ah
