import HarmonicBalls.FirstPass.S11ah.LocalMeasurable
import HarmonicBalls.FirstPass.S11ah.FailureSet
import HarmonicBalls.FirstPass.S11al

/-!
# Step 5 for the local decoders, almost surely (fp-S11ah-11-13-steps-4-5b, owner n4; wave 31)

* `certificateEventLocality_of_containments`: the locality hypothesis `CertificateEventLocality` of
  `S11ah/LocalMeasurable.lean` is derived from q1's `FirstPassS11i.certificateEvent_congr_of_eqOn_closedBall`
  (`HarmonicBalls/FirstPass/S11al.lean`, commit 8f2a2a5), given the containments `CertificateContainments`
  (taken as a hypothesis; proved by fp-S11ap).
* `LocalLengthModification P c R D`: the `P`-almost-sure modification of a family of local length metrics on the disc
  `ball c R`. Its existence is the named hypothesis `hq3` (task fp-S11ao, lemma `exists_localLengthModification`), not
  proved here.
* `failureSetLoc`: the Step 5 failure set (formula (K)) of the local certificate sequence `localCertLoc`, indexed by
  `(z, ω) ∈ ℂ × Ω`.
* `measurableSet_failureSetLoc`: measurability for a decoder whose metrics are local length metrics for every `ω`.
* `failureSetLoc_ae_agree`: two families agreeing `P`-a.e. have failure sets that agree `P`-a.e. on every section.
* `exists_modified_failureSet_ae`: the Step 5 interface for the actual decoder, given `hLen` (the a.s. length property of
  the decoder output) and `hq3`: a modified family with measurable failure set, equal to the actual one `P`-a.s.
-/

open MeasureTheory ProbabilityTheory Metric Set Filter Topology
open scoped ENNReal

noncomputable section

namespace FirstPassS11ah

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Locality, derived (operator item (a)).** The containments `CertificateContainments η Ostar V W T Q' Q` (taken
as a hypothesis; fp-S11ap) give `CertificateEventLocality` through q1's congruence lemma. -/
theorem certificateEventLocality_of_containments {η M : ℝ} {Ostar U V W T Q' Q : Set ℂ}
    (hC : FirstPassS11i.CertificateContainments η Ostar V W T Q' Q) :
    CertificateEventLocality Ostar U V W T Q' Q η M := by
  intro μ r hr z D D' h
  exact FirstPassS11i.certificateEvent_congr_of_eqOn_closedBall (μ := μ) hC hr
    (fun p hp => h p.1 hp.1 p.2 hp.2)

/-- **The a.s. modification of a family of local length metrics on `ball c R`** (the statement of fp-S11ao; its
existence is the named hypothesis `hq3`). -/
def LocalLengthModification (P : Measure Ω) (c : ℂ) (R : ℝ) (D : Ω → ℂ → ℂ → ℝ) : Prop :=
  ∃ D' : Ω → ℂ → ℂ → ℝ, (∀ x ∈ ball c R, ∀ y ∈ ball c R, Measurable fun ω => D' ω x y) ∧
    (∀ ω, IsLengthMetricOn (ball c R) (D' ω)) ∧ ∀ᵐ ω ∂P, D' ω = D ω

/-- The local certificate sequence (J) at a point `x = (z, ω) ∈ ℂ × Ω` (Step 5 indexing `x.1 = z`, `x.2 = ℓ`). -/
def localCertPt (c : ℂ) (R : ℝ) (κ : Kernel Ω ℂ) (D : Ω → ℂ → ℂ → ℝ)
    (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ) (n : ℕ) (x : ℂ × Ω) : ℝ :=
  localCertLoc c R κ D Ostar U V W T Q' Q η M n (x.2, x.1)

/-- The Step 5 failure set of the local decoder `D`: formula (K) for the local certificate sequence, over centres in `A`. -/
def failureSetLoc (c : ℂ) (R : ℝ) (κ : Kernel Ω ℂ) (D : Ω → ℂ → ℂ → ℝ)
    (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ) (A : Set ℂ) (q : ℝ) : Set (ℂ × Ω) :=
  failureSet A (localCertPt c R κ D Ostar U V W T Q' Q η M) q

/-- The local certificate indicator at `(ω, z)` depends on the decoder only through `D ω`. -/
lemma localCertLoc_congr {c : ℂ} {R : ℝ} (κ : Kernel Ω ℂ) {D D' : Ω → ℂ → ℂ → ℝ}
    {Ostar U V W T Q' Q : Set ℂ} {η M : ℝ} (n : ℕ) (p : Ω × ℂ) (h : D' p.1 = D p.1) :
    localCertLoc c R κ D' Ostar U V W T Q' Q η M n p = localCertLoc c R κ D Ostar U V W T Q' Q η M n p := by
  classical
  unfold localCertLoc localCertSet
  simp only [mem_ofPred_eq]
  have hiff : (∃ j : ℕ, closedBall p.2 (7 * certScale n) ⊆ ball c (radialSeq R j) ∧
      FirstPassS11i.CertificateEvent (κ p.1) (liftMetric c (radialSeq R j) R (D' p.1))
        Ostar U V W T Q' Q η M (certScale n) p.2) ↔
      (∃ j : ℕ, closedBall p.2 (7 * certScale n) ⊆ ball c (radialSeq R j) ∧
      FirstPassS11i.CertificateEvent (κ p.1) (liftMetric c (radialSeq R j) R (D p.1))
        Ostar U V W T Q' Q η M (certScale n) p.2) := by
    rw [h]
  exact if_congr Iff.rfl (if_congr hiff rfl rfl) rfl

/-- Membership in a failure set depends only on the values of the certificate sequence at the point. -/
lemma mem_failureSet_congr {O : Type*} {A : Set ℂ} {c c' : ℕ → ℂ × O → ℝ} {q : ℝ} (x : ℂ × O)
    (h : ∀ n, c n x = c' n x) : x ∈ failureSet A c q ↔ x ∈ failureSet A c' q := by
  have hw : ∀ N : ℕ, HarmonicBalls.ReferenceNullS11i.refWindowAverage c N x
      = HarmonicBalls.ReferenceNullS11i.refWindowAverage c' N x := fun N => by
    unfold HarmonicBalls.ReferenceNullS11i.refWindowAverage
    rw [Finset.sum_congr rfl fun n _ => h n]
  simp only [failureSet, mem_ofPred_eq, hw]

/-- **Measurability of the local Step 5 failure set** for a family of local length metrics, measurable in `ω`. -/
theorem measurableSet_failureSetLoc {c : ℂ} {R : ℝ} (hR : 0 < R) (κ : Kernel Ω ℂ) [IsSFiniteKernel κ]
    {D : Ω → ℂ → ℂ → ℝ} (hDm : ∀ x ∈ ball c R, ∀ y ∈ ball c R, Measurable fun ω => D ω x y)
    (hD : ∀ ω, IsLengthMetricOn (ball c R) (D ω))
    {Ostar U V W T Q' Q : Set ℂ} (hOstar : IsOpen Ostar) (h0 : (0 : ℂ) ∈ Ostar)
    (hsph : sphere (0 : ℂ) 5 ⊆ Ostar) (hU : MeasurableSet U) {η M : ℝ} (hη : 0 < η)
    {A : Set ℂ} (hA : MeasurableSet A) (q : ℝ) :
    MeasurableSet (failureSetLoc c R κ D Ostar U V W T Q' Q η M A q) :=
  measurableSet_failureSet hA
    (fun n => (measurable_localCertLoc hR κ hDm hD hOstar h0 hsph hU hη n).comp
      (measurable_snd.prodMk measurable_fst)) q

/-- **Agreement P-a.s. of the failure sets.** If `D' ω = D ω` for `P`-a.e. `ω`, then for `P`-a.e. `ω` the sections
`{z | (z, ω) ∈ failureSetLoc … D}` and `{z | (z, ω) ∈ failureSetLoc … D'}` agree. -/
theorem failureSetLoc_ae_agree {c : ℂ} {R : ℝ} (κ : Kernel Ω ℂ) {P : Measure Ω}
    {D D' : Ω → ℂ → ℂ → ℝ} {Ostar U V W T Q' Q : Set ℂ} {η M : ℝ} (A : Set ℂ) (q : ℝ)
    (hae : ∀ᵐ ω ∂P, D' ω = D ω) :
    ∀ᵐ ω ∂P, ∀ z : ℂ, ((z, ω) ∈ failureSetLoc c R κ D Ostar U V W T Q' Q η M A q ↔
      (z, ω) ∈ failureSetLoc c R κ D' Ostar U V W T Q' Q η M A q) := by
  filter_upwards [hae] with ω hω z
  unfold failureSetLoc
  refine mem_failureSet_congr (z, ω) fun n => ?_
  unfold localCertPt
  exact (localCertLoc_congr κ n (ω, z) hω).symm

/-- **Step 5 interface for the local decoder, almost surely (wave 31).** Let `D ω` be a local length metric on
`ball c R` for `P`-a.e. `ω` (`hLen`), measurable in `ω`, and let `hq3` supply the `P`-a.s. modification (fp-S11ao).
Then there is a modified family `D'`, with the length property for every `ω`, whose Step 5 failure set is measurable
and agrees with that of `D` on every section, for `P`-a.e. `ω`. -/
theorem exists_modified_failureSet_ae {c : ℂ} {R : ℝ} (hR : 0 < R) (κ : Kernel Ω ℂ) [IsSFiniteKernel κ]
    (P : Measure Ω) (D : Ω → ℂ → ℂ → ℝ)
    (hDm : ∀ x ∈ ball c R, ∀ y ∈ ball c R, Measurable fun ω => D ω x y)
    (hLen : ∀ᵐ ω ∂P, IsLengthMetricOn (ball c R) (D ω))
    (hq3 : ∀ (D : Ω → ℂ → ℂ → ℝ), (∀ x ∈ ball c R, ∀ y ∈ ball c R, Measurable fun ω => D ω x y) →
      (∀ᵐ ω ∂P, IsLengthMetricOn (ball c R) (D ω)) → LocalLengthModification P c R D)
    {Ostar U V W T Q' Q : Set ℂ} (hOstar : IsOpen Ostar) (h0 : (0 : ℂ) ∈ Ostar)
    (hsph : sphere (0 : ℂ) 5 ⊆ Ostar) (hU : MeasurableSet U) {η M : ℝ} (hη : 0 < η)
    {A : Set ℂ} (hA : MeasurableSet A) (q : ℝ) :
    ∃ D' : Ω → ℂ → ℂ → ℝ,
      (∀ x ∈ ball c R, ∀ y ∈ ball c R, Measurable fun ω => D' ω x y) ∧
      (∀ ω, IsLengthMetricOn (ball c R) (D' ω)) ∧
      MeasurableSet (failureSetLoc c R κ D' Ostar U V W T Q' Q η M A q) ∧
      ∀ᵐ ω ∂P, ∀ z : ℂ, ((z, ω) ∈ failureSetLoc c R κ D Ostar U V W T Q' Q η M A q ↔
        (z, ω) ∈ failureSetLoc c R κ D' Ostar U V W T Q' Q η M A q) := by
  obtain ⟨D', hm, hl, hae⟩ := hq3 D hDm hLen
  exact ⟨D', hm, hl,
    measurableSet_failureSetLoc hR κ hm hl hOstar h0 hsph hU hη hA q,
    failureSetLoc_ae_agree κ A q hae⟩

end FirstPassS11ah

end
