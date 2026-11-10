import HarmonicBalls.FirstPass.S11at
import HarmonicBalls.FirstPass.S11r.CMTransfer
import HarmonicBalls.FirstPass.S11ai.RootedInstance
import HarmonicBalls.FirstPass.S11s.B1Covariance
import HarmonicBalls.FirstPass.S11s.Inverse
import HarmonicBalls.FirstPass.S11i.MixingCanonical

/-!
# On-`G` termwise interface (Astra step 4, operator task fp-S11i-onG-termwise)

Input: a measurable set `G` of canonical fields, conull for `alphaCanon γ hC` under the whole-plane GFF model, on which
the event identity `hFdefG` holds (`L ∈ G → CertificateEvent (Dμ L) (Dd L) … ↔ ballRestrictPairing 7 L ∈ F`).
`G` is abstract: the properties delivered by `LQGCanonicalDecodersMeasurableExistStmt` (Frozen/S11n.lean:71) are
used only as hypotheses. The only other input is the existing frozen Cameron–Martin transfer
`CameronMartinGFFMutualAbsCont` (Frozen/S11d.lean:74), already used by `ae_canonFieldOf_addFunPairing_mem`.

Proved here:
* `dilOrbit G`: the two-sided dilation orbit of `G`. It is measurable, `dilOp`-invariant
  (`preimage_dilOp_dilOrbit`), contained in `G` (`dilOrbit_subset`), and conull when `G` is (`ae_alphaCanon_mem_dilOrbit`).
  Two-sidedness is what makes the invariance an equality, as `B1_covariance` requires (`dilOp ⁻¹' G0 = G0`).
* `ae_rootedOrbit_mem`: for every root `z` and admissible shift `(b, u)`, almost surely every dilation iterate of the
  root-shifted canonical field lies in `G`. This is the rooted membership that was a named input (`hGroot`).
* `ae_identification_on_G`: the almost-sure event identity of `ae_termwise_of_identification`, using `hFdefG` on `G` only.
* `ae_termwise_on_G`: `ae_termwise_of_identification` with that identity (the all-code wrapper is untouched).
* `covariance_set_on_G`, `ae_shiftedCanon_dilation_on_G`: a B1 covariance set `G0` is replaced by `G0 ∩ dilOrbit G`.
  No inclusion `G0 ⊆ G` is assumed; it is obtained from `dilOrbit_subset`.

Conventions: the field parameter is `γ` throughout, as in `ae_termwise_of_identification` (`canonFieldOf γ`), and the
probability space is `Ω : Type` (universe 0), as in `B1_covariance` and the `.{0}` instances of the frozen statements.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HarmonicBalls.FirstPassS11iOnGTermwise

open HarmonicBalls HarmonicBalls.S11c FirstPassS11ai

/-- The two-sided dilation orbit of a set `G` of canonical fields: `L` lies in it when every `dilOp`-iterate and every
`dilOpInv`-iterate of `L` lies in `G`. -/
def dilOrbit (G : Set S11n.CanonSpace) : Set S11n.CanonSpace :=
  {L | (∀ n : ℕ, dilOp^[n] L ∈ G) ∧ ∀ n : ℕ, dilOpInv^[n] L ∈ G}

theorem mem_dilOrbit_iff {G : Set S11n.CanonSpace} {L : S11n.CanonSpace} :
    L ∈ dilOrbit G ↔ (∀ n : ℕ, dilOp^[n] L ∈ G) ∧ ∀ n : ℕ, dilOpInv^[n] L ∈ G :=
  Iff.rfl

theorem dilOrbit_subset (G : Set S11n.CanonSpace) : dilOrbit G ⊆ G := fun _ hL => by
  simpa using (mem_dilOrbit_iff.1 hL).1 0

theorem measurableSet_dilOrbit {G : Set S11n.CanonSpace} (hG : MeasurableSet G) :
    MeasurableSet (dilOrbit G) := by
  have hset : dilOrbit G = (⋂ n : ℕ, dilOp^[n] ⁻¹' G) ∩ ⋂ n : ℕ, dilOpInv^[n] ⁻¹' G := by
    ext L
    simp only [mem_dilOrbit_iff, mem_inter_iff, mem_iInter, mem_preimage]
  rw [hset]
  exact (MeasurableSet.iInter fun n => (measurable_dilOp.iterate n) hG).inter
    (MeasurableSet.iInter fun n => (measurable_dilOpInv.iterate n) hG)

theorem dilOp_iterate_dilOp (L : S11n.CanonSpace) (n : ℕ) :
    dilOp^[n] (dilOp L) = dilOp^[n + 1] L :=
  (Function.iterate_succ_apply dilOp n L).symm

theorem dilOpInv_iterate_succ_dilOp (L : S11n.CanonSpace) (n : ℕ) :
    dilOpInv^[n + 1] (dilOp L) = dilOpInv^[n] L := by
  rw [Function.iterate_succ_apply, dilOpInv_dilOp]

/-- `dilOrbit G` is invariant under `dilOp` (as a set equality, so that it may be intersected with a `B1` set). -/
theorem preimage_dilOp_dilOrbit (G : Set S11n.CanonSpace) :
    dilOp ⁻¹' dilOrbit G = dilOrbit G := by
  ext L
  simp only [Set.mem_preimage, mem_dilOrbit_iff]
  constructor
  · rintro ⟨hf, hb⟩
    refine ⟨fun n => ?_, fun n => ?_⟩
    · rcases n with _ | k
      · have h1 : dilOpInv^[1] (dilOp L) ∈ G := hb 1
        rw [Function.iterate_one, dilOpInv_dilOp] at h1
        exact h1
      · rw [← dilOp_iterate_dilOp L k]
        exact hf k
    · have h := hb (n + 1)
      rw [dilOpInv_iterate_succ_dilOp] at h
      exact h
  · rintro ⟨hf, hb⟩
    refine ⟨fun n => ?_, fun n => ?_⟩
    · rw [dilOp_iterate_dilOp L n]
      exact hf (n + 1)
    · rcases n with _ | k
      · have h1 : dilOp^[1] L ∈ G := hf 1
        rw [Function.iterate_one] at h1
        simpa using h1
      · rw [dilOpInv_iterate_succ_dilOp]
        exact hb k

/-- Measurability of the canonical field `alphaCanon` (as in the proof of `B1_covariance`). -/
theorem measurable_alphaCanon_of_gff {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc) (α : ℝ) :
    Measurable (alphaCanon α hC) := by
  refine measurable_pi_iff.2 fun i => ?_
  exact (hh.measurable_pairing i.1 i.2.1).sub_const (α * ∫ x, i.1 x * Real.log ‖x‖)

/-- Almost-sure iterate membership transfers along a measure-preserving self-map of the law of `X`. -/
theorem ae_iterate_mem {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → S11n.CanonSpace}
    (hX : Measurable X) {f : S11n.CanonSpace → S11n.CanonSpace} (hf : Measurable f)
    (hfp : MeasurePreserving f (P.map X) (P.map X)) {G : Set S11n.CanonSpace} (hG : MeasurableSet G)
    (hGa : ∀ᵐ ω ∂P, X ω ∈ G) (n : ℕ) : ∀ᵐ ω ∂P, f^[n] (X ω) ∈ G := by
  have h1 : ∀ᵐ y ∂(P.map X), y ∈ G :=
    (MeasureTheory.ae_map_iff hX.aemeasurable (p := fun y => y ∈ G) hG).2 hGa
  have h2 : ∀ᵐ y ∂(P.map X), f^[n] y ∈ G :=
    (hfp.iterate n).quasiMeasurePreserving.ae h1
  exact (MeasureTheory.ae_map_iff hX.aemeasurable (p := fun y => f^[n] y ∈ G) (hf.iterate n hG)).1 h2

/-- **The conull dilation orbit.** If `G` is measurable and `alphaCanon α hC` lies in `G` almost surely, then it lies in
`dilOrbit G` almost surely. The law of `alphaCanon` is `dilOp`-invariant (`measurePreserving_dilOp_law`), and so is the
inverse (`dilOpInv`, from the one-sided invariance by pushing forward along `dilOp` then `dilOpInv`). -/
theorem ae_alphaCanon_mem_dilOrbit {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc) (α : ℝ)
    {G : Set S11n.CanonSpace} (hG : MeasurableSet G) (hGa : ∀ᵐ ω ∂P, alphaCanon α hC ω ∈ G) :
    ∀ᵐ ω ∂P, alphaCanon α hC ω ∈ dilOrbit G := by
  have hX : Measurable (alphaCanon α hC) := measurable_alphaCanon_of_gff hh α
  have hfp : MeasurePreserving dilOp (P.map (alphaCanon α hC)) (P.map (alphaCanon α hC)) :=
    measurePreserving_dilOp_law (α := α) P hh
  have hinvEq : (P.map (alphaCanon α hC)).map dilOpInv = P.map (alphaCanon α hC) := by
    calc (P.map (alphaCanon α hC)).map dilOpInv
        = ((P.map (alphaCanon α hC)).map dilOp).map dilOpInv := by rw [hfp.map_eq]
      _ = (P.map (alphaCanon α hC)).map (dilOpInv ∘ dilOp) :=
          Measure.map_map measurable_dilOpInv measurable_dilOp
      _ = P.map (alphaCanon α hC) := by
          rw [show (dilOpInv ∘ dilOp) = id from funext fun L => dilOpInv_dilOp L, Measure.map_id]
  have hfpInv : MeasurePreserving dilOpInv (P.map (alphaCanon α hC)) (P.map (alphaCanon α hC)) :=
    ⟨measurable_dilOpInv, hinvEq⟩
  have hfw : ∀ n : ℕ, ∀ᵐ ω ∂P, dilOp^[n] (alphaCanon α hC ω) ∈ G :=
    fun n => ae_iterate_mem hX measurable_dilOp hfp hG hGa n
  have hbw : ∀ n : ℕ, ∀ᵐ ω ∂P, dilOpInv^[n] (alphaCanon α hC ω) ∈ G :=
    fun n => ae_iterate_mem hX measurable_dilOpInv hfpInv hG hGa n
  filter_upwards [ae_all_iff.2 hfw, ae_all_iff.2 hbw] with ω h1 h2
  exact mem_dilOrbit_iff.2 ⟨h1, h2⟩

/-- **Orbit membership of the root-shifted canonical field.** For a whole-plane GFF model whose translates are
whole-plane GFFs, the field `canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u)` lies in `dilOrbit G`
almost surely, for each root `z` and smooth compactly supported shift `u` with zero unit-circle average (Cameron–Martin
transfer `ae_canonFieldOf_addFunPairing_mem`). -/
theorem ae_shifted_mem_dilOrbit {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hCM : CameronMartinGFFMutualAbsCont.{0}) (γ : ℝ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    (hTr : ∀ z : ℂ, IsWholePlaneGFF P (S11c.translatedPairing hC hcirc z) (S11c.translatedCircle hcirc z))
    {G : Set S11n.CanonSpace} (hG : MeasurableSet G) (hGa : ∀ᵐ ω ∂P, alphaCanon γ hC ω ∈ G)
    (z : ℂ) (u : ℂ → ℝ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hcomp : HasCompactSupport u)
    (hu0 : Real.circleAverage u 0 1 = 0) :
    ∀ᵐ ω ∂P, canonFieldOf γ (addFunPairing (S11c.translatedPairing hC hcirc z ω) u) ∈ dilOrbit G := by
  have hbase : ∀ᵐ ω ∂P, canonFieldOf γ (S11c.translatedPairing hC hcirc z ω) ∈ dilOrbit G :=
    FirstPassS11at.ae_alphaCanon_translatedPairing_mem hh γ z (measurableSet_dilOrbit hG)
      (ae_alphaCanon_mem_dilOrbit hh γ hG hGa)
  exact ae_canonFieldOf_addFunPairing_mem P hCM γ (hTr z) hu hcomp hu0 (measurableSet_dilOrbit hG) hbase

/-- **Rooted membership in `G` (the former named input `hGroot`).** For every root `z` (in the set `A`, with respect to
any measure `μ` on `ℂ`) and every admissible root shift `(b, u)`, almost surely every dilation iterate of the
root-shifted canonical field lies in `G`. It uses only `G` measurable and conull, and the Cameron–Martin transfer. -/
theorem ae_rootedOrbit_mem {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hCM : CameronMartinGFFMutualAbsCont.{0}) (γ : ℝ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    (hTr : ∀ z : ℂ, IsWholePlaneGFF P (S11c.translatedPairing hC hcirc z) (S11c.translatedCircle hcirc z))
    {G : Set S11n.CanonSpace} (hG : MeasurableSet G) (hGa : ∀ᵐ ω ∂P, alphaCanon γ hC ω ∈ G)
    (μ : Measure ℂ) (A : Set ℂ) (α₀ : ℝ) :
    ∀ᵐ z ∂μ, z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ), AdmissibleRootShift α₀ z b u → ∀ᵐ ω ∂P, ∀ n : ℕ,
      dilOp^[n] (canonFieldOf γ (addFunPairing (S11c.translatedPairing hC hcirc z ω) u)) ∈ G := by
  refine ae_of_all _ fun z _ b u hadm => ?_
  obtain ⟨-, -, -, hu, hcomp, hu0, -⟩ := hadm
  filter_upwards [ae_shifted_mem_dilOrbit hCM γ hh hTr hG hGa z u hu hcomp hu0] with ω hω
  exact fun n => (mem_dilOrbit_iff.1 hω).1 n

/-- **Almost-sure event identity on `G`** (the hypothesis `hG` of `ae_termwise_of_identification`). The event identity
is needed only on `G`, where `hFdefG` holds. The orbit membership above supplies `G` along every dilation iterate. -/
theorem ae_identification_on_G {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hCM : CameronMartinGFFMutualAbsCont.{0})
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    (hTr : ∀ z : ℂ, IsWholePlaneGFF P (S11c.translatedPairing hC hcirc z) (S11c.translatedCircle hcirc z))
    {G : Set S11n.CanonSpace} (hG : MeasurableSet G) (hGa : ∀ᵐ ω ∂P, alphaCanon γ hC ω ∈ G)
    (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ)
    (Dμ : S11n.CanonSpace → Measure ℂ) (Dd : S11n.CanonSpace → ℂ → ℂ → ℝ)
    {F : Set (ModConstTestPairings (ball (0 : ℂ) 7))}
    (hFdefG : ∀ L ∈ G, FirstPassS11i.CertificateEvent (Dμ L) (Dd L) Ostar U V W T Q' Q η M 1 0 ↔
      ballRestrictPairing 7 L ∈ F)
    (A : Set ℂ) (c₁ : ℂ) (r₁ : ℝ) (α₀ : ℝ) :
    ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ),
      AdmissibleRootShift α₀ z b u → ∀ᵐ ω ∂P, ∀ n : ℕ,
        (FirstPassS11i.CertificateEvent
            (Dμ (dilOp^[n] (canonFieldOf γ (addFunPairing (S11c.translatedPairing hC hcirc z ω) u))))
            (Dd (dilOp^[n] (canonFieldOf γ (addFunPairing (S11c.translatedPairing hC hcirc z ω) u))))
            Ostar U V W T Q' Q η M 1 0 ↔
          ballRestrictPairing 7 (dilOp^[n] (canonFieldOf γ (addFunPairing (S11c.translatedPairing hC hcirc z ω) u)))
            ∈ F) := by
  filter_upwards [ae_rootedOrbit_mem hCM γ hh hTr hG hGa (volume.restrict (ball c₁ r₁)) A α₀] with z hz
  intro hzA b u hadm
  filter_upwards [hz hzA b u hadm] with ω hω
  intro n
  exact hFdefG _ (hω n)

/-- **The termwise identity on `G`.** `ae_termwise_of_identification` with its almost-sure event identity supplied by
`ae_identification_on_G` (so `hFdef` is used on `G` only). The all-code wrapper is unchanged. -/
theorem ae_termwise_on_G {γ α₀ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {c₁ c₂ : ℂ} {r₁ r₂ : ℝ}
    (hsub : closedBall c₁ r₁ ⊆ ball c₂ r₂) (A : Set ℂ) (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ)
    (κ : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (m : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → ℂ → ℂ → ℝ)
    (c : ℕ → (ℂ × ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ)) → ℝ)
    (hSeq : ∀ (n : ℕ) (z : ℂ) (ℓ : {φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ),
      c n (z, ℓ) = FirstPassS11ah.localCert (ball c₂ r₂) κ m Ostar U V W T Q' Q η M n ℓ z)
    (Dμ : S11n.CanonSpace → Measure ℂ) (Dd : S11n.CanonSpace → ℂ → ℂ → ℝ)
    {F : Set (ModConstTestPairings (ball (0 : ℂ) 7))}
    (hCov : FirstPassS11at.RootedCertificateEventualCovarianceStmt P γ hC hcirc c₁ c₂ r₁ r₂ A Ostar U V W T Q' Q η M
      (AdmissibleRootShift α₀) rootRadius
      (FirstPassS11at.decodedRootMeasure κ γ α₀ hC) (FirstPassS11at.decodedRootMetric m γ α₀ hC) Dμ Dd)
    (hCM : CameronMartinGFFMutualAbsCont.{0}) (hh : IsWholePlaneGFF P hC hcirc)
    (hTr : ∀ z : ℂ, IsWholePlaneGFF P (S11c.translatedPairing hC hcirc z) (S11c.translatedCircle hcirc z))
    {G : Set S11n.CanonSpace} (hG : MeasurableSet G) (hGa : ∀ᵐ ω ∂P, alphaCanon γ hC ω ∈ G)
    (hFdefG : ∀ L ∈ G, FirstPassS11i.CertificateEvent (Dμ L) (Dd L) Ostar U V W T Q' Q η M 1 0 ↔
      ballRestrictPairing 7 L ∈ F) :
    ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ), 0 < b → 2 * b < ‖z‖ → 2 * b < 1 →
      ContDiff ℝ (⊤ : ℕ∞) u → HasCompactSupport u → Real.circleAverage u 0 1 = 0 →
      (∀ w ∈ ball (0 : ℂ) b, u w = -α₀ * Real.log ‖z + w‖) → ∀ᵐ ω ∂P, ∃ n₀ : ℕ, ∀ n ≥ n₀,
        c n (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z) =
          (ballRestrictPairing 7 ⁻¹' F).indicator (fun _ => (1 : ℝ))
            (dilOp^[n] (canonFieldOf γ (addFunPairing (S11c.translatedPairing hC hcirc z ω) u))) :=
  ae_termwise_of_identification hsub A Ostar U V W T Q' Q η M κ m c hSeq Dμ Dd hCov
    (ae_identification_on_G hCM hh hTr hG hGa Ostar U V W T Q' Q η M Dμ Dd hFdefG A c₁ r₁ α₀)

/-- **B1 covariance set intersected with the orbit.** Given a B1 set `G0` (measurable, conull, `dilOp`-invariant),
`G0 ∩ dilOrbit G` is measurable, conull, `dilOp`-invariant, and contained in `G`. No inclusion `G0 ⊆ G` is assumed. -/
theorem covariance_set_on_G {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc) (α : ℝ)
    {G G0 : Set S11n.CanonSpace} (hG : MeasurableSet G) (hGa : ∀ᵐ ω ∂P, alphaCanon α hC ω ∈ G)
    (hG0 : MeasurableSet G0) (hG0a : ∀ᵐ ω ∂P, alphaCanon α hC ω ∈ G0) (hinv : dilOp ⁻¹' G0 = G0) :
    MeasurableSet (G0 ∩ dilOrbit G) ∧ (∀ᵐ ω ∂P, alphaCanon α hC ω ∈ G0 ∩ dilOrbit G) ∧
      dilOp ⁻¹' (G0 ∩ dilOrbit G) = G0 ∩ dilOrbit G ∧ G0 ∩ dilOrbit G ⊆ G := by
  refine ⟨hG0.inter (measurableSet_dilOrbit hG), ?_, ?_, fun L hL => dilOrbit_subset G hL.2⟩
  · filter_upwards [hG0a, ae_alphaCanon_mem_dilOrbit hh α hG hGa] with ω h1 h2
    exact ⟨h1, h2⟩
  · rw [Set.preimage_inter, hinv, preimage_dilOp_dilOrbit]

/-- **Dilation covariance of the root-shifted canonical field on `G0 ∩ dilOrbit G`.** This is
`FirstPassS11at.ae_shiftedCanon_dilation` (B1 covariance transfer) applied to the intersected set. It takes the output
shape of `B1_covariance` (S11s/B1Covariance.lean:120): `G0`, `dilOp ⁻¹' G0 = G0`, and the one-step identities on `G0`. -/
theorem ae_shiftedCanon_dilation_on_G {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hCM : CameronMartinGFFMutualAbsCont.{0}) (γ : ℝ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    (hTr : ∀ z : ℂ, IsWholePlaneGFF P (S11c.translatedPairing hC hcirc z) (S11c.translatedCircle hcirc z))
    {G : Set S11n.CanonSpace} (hG : MeasurableSet G) (hGa : ∀ᵐ ω ∂P, alphaCanon γ hC ω ∈ G)
    (z : ℂ) (u : ℂ → ℝ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hcomp : HasCompactSupport u)
    (hu0 : Real.circleAverage u 0 1 = 0)
    {Dμ : S11n.CanonSpace → Measure ℂ} {Dd : S11n.CanonSpace → ℂ → ℂ → ℝ}
    {G0 : Set S11n.CanonSpace} (hG0 : MeasurableSet G0) (hG0a : ∀ᵐ ω ∂P, alphaCanon γ hC ω ∈ G0)
    (hinv : dilOp ⁻¹' G0 = G0)
    (hstep : ∀ L ∈ G0, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      Dμ (dilOp L) = ENNReal.ofReal a • (Dμ L).map (fun w : ℂ => w / (((1 / 2 : ℝ)) : ℂ)) ∧
      ∀ x y : ℂ, Dd (dilOp L) x y = b * Dd L (((1 / 2 : ℝ) : ℂ) * x) (((1 / 2 : ℝ) : ℂ) * y))
    (n : ℕ) : ∀ᵐ ω ∂P, ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
      Dμ (dilOp^[n] (FirstPassS11at.shiftedCanon γ hC hcirc z u ω)) =
          ENNReal.ofReal a • (Dμ (FirstPassS11at.shiftedCanon γ hC hcirc z u ω)).map
            (fun w : ℂ => w / (((1 / 2 : ℝ) ^ n : ℝ) : ℂ)) ∧
        ∀ x y : ℂ, Dd (dilOp^[n] (FirstPassS11at.shiftedCanon γ hC hcirc z u ω)) x y =
          c * Dd (FirstPassS11at.shiftedCanon γ hC hcirc z u ω) (((((1 / 2 : ℝ) ^ n : ℝ) : ℂ)) * x)
            ((((1 / 2 : ℝ) ^ n : ℝ) : ℂ) * y) := by
  obtain ⟨h0, h1, h2, -⟩ := covariance_set_on_G hh γ hG hGa hG0 hG0a hinv
  exact FirstPassS11at.ae_shiftedCanon_dilation hCM γ hh hTr z u hu hcomp hu0 h0 h1 h2
    (fun L hL => hstep L hL.1) n

/-- **`B1_covariance` instantiated, then intersected with the orbit of `G`.** The B1 covariance set `G0` (from the
global canonical decoders `K`, `d` of `LQGCanonicalDecodersMeasurableExistStmt`) is not assumed to lie in `G`. The
output set is `G0 ∩ dilOrbit G`, which is measurable, conull, `dilOp`-invariant, contained in `G`, and carries the
one-step identities of `B1_covariance`. `G` is abstract: its regularity `hGs` on `G` is an input, as is its conullity. -/
theorem covariance_on_G_of_B1 {γ ξ α : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    {D : Ω → ℂ → ℂ → ℝ} (hD : IsLQGMetricOfField P γ ξ α hC D)
    (K : ProbabilityTheory.Kernel S11n.CanonSpace ℂ) (d : S11n.CanonSpace → ContinuousMap (ℂ × ℂ) ℝ)
    (hd : Measurable d) (hKf : ∀ L, MeasureTheory.IsFiniteMeasureOnCompacts (K L))
    (hid : S11n.LQGCanonicalIdentificationStmt.{0} γ ξ α (fun L => K L) (fun L x y => d L (x, y)))
    {G : Set S11n.CanonSpace} (hGm : MeasurableSet G) (hGa : ∀ᵐ ω ∂P, alphaCanon α hC ω ∈ G)
    (hGs : ∀ L ∈ G, (K L).support = Set.univ ∧ IsEuclideanLengthMetric (fun x y => d L (x, y))) :
    ∃ G0 : Set S11n.CanonSpace,
      MeasurableSet (G0 ∩ dilOrbit G) ∧ (∀ᵐ ω ∂P, alphaCanon α hC ω ∈ G0 ∩ dilOrbit G) ∧
      dilOp ⁻¹' (G0 ∩ dilOrbit G) = G0 ∩ dilOrbit G ∧ G0 ∩ dilOrbit G ⊆ G ∧
      ∀ L ∈ G0 ∩ dilOrbit G, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
        K (dilOp L) = ENNReal.ofReal a • (K L).map (fun w : ℂ => w / ((1 / 2 : ℝ) : ℂ)) ∧
        ∀ u v : ℂ, d (dilOp L) (u, v) = b * d L (((1 / 2 : ℝ) : ℂ) * u, ((1 / 2 : ℝ) : ℂ) * v) := by
  obtain ⟨G0, hG0, hG0a, hinv, hstep⟩ :=
    B1_covariance hγ0 hγ2 hα P hG hμ hD K d hd hKf hid G hGm hGa hGs
  obtain ⟨h0, h1, h2, h3⟩ := covariance_set_on_G hG α hGm hGa hG0 hG0a hinv
  exact ⟨G0, h0, h1, h2, h3, fun L hL => hstep L hL.1⟩

end HarmonicBalls.FirstPassS11iOnGTermwise
