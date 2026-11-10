import HarmonicBalls.FirstPass.S11r.FrozenCanonDecoders
import HarmonicBalls.FirstPass.S11i.CertCanonMeasurable
import HarmonicBalls.FirstPass.S11i.RootedLocalLimit
import HarmonicBalls.FirstPass.S11i.CertificateCanonical
import HarmonicBalls.FirstPass.S11i.Step8TransferDilation
import HarmonicBalls.FirstPass.S11i.Step8PhysExists
import HarmonicBalls.FirstPass.S11ap


/-!
# The global agreement set `G` for the rooted `href` (fp-S11r-G-global-and-href, step 3, n2)

For the canonical decoders `K`, `d` of `CanonDecoderData γ ξ γ` (FrozenCanonDecoders.lean), and a pinch data
`(Ostar, U, V, W, T, Q', Q, η, M)` and a coding set `E` of `Step8Code`, the set

  `G = {L | L ∈ G_reg ∧ (CertificateEvent (K L) (d L) … 1 0 ↔ ballRestrictPairing 7 L ∈ E)}`

is the global version of the agreement set of Lemma 11.12 (Duplantier-Sheffield LQG measure and metric, Armitage-Gardiner
potential theory): its complement is null for the canonical field and on it the certificate identity holds with the
global decoders, so `hFdefG` holds by construction. Scale factors of the identification cancel by
`certificateEvent_ofReal_smul_iff`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace HarmonicBalls.FirstPassS11rGlobalG

open HarmonicBalls FirstPassS11i HarmonicBalls.FirstPassS11rFrozenCanonDecoders
open HarmonicBalls.FirstPassS11iStep8PhysExists HarmonicBalls.FirstPassS11iStep8Transfer HarmonicBalls.S11iCert Metric

variable {γ ξ : ℝ}

/-- The certificate set of the global canonical decoders, restricted to the regular set `G_reg`. -/
def globalCertSet (D : CanonDecoderData γ ξ γ) (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ) : Set S11n.CanonSpace :=
  {L | L ∈ D.G ∧ CertificateEvent (D.K L) (fun x y => D.d L (x, y)) Ostar U V W T Q' Q η M 1 0}

/-- **The global agreement set `G`** (Codex route of fp-S11r-G-global-and-href, step 3): the regular canonical fields on
which the certificate identity with the global decoders agrees with the coding event `E`. -/
def globalG (D : CanonDecoderData γ ξ γ) (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ) (E : Set Step8Code) :
    Set S11n.CanonSpace :=
  {L | L ∈ D.G ∧ (CertificateEvent (D.K L) (fun x y => D.d L (x, y)) Ostar U V W T Q' Q η M 1 0 ↔
    ballRestrictPairing 7 L ∈ E)}

theorem globalG_eq (D : CanonDecoderData γ ξ γ) (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ) (E : Set Step8Code) :
    globalG D Ostar U V W T Q' Q η M E =
      (globalCertSet D Ostar U V W T Q' Q η M ∩ ballRestrictPairing 7 ⁻¹' E) ∪
        ((D.G \ globalCertSet D Ostar U V W T Q' Q η M) ∩ (ballRestrictPairing 7 ⁻¹' E)ᶜ) := by
  ext L
  simp only [globalG, globalCertSet, mem_ofPred_eq, mem_union, mem_inter_iff, Set.mem_sdiff, mem_preimage, mem_compl_iff]
  tauto

/-- Measurability of the global agreement set, from the measurable certificate event on the regular set
(`measurableSet_certificateEvent_on`) and a measurable coding set `E`. -/
theorem measurableSet_globalG (D : CanonDecoderData γ ξ γ) {Ostar U V W T Q' Q : Set ℂ} {η M : ℝ}
    (hOstar : IsOpen Ostar) (h0 : (0 : ℂ) ∈ Ostar) (hsph : sphere (0 : ℂ) 5 ⊆ Ostar)
    (hU : MeasurableSet U) (hη : 0 < η) {E : Set Step8Code} (hE : MeasurableSet E) :
    MeasurableSet (globalG D Ostar U V W T Q' Q η M E) := by
  have := D.isSFinite_K
  have hS := measurableSet_certificateEvent_on (Ostar := Ostar) (U := U) (V := V) (W := W) (T := T) (Q' := Q')
    (Q := Q) (η := η) (M := M) (r := 1) D.K D.measurable_d D.measurableSet_G
    (fun L hL => (D.regular_G L hL).2) hOstar h0 hsph hU hη one_pos
  have hmap : Measurable fun L : S11n.CanonSpace => (L, (0 : ℂ)) :=
    measurable_id.prodMk measurable_const
  have hC : MeasurableSet (globalCertSet D Ostar U V W T Q' Q η M) := hS.preimage hmap
  have hRp : MeasurableSet (ballRestrictPairing 7 ⁻¹' E) := (measurable_ballRestrictPairing 7) hE
  rw [globalG_eq]
  exact (hC.inter hRp).union ((D.measurableSet_G.diff hC).inter hRp.compl)

/-- The certificate identity on the global agreement set is the defining one (`hFdefG` of `href_ballMetric_of_inputs`). -/
theorem hFdefG_globalG (D : CanonDecoderData γ ξ γ) {Ostar U V W T Q' Q : Set ℂ} {η M : ℝ} {E : Set Step8Code} :
    ∀ L ∈ globalG D Ostar U V W T Q' Q η M E,
      CertificateEvent (D.K L) (fun x y => D.d L (x, y)) Ostar U V W T Q' Q η M 1 0 ↔ ballRestrictPairing 7 L ∈ E :=
  fun _ hL => hL.2

/-- **Almost sure membership in `G` from the event identity of one model.** For a whole-plane model with the LQG measure
`μ` and metric `Dm` at insertion `γ`, if the coding event of the canonical field agrees almost surely with the certificate
event of `(μ, Dm)` (the a.s. event equivalence of Lemma 11.12, step 2 of the Codex plan, input `hEv`), then the canonical field
lies in `globalG` almost surely. The identification constants `a, b` of `LQGCanonicalIdentificationStmt` cancel. -/
theorem ae_alphaCanon_mem_globalG (D : CanonDecoderData γ ξ γ) {Ostar U V W T Q' Q : Set ℂ} {η M : ℝ} {E : Set Step8Code}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    (μ : Ω → Measure ℂ) (Dm : Ω → ℂ → ℂ → ℝ)
    (hμ : IsLQGMeasureOfField P γ γ hcirc μ) (hD : IsLQGMetricOfField P γ ξ γ hC Dm)
    (hEv : ∀ᵐ ω ∂P, localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E ↔
      CertificateEvent (μ ω) (Dm ω) Ostar U V W T Q' Q η M 1 0) :
    ∀ᵐ ω ∂P, alphaCanon γ hC ω ∈ globalG D Ostar U V W T Q' Q η M E := by
  have hid := D.ident Ω P hC hcirc μ Dm hh hμ hD
  filter_upwards [hid, D.ae_mem_G Ω P hC hcirc hh, hEv] with ω hω hGω hEω
  obtain ⟨a, b, ha, hb, hμω, hDω⟩ := hω
  have e1 : Dm ω = fun x y => b * D.d (alphaCanon γ hC ω) (x, y) := funext fun x => funext fun y => hDω x y
  have key : CertificateEvent (D.K (alphaCanon γ hC ω)) (fun x y => D.d (alphaCanon γ hC ω) (x, y))
      Ostar U V W T Q' Q η M 1 0 ↔ CertificateEvent (μ ω) (Dm ω) Ostar U V W T Q' Q η M 1 0 := by
    rw [hμω, e1]
    exact (certificateEvent_ofReal_smul_iff ha hb (D.K (alphaCanon γ hC ω)) Ostar U V W T Q' Q η M 1 0).symm
  refine ⟨hGω, ?_⟩
  rw [ballRestrict_alphaCanon_eq γ hC ω]
  exact key.trans hEω.symm

end HarmonicBalls.FirstPassS11rGlobalG

#print axioms HarmonicBalls.FirstPassS11rGlobalG.measurableSet_globalG
#print axioms HarmonicBalls.FirstPassS11rGlobalG.ae_alphaCanon_mem_globalG
#print axioms HarmonicBalls.FirstPassS11rGlobalG.hFdefG_globalG
