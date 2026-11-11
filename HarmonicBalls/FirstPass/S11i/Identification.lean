import HarmonicBalls.FirstPass.S11i.Certificate
import HarmonicBalls.FirstPass.S11i.Faithful
import HarmonicBalls.FirstPass.S11ah.LocalCert

/-!
# Shared decoded-to-physical identification of certificates

`CertificateIdentification` is the shared `Prop`: one structure with three
clauses, used by two instances.

* Step 8, unrooted law (`Step8IdentificationStmt`): `obs ω = obs_{D_j} h^{α₀}_ω` on a local domain `Dloc = D_j`.
* hId, rooted law: `obs ω = obs_D f_{z₀,ω}` (Campbell reference field) for a fixed good root `z₀`.

Fields:
* `sequence_eq`: the decoded sequence `c` is the truncated `localCert` sequence (`FirstPassS11ah.localCert`, `LocalCert.lean:24`).
* `fitting_eq`: almost surely, for every centre `z` and every fitting scale `n` with `closedBall z (cutRadius n) ⊆ Dloc`, the decoded
  certificate event `CertificateEvent` of the observation equals the physical `CertificateEvent` (`Certificate.lean:42`).
  Quantifier order (§3 of the answer): one conull set per local domain, simultaneously for all centres and all fitting scales.
* `scale_one_eq`: almost surely, the coding event `F` at scale one holds exactly when the physical certificate at scale one
  (`CertificateEvent … 1 0`: radius `1`, centre `0`) holds. This is the canonical almost-sure equality of §5.3.

The structure is an interface; its fields are proved by the instances, not assumed for arbitrary parameters.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open FirstPassS11i FirstPassS11ah

/-- The shared identification of decoded and physical certificates. The observation law is
`P` (`obs : Ω → Obs`, decoders `κ`, `m`), the physical objects are `μ, d` on `Ω`, and the scale-one coding event `F` is given
by the canonical law `P₀` with observation `unitObs` and physical objects `μ₀, d₀`. -/
structure CertificateIdentification
    {Ω Ω₀ Obs : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₀]
    (P : Measure Ω) (P₀ : Measure Ω₀)
    (Dloc Ostar U V W T Q' Q : Set ℂ) (η M : ℝ)
    (κ : Obs → Measure ℂ) (m : Obs → ℂ → ℂ → ℝ) (c : ℕ → (ℂ × Obs) → ℝ)
    (obs : Ω → Obs) (μ : Ω → Measure ℂ) (d : Ω → ℂ → ℂ → ℝ)
    (F : Set (ModConstTestPairings (ball (0 : ℂ) 7)))
    (unitObs : Ω₀ → ModConstTestPairings (ball (0 : ℂ) 7))
    (μ₀ : Ω₀ → Measure ℂ) (d₀ : Ω₀ → ℂ → ℂ → ℝ) : Prop where
  /-- The decoded sequence is the truncated local certificate sequence. -/
  sequence_eq :
    ∀ (n : ℕ) (z : ℂ) (ℓ : Obs),
      c n (z, ℓ) = localCert Dloc κ m Ostar U V W T Q' Q η M n ℓ z
  /-- Almost surely, at every centre and every fitting scale inside `Dloc`, the decoded and physical certificates agree. -/
  fitting_eq :
    ∀ᵐ ω ∂P, ∀ (z : ℂ) (n : ℕ),
      closedBall z (cutRadius n) ⊆ Dloc →
        (CertificateEvent (κ (obs ω)) (m (obs ω)) Ostar U V W T Q' Q η M (certScale n) z ↔
         CertificateEvent (μ ω) (d ω) Ostar U V W T Q' Q η M (certScale n) z)
  /-- Almost surely, the scale-one coding event holds exactly when the physical certificate at scale one holds. -/
  scale_one_eq :
    ∀ᵐ ω₀ ∂P₀,
      unitObs ω₀ ∈ F ↔
        CertificateEvent (μ₀ ω₀) (d₀ ω₀) Ostar U V W T Q' Q η M 1 0

end HarmonicBalls
