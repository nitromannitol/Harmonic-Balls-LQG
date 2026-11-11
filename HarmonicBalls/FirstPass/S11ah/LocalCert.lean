import HarmonicBalls.FirstPass.S11i.CertCanonMeasurable
import HarmonicBalls.FirstPass.S11ah.Cutoff

/-!
# Step 4: the local certificate sequence (J)

For a local observation `ℓ` (with local measure `κ ℓ` and local metric decoder `D ℓ`) and a centre `z`, the `n`-th term is
`c_n(z, ℓ) = 1_{𝓔_{2^{-n}}(κ ℓ, D ℓ; z, M)}` when `closedBall z (7 · 2^{-n}) ⊆ D_loc`, and `0` otherwise (formula (J)).
Here `𝓔_r(μ, D; z, M)` is the certificate event `CertificateEvent μ D Ostar U V W T Q' Q η M r z` of
`FirstPass/S11i/Certificate.lean`, with the fixed buffered domain `Ostar` and the sets `U, V, W, T, Q', Q` of the construction.
The cutoff makes `c_n` depend only on the decoder inside `D_loc`.
-/

open MeasureTheory ProbabilityTheory Metric Set Filter Topology
open scoped ENNReal
open FirstPassS11i

namespace FirstPassS11ah

open Classical in
/-- The local certificate sequence (J) of Step 4: `c_n(ℓ, z) = 1_{𝓔_{2^{-n}}(κ ℓ, D ℓ; z, M)}` when
`closedBall z (7 · 2^{-n}) ⊆ D_loc`, and `0` otherwise. -/
noncomputable def localCert {Ω : Type*} (Dloc : Set ℂ) (κ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ)
    (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ) (n : ℕ) (ℓ : Ω) (z : ℂ) : ℝ :=
  if closedBall z (cutRadius n) ⊆ Dloc then
    (if CertificateEvent (κ ℓ) (D ℓ) Ostar U V W T Q' Q η M (certScale n) z then 1 else 0)
  else 0

section

variable {Ω : Type*} {Dloc : Set ℂ} {κ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    {Ostar U V W T Q' Q : Set ℂ} {η M : ℝ} {n : ℕ} {ℓ : Ω} {z : ℂ}

open Classical in
lemma localCert_of_not_subset (h : ¬ closedBall z (cutRadius n) ⊆ Dloc) :
    localCert Dloc κ D Ostar U V W T Q' Q η M n ℓ z = 0 := by
  simp [localCert, h]

open Classical in
lemma localCert_of_subset (h : closedBall z (cutRadius n) ⊆ Dloc) :
    localCert Dloc κ D Ostar U V W T Q' Q η M n ℓ z =
      if CertificateEvent (κ ℓ) (D ℓ) Ostar U V W T Q' Q η M (certScale n) z then 1 else 0 := by
  simp [localCert, h]

open Classical in
lemma localCert_nonneg : 0 ≤ localCert Dloc κ D Ostar U V W T Q' Q η M n ℓ z := by
  unfold localCert
  split_ifs <;> norm_num

open Classical in
lemma localCert_le_one : localCert Dloc κ D Ostar U V W T Q' Q η M n ℓ z ≤ 1 := by
  unfold localCert
  split_ifs <;> norm_num

end

end FirstPassS11ah
