import HarmonicBalls.FirstPass.S11i.Step8Fitting
import HarmonicBalls.FirstPass.S11ai.RootedCertSpecialized

/-!
# Normalized local kernel and the transfer of `hT` (Stage B2 of fp-S11i-11-13h, owner n3)

* `restrict_window_eq`: a restriction identity on `Dloc` gives the same identity on a measurable window `S ⊆ Dloc`.
* `localCert_normalized_restrict_eq`: if `κ' ℓ` and `κ ℓ` are proportional on `Dloc` (positive factor) and the
  metrics `D' ℓ`, `D ℓ` agree on `closedBall z (7 certScale n)`, the local certificates `localCert Dloc κ' D'` and
  `localCert Dloc κ D` agree at `(n, ℓ, z)`. Containment `closedBall z (cutRadius n) ⊆ Dloc` is handled inside `localCert`.
* `rootedCertTermwise_of_normalized_modified`: `RootedCertificateTermwiseIdentificationStmt` for `(κ, m)` transfers to
  `(κ', m')` under the a.s. positivity `hκpos` (named input) and `m' = m` on the observation set `H`.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace HarmonicBalls.FirstPassS11iStep8Normalized

open HarmonicBalls FirstPassS11ah FirstPassS11ai

universe u

/-- A restriction identity on `Dloc` restricts to the same identity on a measurable window `S ⊆ Dloc`. -/
lemma restrict_window_eq {Dloc S : Set ℂ} (hS : MeasurableSet S) (hSD : S ⊆ Dloc) {μ μ' : Measure ℂ} {s : ℝ}
    (hμ : μ.restrict Dloc = ENNReal.ofReal s • μ'.restrict Dloc) :
    μ.restrict S = (ENNReal.ofReal s • μ').restrict S := by
  have h := congrArg (fun ν : Measure ℂ => ν.restrict S) hμ
  simp only [Measure.restrict_restrict hS, Measure.restrict_smul, Set.inter_eq_left.mpr hSD] at h
  rw [Measure.restrict_smul]
  exact h

/-- **Local normalization is invisible to the certificate.** A positive proportionality of `κ' ℓ` and `κ ℓ` on the
decoding disc `Dloc`, together with agreement of the metrics on `closedBall z (7 certScale n)`, gives equal local
certificates at scale `n`. -/
theorem localCert_normalized_restrict_eq {Ω : Type*} {Dloc : Set ℂ} {z : ℂ} {n : ℕ} {ℓ : Ω}
    {κ κ' : Ω → Measure ℂ} {D D' : Ω → ℂ → ℂ → ℝ} {Ostar U V W T Q' Q : Set ℂ} {η M : ℝ}
    (hC : FirstPassS11i.CertificateContainments η Ostar V W T Q' Q) (hU : U ⊆ closedBall 0 7)
    {s : ℝ} (hs : 0 < s)
    (hκ : (κ' ℓ).restrict Dloc = ENNReal.ofReal s • (κ ℓ).restrict Dloc)
    (hm : ∀ x ∈ closedBall z (7 * certScale n), ∀ y ∈ closedBall z (7 * certScale n), D' ℓ x y = D ℓ x y) :
    localCert Dloc κ' D' Ostar U V W T Q' Q η M n ℓ z = localCert Dloc κ D Ostar U V W T Q' Q η M n ℓ z := by
  unfold localCert
  by_cases hsub : closedBall z (cutRadius n) ⊆ Dloc
  · simp only [hsub, ↓reduceIte]
    have hwin : closedBall z (7 * certScale n) ⊆ Dloc := hsub
    have hcert := FirstPassS11iStep8Fitting.certificateEvent_of_restrict_scalar_at (κ' ℓ) (κ ℓ) (D' ℓ) (D ℓ)
      Ostar U V W T Q' Q η M (certScale n) z (a := s) (b := 1) hs one_pos hC hU (certScale_pos n)
      (restrict_window_eq measurableSet_closedBall hwin hκ) (by
        intro p hp
        show D' ℓ p.1 p.2 = 1 * D ℓ p.1 p.2
        rw [one_mul]
        exact hm p.1 hp.1 p.2 hp.2)
    by_cases hce : FirstPassS11i.CertificateEvent (κ' ℓ) (D' ℓ) Ostar U V W T Q' Q η M (certScale n) z
    · have hce2 := hcert.mp hce
      simp only [hce, hce2, ↓reduceIte]
    · have hce2 : ¬ FirstPassS11i.CertificateEvent (κ ℓ) (D ℓ) Ostar U V W T Q' Q η M (certScale n) z :=
        fun h => hce (hcert.mpr h)
      simp only [hce, hce2, ↓reduceIte]
  · simp only [hsub, ↓reduceIte]

/-- **Termwise identity transfers to the normalized, modified pair.** Given `hT` for `(κ, m)`, a.s. positivity of the
normalizing factor at the rooted reference observations (`hκpos`, named), and `m' = m` on the observation set `H`
carrying the rooted reference observations for a.e. root (`hrefH`), the termwise identity holds for `(κ', m')`.
The containment of the certificate window is handled inside `localCert`, so no eventuality in `n` is needed. -/
theorem rootedCertTermwise_of_normalized_modified {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ) (A : Set ℂ)
    (F : Set (ModConstTestPairings (ball (0 : ℂ) 7)))
    (κ κ' : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (m m' : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → ℂ → ℂ → ℝ)
    (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ)
    (hCC : FirstPassS11i.CertificateContainments η Ostar V W T Q' Q) (hU : U ⊆ closedBall 0 7)
    (hT : RootedCertificateTermwiseIdentificationStmt P γ α₀ hC hcirc c₁ c₂ r₁ r₂ A F κ m Ostar U V W T Q' Q η M)
    (hκpos : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ᵐ ω ∂P, ∃ s : ℝ, 0 < s ∧
      (κ' (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2).restrict (ball c₂ r₂) =
        ENNReal.ofReal s • (κ (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2).restrict (ball c₂ r₂))
    (H : Set ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ))
    (hrefH : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ᵐ ω ∂P,
      (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2 ∈ H)
    (hagree : ∀ l ∈ H, m' l = m l) :
    RootedCertificateTermwiseIdentificationStmt P γ α₀ hC hcirc c₁ c₂ r₁ r₂ A F κ' m' Ostar U V W T Q' Q η M := by
  filter_upwards [hT, hκpos, hrefH] with z hzT hzκ hzH hzA b u hb h2b h2b1 hu hsupp hcu hu'
  filter_upwards [hzT hzA b u hb h2b h2b1 hu hsupp hcu hu', hzκ, hzH] with ω hω hκω hHω
  obtain ⟨n₀, hn₀⟩ := hω
  obtain ⟨s, hs, hκs⟩ := hκω
  refine ⟨n₀, fun n hn => ?_⟩
  refine Eq.trans ?_ (hn₀ n hn)
  exact localCert_normalized_restrict_eq hCC hU hs hκs
    (fun x _ y _ => congrFun (congrFun (hagree _ hHω) x) y)

end HarmonicBalls.FirstPassS11iStep8Normalized

#print axioms HarmonicBalls.FirstPassS11iStep8Normalized.localCert_normalized_restrict_eq
#print axioms HarmonicBalls.FirstPassS11iStep8Normalized.rootedCertTermwise_of_normalized_modified
