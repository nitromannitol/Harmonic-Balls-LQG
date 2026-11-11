import Mathlib
import HarmonicBalls.FirstPass.S11i.Step8FailureIdentification
import HarmonicBalls.FirstPass.S11ai.RootedCertSpecialized

/-!
# Local decoder compatibility of the unit-scale window frequency (Step 8)

Deterministic part of the local-to-physical step of the corrected marked transfer ("local decoder
fitting/compatibility"). For a fixed decoded observation `ℓ` and a fixed physical pair `(μ, d)` at a root `z`:
if the decoded certificate agrees with the physical one at every scale `certScale n` whose cutoff ball
`closedBall z (cutRadius n)` lies in `Dloc` (the `fitting_eq` field of `CertificateIdentification`,
`FirstPass/S11i/Identification.lean:33`), and the cutoff balls eventually lie in `Dloc` (`hev`), then the local window
average of the reference observation `(z, ℓ)` converges to `q` iff the unit-scale window frequency of `(μ, d)` at `z`
does. The window sums agree eventually in `N` (`refWindowAverage` sums `n ∈ [N+1, 2N]`; `unitScaleWindowFreq` counts the
same window with `ncard`). No new input.
-/

universe u

namespace HarmonicBalls.FirstPassS11iStep8LocalCompat

open MeasureTheory Filter Topology Set Metric
open HarmonicBalls.FirstPassS11iStep8Transfer
open FirstPassS11ah FirstPassS11ai

/-- **Local window compatibility (deterministic).** -/
theorem tendsto_localWindow_iff_unitScale {c₂ z : ℂ} {r₂ : ℝ}
    (κ : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (m : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → ℂ → ℂ → ℝ)
    (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ)
    (ℓ : {φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ)
    (μ : Measure ℂ) (d : ℂ → ℂ → ℝ) (q : ℝ)
    (hev : ∀ᶠ n : ℕ in atTop, closedBall z (cutRadius n) ⊆ ball c₂ r₂)
    (hfit : ∀ᶠ n : ℕ in atTop,
      (FirstPassS11i.CertificateEvent (κ ℓ) (m ℓ) Ostar U V W T Q' Q η M (certScale n) z ↔
        FirstPassS11i.CertificateEvent μ d Ostar U V W T Q' Q η M (certScale n) z)) :
    Tendsto (fun N : ℕ => HarmonicBalls.ReferenceNullS11i.refWindowAverage
        (localCertSeq κ m Ostar U V W T Q' Q η M) N (z, ℓ)) atTop (𝓝 q) ↔
      Tendsto (fun N : ℕ => unitScaleWindowFreq μ d Ostar U V W T Q' Q η M z N) atTop (𝓝 q) := by
  classical
  have hwin : ∀ᶠ N : ℕ in atTop, ∀ n ∈ Finset.Icc (N + 1) (2 * N),
      closedBall z (cutRadius n) ⊆ ball c₂ r₂ := by
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hev
    filter_upwards [eventually_ge_atTop n₀] with N hN n hn
    exact hn₀ n (by have := (Finset.mem_Icc.1 hn).1; omega)
  have heq : (fun N : ℕ => HarmonicBalls.ReferenceNullS11i.refWindowAverage
        (localCertSeq κ m Ostar U V W T Q' Q η M) N (z, ℓ)) =ᶠ[atTop]
      (fun N : ℕ => unitScaleWindowFreq μ d Ostar U V W T Q' Q η M z N) := by
    obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 hfit
    filter_upwards [hwin, eventually_ge_atTop (n₁ + 1)] with N hN hN1
    have hterm : ∀ n ∈ Finset.Icc (N + 1) (2 * N),
        localCertSeq κ m Ostar U V W T Q' Q η M n (z, ℓ) =
          if FirstPassS11i.CertificateEvent μ d Ostar U V W T Q' Q η M (certScale n) z then (1 : ℝ) else 0 := by
      intro n hn
      have hsub := hN n hn
      have hiff := hn₁ n (by have := (Finset.mem_Icc.1 hn).1; omega)
      show localCert (ball c₂ r₂) κ m Ostar U V W T Q' Q η M n ℓ z = _
      unfold localCert
      simp only [hsub, ↓reduceIte]
      by_cases h : FirstPassS11i.CertificateEvent μ d Ostar U V W T Q' Q η M (certScale n) z
      · simp [h, hiff.2 h]
      · have h' : ¬ FirstPassS11i.CertificateEvent (κ ℓ) (m ℓ) Ostar U V W T Q' Q η M (certScale n) z :=
          fun h'' => h (hiff.1 h'')
        simp [h, h']
    have hset : {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
          FirstPassS11i.CertificateEvent μ d Ostar U V W T Q' Q η M ((2 : ℝ)⁻¹ ^ n) z} =
        ↑((Finset.Icc (N + 1) (2 * N)).filter (fun n : ℕ =>
          FirstPassS11i.CertificateEvent μ d Ostar U V W T Q' Q η M (certScale n) z)) := by
      ext n
      simp [Finset.coe_filter, Finset.mem_Icc, certScale, and_assoc]
    unfold HarmonicBalls.ReferenceNullS11i.refWindowAverage unitScaleWindowFreq
    congr 1
    rw [Finset.sum_congr rfl hterm, hset, Set.ncard_coe_finset]
    simp [Finset.sum_boole]
  exact tendsto_congr' heq

end HarmonicBalls.FirstPassS11iStep8LocalCompat

