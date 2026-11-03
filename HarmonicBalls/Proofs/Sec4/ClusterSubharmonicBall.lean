import HarmonicBalls.Proofs.Sec4.LeastSupersolutionHolder
import HarmonicBalls.Steps.Sec4.ClusterSubharmonicBall

/-!
# Lemma 4.3 (lemma:harmonic-ball): steps

`clusterHarmonicQuadratureStep_holds` (`ClusterHarmonicQuadratureStep`, lines 773-779): under eq:v-characterization,
`t q(z) = ∫_Λ q dμ` for every `q` harmonic on an open `O ⊇ closure Λ`. Route: a cut-off `χ = 1` on a neighbourhood of
the compact `closure Λ`, supported in `O ∩ B_R`; `φ = q χ` is a test function (harmonic functions are real-analytic,
`HarmonicAt.analyticAt`), `φ = q` near `closure Λ`, so `u Δφ = 0` everywhere (`Δφ = Δq = 0` near `closure Λ`, `u = 0`
on `B_R \ Λ`, `φ = 0` off `B_R`), and `Δu = -t δ_z + μ|_Λ` tested against `φ` gives the identity.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Laplacian
open scoped ContDiff ENNReal

/-- **Lemma 4.3, Step 1** (`ClusterHarmonicQuadratureStep`). -/
theorem clusterHarmonicQuadratureStep_holds : ClusterHarmonicQuadratureStep := by
  intro μ R Λ z t u hU O q hO hΛO hq
  obtain ⟨-, ht, hΛo, hzΛ, hclR, -, hu0, -, hLap, -⟩ := hU
  have hK : IsCompact (closure Λ) := (isCompact_closedBall 0 R).of_isClosed_subset isClosed_closure
    (hclR.trans ball_subset_closedBall)
  have hV : IsOpen (O ∩ ball (0 : ℂ) R) := hO.inter isOpen_ball
  have hKV : closure Λ ⊆ O ∩ ball (0 : ℂ) R := subset_inter hΛO hclR
  obtain ⟨δ, hδ, hδV⟩ := hK.exists_cthickening_subset_open hV hKV
  obtain ⟨χ, hχd, hχc, hχU, -, hχ1⟩ := exists_cutoff_of_isCompact_subset_isOpen hK.cthickening hV hδV
  set φ : ℂ → ℝ := fun x => q x * χ x with hφ
  have hφd : ContDiff ℝ ∞ φ := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ O
    · exact ((_root_.HarmonicAt.analyticAt (hq x hx)).contDiffAt).mul hχd.contDiffAt
    · have hx' : x ∉ tsupport χ := fun h => hx (hχU h).1
      have hev : φ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with y hy
        simp only [hφ, hy, Pi.zero_apply, mul_zero]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have hφts : tsupport φ ⊆ tsupport χ := tsupport_mul_subset_right
  have hφT : IsTestFunction (ball (0 : ℂ) R) φ :=
    ⟨hφd, hχc.of_isClosed_subset (isClosed_tsupport _) hφts, hφts.trans (hχU.trans inter_subset_right)⟩
  obtain ⟨hiΛ, -, heq⟩ := hLap.2 φ hφT
  have hφq : ∀ x ∈ thickening δ (closure Λ), φ x = q x := fun x hx => by
    simp only [hφ, hχ1 x (thickening_subset_cthickening _ _ hx), mul_one]
  have hΔφ0 : ∀ x ∈ closure Λ, Δ φ x = 0 := by
    intro x hx
    have hev : φ =ᶠ[𝓝 x] q := by
      filter_upwards [isOpen_thickening.mem_nhds (self_subset_thickening hδ _ hx)] with y hy using hφq y hy
    rw [(InnerProductSpace.laplacian_congr_nhds hev).self_of_nhds]
    exact (hq x (hΛO hx)).2.self_of_nhds
  have huΔ : (fun x => u x * Δ φ x) = fun _ => 0 := by
    funext x
    by_cases hxΛ : x ∈ Λ
    · rw [hΔφ0 x (subset_closure hxΛ), mul_zero]
    by_cases hxB : x ∈ ball (0 : ℂ) R
    · rw [hu0 x ⟨hxB, hxΛ⟩, zero_mul]
    · rw [laplacian_eq_zero_of_notMem_tsupport (fun h => hxB (hφT.2.2 h)), mul_zero]
  rw [huΔ, integral_zero, integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal ht.le,
    smul_eq_mul] at heq
  have hφqΛ : EqOn φ q Λ := fun x hx => hφq x (self_subset_thickening hδ _ (subset_closure hx))
  have hφz : φ z = q z := hφqΛ hzΛ
  refine ⟨IntegrableOn.congr_fun (hiΛ : IntegrableOn φ Λ μ) hφqΛ hΛo.measurableSet, ?_⟩
  rw [← setIntegral_congr_fun hΛo.measurableSet hφqΛ, ← hφz]
  linarith

end HarmonicBalls
