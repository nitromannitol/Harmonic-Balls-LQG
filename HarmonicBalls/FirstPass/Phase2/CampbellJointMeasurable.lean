import HarmonicBalls.FirstPass.S11i.Step8TransferMarked

/-!
# Joint measurability for the Campbell identity of the whole-plane LQG measure

The proof of the rooted-measure description of the LQG measure (Duplantier-Miller-Sheffield, Lemma A.10) integrates
the weighted field `ε^{γ²/2} e^{γ h_ε(z)}` over `(ω, z)` and exchanges the two integrals (Tonelli). This file supplies
the joint measurability used there.

* `IsWholePlaneGFF.exists_measurable_circle_version`: for `ε > 0`, the circle average process `z ↦ h_ε(z)` has a
  version that is jointly measurable in `(ω, z)`, continuous in `z` for every `ω`, and equal to `z ↦ h_ε(z)` for
  almost every `ω` (Carathéodory's lemma, from the a.s. continuity of the circle average process).
* `IsWholePlaneGFF.aemeasurable_circle_uncurry`: `(ω, z) ↦ h_ε(z)` is a.e.-measurable for `P ⊗ ν`.
* `IsWholePlaneGFF.measurable_marked`: a marked test function `Ψ(h, z)`, measurable for the pairing σ-algebra of the
  field times the Borel σ-algebra of `ℂ`, gives a measurable function `(ω, z) ↦ Ψ(h(ω), z)`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace HarmonicBalls

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- For `ε > 0` the circle average process `z ↦ h_ε(z)` of a whole-plane GFF has a version `H` that is jointly
measurable in `(ω, z)`, measurable in `ω` for every `z`, continuous in `z` for every `ω`, and equal to `z ↦ h_ε(z)`
for `P`-a.e. `ω`. It is `h_ε(z)` off a measurable null set containing the discontinuity event, and `0` on it. -/
theorem IsWholePlaneGFF.exists_measurable_circle_version (hh : IsWholePlaneGFF P hC hcirc) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ H : Ω → ℂ → ℝ, Measurable (Function.uncurry H) ∧ (∀ z, Measurable fun ω => H ω z) ∧
      (∀ ω, Continuous (H ω)) ∧ ∀ᵐ ω ∂P, H ω = hcirc ω ε := by
  have hae := hh.ae_continuousOn_circle
  rw [ae_iff] at hae
  obtain ⟨N, hBN, hNm, hN0⟩ := exists_measurable_superset_of_null hae
  have hmeas : ∀ z, Measurable fun ω => Nᶜ.indicator (fun ω => hcirc ω ε z) ω := fun z =>
    (hh.measurable_circle ε z hε).indicator hNm.compl
  have hcont : ∀ ω, Continuous fun z => Nᶜ.indicator (fun ω => hcirc ω ε z) ω := by
    intro ω
    by_cases hω : ω ∈ N
    · simp only [indicator_of_notMem (show ω ∉ Nᶜ from fun h => h hω)]
      exact continuous_const
    · simp only [indicator_of_mem (show ω ∈ Nᶜ from hω)]
      have hc : ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ) := by
        by_contra hc
        exact hω (hBN hc)
      exact hc.comp_continuous (continuous_const.prodMk continuous_id) fun z => ⟨hε, mem_univ z⟩
  refine ⟨fun ω z => Nᶜ.indicator (fun ω => hcirc ω ε z) ω,
    (measurable_uncurry_of_continuous_of_measurable
      (u := fun z ω => Nᶜ.indicator (fun ω => hcirc ω ε z) ω) hcont hmeas).comp measurable_swap,
    hmeas, hcont, ?_⟩
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
  funext z
  exact indicator_of_mem (show ω ∈ Nᶜ from hω) _

/-- For `ε > 0`, the circle average `(ω, z) ↦ h_ε(z)` of a whole-plane GFF is a.e.-measurable for `P ⊗ ν`, for every
s-finite measure `ν` on `ℂ`. -/
theorem IsWholePlaneGFF.aemeasurable_circle_uncurry (hh : IsWholePlaneGFF P hC hcirc) {ε : ℝ} (hε : 0 < ε)
    (ν : Measure ℂ) [SFinite ν] :
    AEMeasurable (fun p : Ω × ℂ => hcirc p.1 ε p.2) (P.prod ν) := by
  obtain ⟨H, hHm, -, -, hH⟩ := hh.exists_measurable_circle_version hε
  refine ⟨Function.uncurry H, hHm, ?_⟩
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P) (ν := ν)).ae hH] with p hp
  exact (congrFun hp p.2).symm

/-- A marked test function `Ψ(h, z)`, measurable for the product of the pairing σ-algebra of test functions on `ℂ` and
the Borel σ-algebra of `ℂ`, gives a measurable function `(ω, z) ↦ Ψ(h(ω), z)` of a whole-plane GFF `h`. -/
theorem IsWholePlaneGFF.measurable_marked (hh : IsWholePlaneGFF P hC hcirc)
    {Ψ : (((ℂ → ℝ) → ℝ) × ℂ) → ℝ≥0∞}
    (hΨ : Measurable[(pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) Set.univ).prod inferInstance] Ψ) :
    Measurable fun p : Ω × ℂ => Ψ (hC p.1, p.2) := by
  let _ : MeasurableSpace ((ℂ → ℝ) → ℝ) := pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) Set.univ
  have hCm : Measurable hC := FirstPassS11iStep8Transfer.measurable_hC_pairingUniv hh
  exact hΨ.comp ((hCm.comp measurable_fst).prodMk measurable_snd)

end HarmonicBalls
