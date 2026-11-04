import HarmonicBalls.Proofs.Sec5.ExhaustionHorizon
import HarmonicBalls.Proofs.Sec5.LocalFamilyThroughContact

/-! # Field-local families along open-domain exhaustions -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

universe u

/-- Along an increasing open exhaustion, the field in each domain determines
its stopped regularized family through first contact. The horizons increase
to the horizon in the union, and every family member compactly contained in
the union is eventually recovered. The locality input is proposed and awaits
source review. -/
theorem exists_fieldLocal_families_of_open_exhaustion
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc)
    (U : ℕ → Set ℂ) (hopen : ∀ n, IsOpen (U n)) (hmono : Monotone U)
    {Λ : Ω → ℂ → ℝ → Set ℂ}
    (hΛ : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (μ ω) (Λ ω z) z) :
    ∃ H : ℕ → Ω → ((⋃ n, U n) → ℝ≥0∞),
    ∃ F : ℕ → Ω → (((⋃ n, U n) × Ioi (0 : ℝ)) → Set ℂ),
    ∃ K : Ω → ((⋃ n, U n) → ℝ≥0∞),
      (∀ n, Measurable[fieldSigmaAlgebra α₀ hC (U n)] (H n)) ∧
      (∀ n, Measurable[fieldSigmaAlgebra α₀ hC (U n)] (F n)) ∧
      Measurable[fieldSigmaAlgebra α₀ hC (⋃ n, U n)] K ∧
      ∀ᵐ ω ∂P, ∀ z : (⋃ n, U n),
        (∀ n, (z : ℂ) ∉ U n → H n ω z = 0) ∧
        (∀ (n : ℕ) (t : ℝ), 0 < t →
          (ENNReal.ofReal t < H n ω z ↔ closure (Λ ω z t) ⊆ U n)) ∧
        (∀ t : ℝ, 0 < t →
          (ENNReal.ofReal t < K ω z ↔ closure (Λ ω z t) ⊆ ⋃ n, U n)) ∧
        Monotone (fun n => H n ω z) ∧ (⨆ n, H n ω z) = K ω z ∧
        Tendsto (fun n => H n ω z) atTop (𝓝 (K ω z)) ∧
        (∀ (n : ℕ) (t : Ioi (0 : ℝ)), (z : ℂ) ∈ U n →
          ENNReal.ofReal t ≤ H n ω z → F n ω (z, t) = Λ ω z t) ∧
        (∀ (n : ℕ) (t s : Ioi (0 : ℝ)), (z : ℂ) ∈ U n →
          H n ω z ≤ ENNReal.ofReal t → H n ω z ≤ ENNReal.ofReal s →
          F n ω (z, t) = F n ω (z, s)) ∧
        (∀ t : Ioi (0 : ℝ), ENNReal.ofReal t < K ω z →
          ∀ᶠ n in atTop, F n ω (z, t) = Λ ω z t) := by
  classical
  obtain ⟨H, K, hH, hK, hHchar⟩ := exists_fieldLocal_horizons_of_open_exhaustion
    hI2 hγ hγ2 hα hGFF hμ hloc U hopen hmono hΛ
  let S := ⋃ n, U n
  let Hlocal (n : ℕ) (ω : Ω) (z : U n) : ℝ≥0∞ :=
    H n ω ⟨z, subset_iUnion U n z.property⟩
  have hlocalchar (n : ℕ) : ∀ᵐ ω ∂P, ∀ z : U n, ∀ t : ℝ, 0 < t →
      (ENNReal.ofReal t < Hlocal n ω z ↔ closure (Λ ω z t) ⊆ U n) := by
    filter_upwards [hHchar] with ω hω
    intro z t ht
    exact (hω ⟨z, subset_iUnion U n z.property⟩).2.1 n t ht
  choose G hG hGchar using fun n : ℕ => exists_fieldLocal_regularizedFamily_through_horizon
    hI2 hγ hγ2 hα hGFF hμ hloc (hopen n) hΛ (Hlocal n) (hlocalchar n)
  let F : ℕ → Ω → (S × Ioi (0 : ℝ) → Set ℂ) := fun n ω p =>
    if hp : (p.1 : ℂ) ∈ U n then G n ω (⟨p.1, hp⟩, p.2) else ∅
  have hF (n : ℕ) : Measurable[fieldSigmaAlgebra α₀ hC (U n)] (F n) := by
    let : MeasurableSpace Ω := fieldSigmaAlgebra α₀ hC (U n)
    apply Measurable.of_eval
    intro p
    by_cases hp : (p.1 : ℂ) ∈ U n
    · simpa only [F, dite_eq_left hp, Function.comp_def] using
        (measurable_pi_apply (⟨(p.1 : ℂ), hp⟩, p.2)).comp (hG n)
    · simpa only [F, dite_eq_right hp] using
        (measurable_const : Measurable (fun _ : Ω => (∅ : Set ℂ)))
  refine ⟨H, F, K, hH, hF, hK, ?_⟩
  filter_upwards [hHchar, ae_all_iff.mpr hGchar] with ω hHω hGω
  intro z
  refine ⟨(hHω z).1, (hHω z).2.1, (hHω z).2.2.1,
    (hHω z).2.2.2.1, (hHω z).2.2.2.2.1, (hHω z).2.2.2.2.2, ?_, ?_, ?_⟩
  · intro n t hz ht
    simpa only [F, dite_eq_left hz, Hlocal] using (hGω n).1 (⟨z, hz⟩, t) ht
  · intro n t s hz ht hs
    simpa only [F, dite_eq_left hz, Hlocal] using (hGω n).2 ⟨z, hz⟩ t s ht hs
  · intro t ht
    have hevent : ∀ᶠ n in atTop, ENNReal.ofReal (t : ℝ) < H n ω z :=
      ((hHω z).2.2.2.2.2).eventually (Ioi_mem_nhds ht)
    filter_upwards [hevent] with n hn
    have hz : (z : ℂ) ∈ U n := by
      by_contra hz
      rw [(hHω z).1 n hz] at hn
      exact (not_lt_zero hn)
    simpa only [F, dite_eq_left hz, Hlocal] using (hGω n).1 (⟨z, hz⟩, t) hn.le

/-- If the exhaustion covers the plane, the local stopped families eventually
recover every positive-time member, simultaneously for all centres and times.
The locality input is proposed and awaits source review. -/
theorem exists_fieldLocal_families_of_plane_exhaustion
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc)
    (U : ℕ → Set ℂ) (hopen : ∀ n, IsOpen (U n)) (hmono : Monotone U)
    (hcover : (⋃ n, U n) = univ)
    {Λ : Ω → ℂ → ℝ → Set ℂ}
    (hΛ : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (μ ω) (Λ ω z) z) :
    ∃ H : ℕ → Ω → ((⋃ n, U n) → ℝ≥0∞),
    ∃ F : ℕ → Ω → (((⋃ n, U n) × Ioi (0 : ℝ)) → Set ℂ),
      (∀ n, Measurable[fieldSigmaAlgebra α₀ hC (U n)] (H n)) ∧
      (∀ n, Measurable[fieldSigmaAlgebra α₀ hC (U n)] (F n)) ∧
      ∀ᵐ ω ∂P, ∀ z : (⋃ n, U n),
        Monotone (fun n => H n ω z) ∧ Tendsto (fun n => H n ω z) atTop (𝓝 ⊤) ∧
        (∀ (n : ℕ) (t : Ioi (0 : ℝ)), (z : ℂ) ∈ U n →
          ENNReal.ofReal t ≤ H n ω z → F n ω (z, t) = Λ ω z t) ∧
        (∀ t : Ioi (0 : ℝ), ∀ᶠ n in atTop, F n ω (z, t) = Λ ω z t) := by
  obtain ⟨H, F, K, hH, hF, _, hchar⟩ := exists_fieldLocal_families_of_open_exhaustion
    hI2 hγ hγ2 hα hGFF hμ hloc U hopen hmono hΛ
  refine ⟨H, F, hH, hF, ?_⟩
  filter_upwards [hchar] with ω hω
  intro z
  have htop : K ω z = ⊤ := exact_containment_horizon_univ (by
    simpa only [hcover] using (hω z).2.2.1)
  refine ⟨(hω z).2.2.2.1, ?_, (hω z).2.2.2.2.2.2.1, ?_⟩
  · simpa only [htop] using (hω z).2.2.2.2.2.1
  · intro t
    apply (hω z).2.2.2.2.2.2.2.2 t
    rw [htop]
    exact ENNReal.ofReal_lt_top

#print axioms exists_fieldLocal_families_of_plane_exhaustion

#print axioms exists_fieldLocal_families_of_open_exhaustion

end HarmonicBalls
