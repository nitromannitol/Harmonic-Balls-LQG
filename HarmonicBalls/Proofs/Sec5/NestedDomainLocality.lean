import HarmonicBalls.Proofs.Sec5.LocalFamilyThroughContact

/-! # Consistency of first-contact stopping across nested open domains -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

universe u

/-- Exact compact-containment horizons are monotone in the open domain.
No regularity of the underlying family is needed. -/
theorem exact_containment_horizon_mono
    {A : ℝ → Set ℂ} {U V : Set ℂ} (hUV : U ⊆ V) {H K : ℝ≥0∞}
    (hH : ∀ t : ℝ, 0 < t → (ENNReal.ofReal t < H ↔ closure (A t) ⊆ U))
    (hK : ∀ t : ℝ, 0 < t → (ENNReal.ofReal t < K ↔ closure (A t) ⊆ V)) :
    H ≤ K := by
  by_contra hn
  obtain ⟨q, hqK, hqH⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp (lt_of_not_ge hn)
  have hqpos : 0 < (q : ℝ) := by
    have hqpos' : 0 < (q : ℝ≥0∞) := lt_of_le_of_lt bot_le hqK
    exact_mod_cast hqpos'
  have hlt : ENNReal.ofReal (q : ℝ) < H := by simpa using hqH
  have hlt' : ENNReal.ofReal (q : ℝ) < K :=
    (hK q hqpos).mpr (((hH q hqpos).mp hlt).trans hUV)
  have hge : K < ENNReal.ofReal (q : ℝ) := by simpa using hqK
  exact (not_lt_of_ge hlt'.le) hge

/-- Field-local stopped families for nested open domains can be chosen to
agree at every positive time through the smaller horizon, simultaneously for
all centres in the smaller domain. The locality input is proposed and awaits
source review. -/
theorem exists_fieldLocal_nested_open_families_through_contact
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc)
    {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ⊆ V)
    {Λ : Ω → ℂ → ℝ → Set ℂ}
    (hΛ : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (μ ω) (Λ ω z) z) :
    ∃ H : Ω → (U → ℝ≥0∞), ∃ K : Ω → (V → ℝ≥0∞),
      ∃ F : Ω → (U × Ioi (0 : ℝ) → Set ℂ),
      ∃ G : Ω → (V × Ioi (0 : ℝ) → Set ℂ),
      Measurable[fieldSigmaAlgebra α₀ hC U] H ∧
      Measurable[fieldSigmaAlgebra α₀ hC V] K ∧
      Measurable[fieldSigmaAlgebra α₀ hC U] F ∧
      Measurable[fieldSigmaAlgebra α₀ hC V] G ∧
      ∀ᵐ ω ∂P, ∀ z : U,
        H ω z ≤ K ω ⟨z, hUV z.property⟩ ∧
        (∀ t : Ioi (0 : ℝ), ENNReal.ofReal t ≤ H ω z →
          F ω (z, t) = Λ ω z t ∧
          G ω (⟨z, hUV z.property⟩, t) = Λ ω z t) ∧
        (∀ t s : Ioi (0 : ℝ), H ω z ≤ ENNReal.ofReal t →
          H ω z ≤ ENNReal.ofReal s → F ω (z, t) = F ω (z, s)) ∧
        (∀ t : ℝ, 0 < t →
          (ENNReal.ofReal t < H ω z ↔ closure (Λ ω z t) ⊆ U)) ∧
        (∀ t : ℝ, 0 < t →
          (ENNReal.ofReal t < K ω ⟨z, hUV z.property⟩ ↔ closure (Λ ω z t) ⊆ V)) := by
  obtain ⟨H, F, hH, hF, hHU⟩ := exists_fieldLocal_open_family_through_contact
    hI2 hγ hγ2 hα hGFF hμ hloc hU hΛ
  obtain ⟨K, G, hK, hG, hKV⟩ := exists_fieldLocal_open_family_through_contact
    hI2 hγ hγ2 hα hGFF hμ hloc hV hΛ
  refine ⟨H, K, F, G, hH, hK, hF, hG, ?_⟩
  filter_upwards [hHU, hKV] with ω hHUω hKVω
  intro z
  let z' : V := ⟨z, hUV z.property⟩
  have hle : H ω z ≤ K ω z' := exact_containment_horizon_mono hUV
    (hHUω z).1 (hKVω z').1
  refine ⟨hle, ?_, (hHUω z).2.2.1, (hHUω z).1, (hKVω z').1⟩
  intro t ht
  exact ⟨(hHUω z).2.1 t ht, (hKVω z').2.1 t (ht.trans hle)⟩

/-- If the smaller domain is bounded, its stopped family agrees after contact
with the larger-domain family evaluated at the smaller contact time. The
locality, affine invariance and coordinate change inputs are proposed and
await source review. -/
theorem exists_fieldLocal_nested_bounded_open_families
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc)
    {U V : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hV : IsOpen V) (hUV : U ⊆ V)
    {Λ : Ω → ℂ → ℝ → Set ℂ}
    (hΛ : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (μ ω) (Λ ω z) z) :
    ∃ H : Ω → (U → ℝ≥0∞), ∃ K : Ω → (V → ℝ≥0∞),
      ∃ F : Ω → (U × Ioi (0 : ℝ) → Set ℂ),
      ∃ G : Ω → (V × Ioi (0 : ℝ) → Set ℂ),
      Measurable[fieldSigmaAlgebra α₀ hC U] H ∧
      Measurable[fieldSigmaAlgebra α₀ hC V] K ∧
      Measurable[fieldSigmaAlgebra α₀ hC U] F ∧
      Measurable[fieldSigmaAlgebra α₀ hC V] G ∧
      ∀ᵐ ω ∂P, ∀ z : U,
        0 < H ω z ∧ H ω z ≤ μ ω U ∧ H ω z < ⊤ ∧
        H ω z ≤ K ω ⟨z, hUV z.property⟩ ∧
        (∀ t : ℝ, 0 < t →
          (ENNReal.ofReal t < H ω z ↔ closure (Λ ω z t) ⊆ U)) ∧
        (∀ t : ℝ, 0 < t →
          (ENNReal.ofReal t < K ω ⟨z, hUV z.property⟩ ↔ closure (Λ ω z t) ⊆ V)) ∧
        (∀ t : Ioi (0 : ℝ), ENNReal.ofReal t ≤ K ω ⟨z, hUV z.property⟩ →
          G ω (⟨z, hUV z.property⟩, t) = Λ ω z t) ∧
        (∀ t : Ioi (0 : ℝ), ENNReal.ofReal t ≤ H ω z →
          F ω (z, t) = G ω (⟨z, hUV z.property⟩, t)) ∧
        (∃ τ : Ioi (0 : ℝ), (τ : ℝ) = (H ω z).toReal ∧
          ∀ t : Ioi (0 : ℝ), H ω z ≤ ENNReal.ofReal t →
            F ω (z, t) = G ω (⟨z, hUV z.property⟩, τ)) ∧
        (closure (Λ ω z (H ω z).toReal) ∩ frontier U).Nonempty := by
  obtain ⟨H, F, hH, hF, hHU⟩ := exists_fieldLocal_bounded_open_family_through_contact
    hI2 h71 hAff hCC hγ hγ2 hα hGFF hμ hloc hU hUb hΛ
  obtain ⟨K, G, hK, hG, hKV⟩ := exists_fieldLocal_open_family_through_contact
    hI2 hγ hγ2 hα hGFF hμ hloc hV hΛ
  refine ⟨H, K, F, G, hH, hK, hF, hG, ?_⟩
  filter_upwards [hHU, hKV] with ω hHUω hKVω
  intro z
  let z' : V := ⟨z, hUV z.property⟩
  have hpos := (hHUω z).1
  have hbound := (hHUω z).2.1
  have hfin := (hHUω z).2.2.1
  have hle : H ω z ≤ K ω z' := exact_containment_horizon_mono hUV
    (hHUω z).2.2.2.1 (hKVω z').1
  have heq (t : Ioi (0 : ℝ)) (ht : ENNReal.ofReal t ≤ H ω z) :
      F ω (z, t) = G ω (z', t) := by
    rw [(hHUω z).2.2.2.2.1 t ht, (hKVω z').2.1 t (ht.trans hle)]
  have hT : 0 < (H ω z).toReal := ENNReal.toReal_pos hpos.ne' hfin.ne
  let τ : Ioi (0 : ℝ) := ⟨(H ω z).toReal, hT⟩
  have hτ : ENNReal.ofReal τ = H ω z := ENNReal.ofReal_toReal hfin.ne
  refine ⟨hpos, hbound, hfin, hle, (hHUω z).2.2.2.1, (hKVω z').1,
    (hKVω z').2.1, heq, ⟨τ, rfl, ?_⟩, (hHUω z).2.2.2.2.2.2⟩
  intro t ht
  calc
    F ω (z, t) = F ω (z, τ) := (hHUω z).2.2.2.2.2.1 t τ ht hτ.ge
    _ = G ω (z', τ) := heq τ hτ.le

end HarmonicBalls
