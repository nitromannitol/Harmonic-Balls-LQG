import HarmonicBalls.Proofs.Sec5.LocalExactContainment

/-! # A field-local horizon for exact uniform containment -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

universe u

/-- The largest reciprocal dyadic time for which all clusters centred in the
half-disc are contained in the unit disc has a field-local representative.
The proposed LQG measure locality hypothesis is explicit. -/
theorem exists_fieldLocal_exact_dyadic_containment_horizon
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc) :
    ∃ H : Ω → ℝ, Measurable[fieldSigmaAlgebra α₀ hC (ball 0 1)] H ∧
      ∀ᵐ ω ∂P, 0 < H ω ∧ (∃ m, H ω = (2 : ℝ)⁻¹ ^ m) ∧
        (∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ t ∈ Ioo (0 : ℝ) (H ω),
          closure (cluster (μ ω) 1 z t) ⊆ ball 0 1) ∧
        ∀ m, μ ω ∈ unitClusterContainmentEvent m → (2 : ℝ)⁻¹ ^ m ≤ H ω := by
  classical
  obtain ⟨E, hE, heq⟩ := exists_local_lqg_unitClusterContainmentEvents
    hI2 hγ hγ2 hα hGFF hμ hloc
  let p : Ω → ℕ → Prop := fun ω m => ω ∈ E m ∨ (m = 0 ∧ ω ∉ ⋃ k, E k)
  have hex : ∀ ω, ∃ m, p ω m := by
    intro ω
    by_cases h : ∃ m, ω ∈ E m
    · obtain ⟨m, hm⟩ := h
      exact ⟨m, Or.inl hm⟩
    · refine ⟨0, Or.inr ⟨rfl, ?_⟩⟩
      simpa only [mem_iUnion, not_exists] using h
  have hp : ∀ m, MeasurableSet[fieldSigmaAlgebra α₀ hC (ball 0 1)] {ω | p ω m} := by
    intro m
    by_cases hm : m = 0
    · convert (hE m).union (MeasurableSet.iUnion hE).compl using 1
      ext ω
      simp [p, hm]
    · convert hE m using 1
      ext ω
      simp [p, hm]
  let H : Ω → ℝ := fun ω => (2 : ℝ)⁻¹ ^ Nat.find (hex ω)
  have hH : Measurable[fieldSigmaAlgebra α₀ hC (ball 0 1)] H := by
    let : MeasurableSpace Ω := fieldSigmaAlgebra α₀ hC (ball 0 1)
    exact (measurable_of_countable (fun m : ℕ => (2 : ℝ)⁻¹ ^ m)).comp (measurable_find hex hp)
  refine ⟨H, hH, ?_⟩
  have hgood : ∀ᵐ ω ∂P, ∃ m, μ ω ∈ unitClusterContainmentEvent m := by
    have hs := h71 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ (1 / 2) (by norm_num)
    filter_upwards [hs.ae_eventually_dyadic] with ω hω
    obtain ⟨m, hm⟩ := hω.exists
    refine ⟨m, ?_⟩
    intro z hz t ht x hx
    have hnear := hm t ⟨ht.1, ht.2.le⟩ z hz hx
    simp only [mem_ball, dist_zero_right] at hz ⊢
    have htri := dist_triangle x z (0 : ℂ)
    simp only [dist_zero_right] at htri
    simp only [mem_ball] at hnear
    norm_num at hnear hz ⊢
    linarith
  filter_upwards [heq, hgood] with ω heqω hgoodω
  obtain ⟨m, hm⟩ := hgoodω
  have hEexists : ∃ m, ω ∈ E m := ⟨m, (heqω m).mp hm⟩
  have hselected : ω ∈ E (Nat.find (hex ω)) := by
    rcases Nat.find_spec (hex ω) with h | ⟨_, h⟩
    · exact h
    · exact False.elim (h (mem_iUnion.mpr hEexists))
  refine ⟨by dsimp [H]; positivity, ⟨Nat.find (hex ω), rfl⟩, ?_, ?_⟩
  · exact (heqω _).mpr hselected
  · intro m hm
    have hmin : Nat.find (hex ω) ≤ m := Nat.find_min' (hex ω) (Or.inl ((heqω m).mp hm))
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hmin

end HarmonicBalls
