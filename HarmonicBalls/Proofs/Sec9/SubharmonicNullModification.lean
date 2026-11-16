import HarmonicBalls.Draft.Section4

/-! # Puncturing real signed Green tests

The extended absolute kernel records the infinite diagonal while the real-valued
integrals use the existing Green potential. -/

namespace HarmonicBalls

open MeasureTheory Metric Set InnerProductSpace

/-- A finite extended kernel integral cannot charge its infinite diagonal. -/
theorem measure_singleton_eq_zero_of_extended_green_integral_lt_top
    (O : Set ℂ) (x : ℂ) (ν : Measure ℂ)
    (h : (∫⁻ y, Function.update (fun y => ENNReal.ofReal |greenFunction O x y|) x ⊤ y ∂ν) < ⊤) :
    ν {x} = 0 := by
  have hle := setLIntegral_le_lintegral (μ := ν) {x}
    (Function.update (fun y => ENNReal.ofReal |greenFunction O x y|) x ⊤)
  rw [lintegral_singleton, Function.update_self] at hle
  by_contra hn
  rw [ENNReal.top_mul hn] at hle
  exact (not_lt_of_ge hle) h

/-- Deleting a center of zero mass preserves every real signed Green test
whose two source integrals are finite on the witness closure. -/
theorem punctured_signed_green_submean
    {μ : Measure ℂ} {G : Set ℂ} {z : ℂ}
    (hG : IsOpen G) (hz : z ∈ G) (hμz : μ {z} = 0)
    (hpos : 0 < μ G) (hfinite : μ G < ⊤)
    (hmean : ∀ (O K : Set ℂ) (ν₁ ν₂ : Measure ℂ) (q : ℂ → ℝ),
      IsOpen O → closure G ⊆ O → IsCompact K → K ⊆ O →
      IsFiniteMeasure ν₁ → IsFiniteMeasure ν₂ → ν₁ ⟂ₘ ν₂ →
      ν₁ Kᶜ = 0 → ν₂ Kᶜ = 0 → ν₁ G = 0 → HarmonicOnNhd q O →
      (∀ x ∈ closure O,
        Integrable (greenFunction O x) ν₁ ∧ Integrable (greenFunction O x) ν₂ ∧
        (∫⁻ y, Function.update (fun y => ENNReal.ofReal |greenFunction O x y|) x ⊤ y ∂ν₁) < ⊤ ∧
        (∫⁻ y, Function.update (fun y => ENNReal.ofReal |greenFunction O x y|) x ⊤ y ∂ν₂) < ⊤) →
      IntegrableOn (q + greenPotential O ν₁ - greenPotential O ν₂) G μ →
      (q + greenPotential O ν₁ - greenPotential O ν₂) z * μ.real G ≤
        ∫ x in G, (q + greenPotential O ν₁ - greenPotential O ν₂) x ∂μ) :
    IsOpen (G \ {z}) ∧ z ∉ G \ {z} ∧ 0 < μ (G \ {z}) ∧ μ (G \ {z}) < ⊤ ∧
    ∀ (O K : Set ℂ) (ν₁ ν₂ : Measure ℂ) (q : ℂ → ℝ),
      IsOpen O → closure (G \ {z}) ⊆ O → IsCompact K → K ⊆ O →
      IsFiniteMeasure ν₁ → IsFiniteMeasure ν₂ → ν₁ ⟂ₘ ν₂ →
      ν₁ Kᶜ = 0 → ν₂ Kᶜ = 0 → ν₁ (G \ {z}) = 0 → HarmonicOnNhd q O →
      (∀ x ∈ closure O,
        Integrable (greenFunction O x) ν₁ ∧ Integrable (greenFunction O x) ν₂ ∧
        (∫⁻ y, Function.update (fun y => ENNReal.ofReal |greenFunction O x y|) x ⊤ y ∂ν₁) < ⊤ ∧
        (∫⁻ y, Function.update (fun y => ENNReal.ofReal |greenFunction O x y|) x ⊤ y ∂ν₂) < ⊤) →
      IntegrableOn (q + greenPotential O ν₁ - greenPotential O ν₂) (G \ {z}) μ →
      (q + greenPotential O ν₁ - greenPotential O ν₂) z * μ.real (G \ {z}) ≤
        ∫ x in G \ {z}, (q + greenPotential O ν₁ - greenPotential O ν₂) x ∂μ := by
  have hclosure : closure (G \ {z}) = closure G := by
    apply le_antisymm (closure_mono sdiff_subset)
    apply closure_minimal _ isClosed_closure
    simpa only [sdiff_eq] using (dense_compl_singleton z).open_subset_closure_inter hG
  have hae : (G \ {z}) =ᵐ[μ] G := sdiff_null_ae_eq_self hμz
  have hm : μ (G \ {z}) = μ G := measure_congr hae
  have hr : μ.restrict (G \ {z}) = μ.restrict G := Measure.restrict_congr_set hae
  refine ⟨hG.sdiff isClosed_singleton, by simp, by simpa [hm] using hpos,
    by simpa [hm] using hfinite, ?_⟩
  intro O K ν₁ ν₂ q hO hGO hK hKO hf₁ hf₂ hsing hK₁ hK₂ hzero hq hint htest
  have hzO : z ∈ closure O := subset_closure (hGO (by rw [hclosure]; exact subset_closure hz))
  have hzν : ν₁ {z} = 0 :=
    measure_singleton_eq_zero_of_extended_green_integral_lt_top O z ν₁ (hint z hzO).2.2.1
  have hzG : ν₁ G = 0 := by
    rw [← measure_sdiff_null hzν]
    exact hzero
  have htestG : IntegrableOn (q + greenPotential O ν₁ - greenPotential O ν₂) G μ := by
    simpa only [IntegrableOn, ← hr] using htest
  have hresult := hmean O K ν₁ ν₂ q hO (by simpa only [hclosure] using hGO)
    hK hKO hf₁ hf₂ hsing hK₁ hK₂ hzG hq hint htestG
  simpa only [Measure.real, hm, hr] using hresult

end HarmonicBalls
