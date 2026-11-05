import HarmonicBalls.Proofs.Sec6.CollarReturnProbability
import HarmonicBalls.Proofs.Sec6.BrownianScaling

/-! # Spatial transport of collar-return probabilities -/

namespace HarmonicBalls.Section6

open MeasureTheory Set MarkovProcess
open scoped ENNReal NNReal

/-- A spatial homeomorphism carries the core-return event to the corresponding
return event for the images of the three sets. -/
theorem core_return_comp_homeomorph_iff
    (f : ℂ ≃ₜ ℂ) (A B C : Set ℂ) (ω : ContinuousPath ℂ) :
    (∃ t : ℝ≥0, ContinuousPath.exitTime (f '' B) ((⟨f, f.continuous⟩ : C(ℂ, ℂ)).comp ω) ≤
        (t : ℝ≥0∞) ∧ (t : ℝ≥0∞) <
        ContinuousPath.exitTime (f '' A) ((⟨f, f.continuous⟩ : C(ℂ, ℂ)).comp ω) ∧
        ((⟨f, f.continuous⟩ : C(ℂ, ℂ)).comp ω) t ∈ f '' C) ↔
      ∃ t : ℝ≥0, ContinuousPath.exitTime B ω ≤ (t : ℝ≥0∞) ∧
        (t : ℝ≥0∞) < ContinuousPath.exitTime A ω ∧ ω t ∈ C := by
  have he (U : Set ℂ) : ContinuousPath.exitTime (f '' U)
      ((⟨f, f.continuous⟩ : C(ℂ, ℂ)).comp ω) = ContinuousPath.exitTime U ω := by
    exact exitTime_comp_injective (⟨f, f.continuous⟩ : C(ℂ, ℂ)) f.injective U ω
  simp only [he]
  constructor <;> rintro ⟨t, hB, hA, hC⟩
  · refine ⟨t, hB, hA, ?_⟩
    obtain ⟨x, hx, hxeq⟩ := hC
    exact f.injective hxeq ▸ hx
  · exact ⟨t, hB, hA, ⟨ω t, hC, rfl⟩⟩

/-- A spatial homeomorphism and a corresponding path-law identity preserve
core-return probabilities, even for nonmeasurable sets. -/
theorem measure_core_return_eq_of_homeomorph
    (f : ℂ ≃ₜ ℂ) (A B C : Set ℂ) (μ ν : Measure (ContinuousPath ℂ))
    (hmap : μ.map ((Homeomorph.refl ℝ≥0).arrowCongr f) = ν) :
    ν {ω | ∃ t : ℝ≥0, ContinuousPath.exitTime (f '' B) ω ≤ (t : ℝ≥0∞) ∧
        (t : ℝ≥0∞) < ContinuousPath.exitTime (f '' A) ω ∧ ω t ∈ f '' C} =
      μ {ω | ∃ t : ℝ≥0, ContinuousPath.exitTime B ω ≤ (t : ℝ≥0∞) ∧
        (t : ℝ≥0∞) < ContinuousPath.exitTime A ω ∧ ω t ∈ C} := by
  rw [← hmap, ((Homeomorph.refl ℝ≥0).arrowCongr f).measurableEmbedding.map_apply]
  congr 1
  ext ω
  exact core_return_comp_homeomorph_iff f A B C ω

/-- Simultaneously translating the starting point and all three sets leaves
Brownian core-return probabilities unchanged. -/
theorem planarBrownian_core_return_add (x v : ℂ) (A B C : Set ℂ) :
    planarBrownianMotion (x + v)
      {ω | ∃ t : ℝ≥0, ContinuousPath.exitTime ((fun z : ℂ => z + v) '' B) ω ≤
          (t : ℝ≥0∞) ∧ (t : ℝ≥0∞) <
          ContinuousPath.exitTime ((fun z : ℂ => z + v) '' A) ω ∧
          ω t ∈ (fun z : ℂ => z + v) '' C} =
      planarBrownianMotion x {ω | ∃ t : ℝ≥0,
        ContinuousPath.exitTime B ω ≤ (t : ℝ≥0∞) ∧
        (t : ℝ≥0∞) < ContinuousPath.exitTime A ω ∧ ω t ∈ C} := by
  exact measure_core_return_eq_of_homeomorph (Homeomorph.addRight v) A B C
    (planarBrownianMotion x) (planarBrownianMotion (x + v))
    (planarBrownianMotion_map_add_from x v)


/-- A shifted starting point is controlled by a return event at the original
point whenever the translated inner domain is smaller and the translated
outer domain and core are larger. -/
theorem planarBrownian_core_return_le_of_translation
    (x v : ℂ) (A B C A' B' C' : Set ℂ)
    (hB : (fun z : ℂ => z + v) '' B' ⊆ B)
    (hA : A ⊆ (fun z : ℂ => z + v) '' A')
    (hC : C ⊆ (fun z : ℂ => z + v) '' C') :
    planarBrownianMotion (x + v) {ω | ∃ t : ℝ≥0,
      ContinuousPath.exitTime B ω ≤ (t : ℝ≥0∞) ∧
      (t : ℝ≥0∞) < ContinuousPath.exitTime A ω ∧ ω t ∈ C} ≤
    planarBrownianMotion x {ω | ∃ t : ℝ≥0,
      ContinuousPath.exitTime B' ω ≤ (t : ℝ≥0∞) ∧
      (t : ℝ≥0∞) < ContinuousPath.exitTime A' ω ∧ ω t ∈ C'} := by
  rw [← planarBrownian_core_return_add x v A' B' C']
  apply measure_mono
  rintro ω ⟨t, htB, htA, htC⟩
  refine ⟨t, (ContinuousPath.exitTime_mono hB ω).trans htB, ?_, hC htC⟩
  exact htA.trans_le (ContinuousPath.exitTime_mono hA ω)

end HarmonicBalls.Section6
