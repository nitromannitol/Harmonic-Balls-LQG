import HarmonicBalls.Proofs.Sec8.RootedMassApproximation

/-! # Measurable translated circle averages

The imported Section 8 development uses Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization.
-/

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal Topology

namespace HarmonicBalls

/-- The translated dyadic circle averages have a jointly measurable version
at every scale, simultaneously equal to the original averages under a rooted
law. The version has the same recentered LQG limit. -/
theorem IsWholePlaneGFF.exists_rooted_circle_measurable_version
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) (hm : AEMeasurable μ P)
    (B : Set ℂ) (hB : MeasurableSet B) (w : ℂ → ℝ≥0∞) (hw : Measurable w) :
    ∃ g : (Ω × ℂ) → ℝ → ℂ → ℝ,
      (∀ n, Measurable (fun p : (Ω × ℂ) × ℂ => g p.1 (dyadicScale n) p.2)) ∧
      ∀ᵐ x ∂(P ⊗ₘ weightedRestrictionKernel P μ hm B hB w hw),
        (∀ n z, g x (dyadicScale n) z =
          fieldCircleAverage α₀ (hcirc x.1) (dyadicScale n) (z + x.2)) ∧
        (∀ n, Continuous (g x (dyadicScale n))) ∧
        IsLQGLimit γ (g x) ((μ x.1).map (fun v : ℂ => v - x.2)) := by
  classical
  have hv (n : ℕ) : ∃ d : Ω → ℂ → ℝ,
      Measurable (Function.uncurry d) ∧ ∀ᵐ ω ∂P, ∀ z,
        d ω z = fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) z := by
    obtain ⟨d, hdm, hdeq⟩ := exists_joint_local_version_of_pointwise
      (inferInstance : MeasurableSpace Ω) isOpen_univ
      (fun ω z => fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) z)
      (hGFF.ae_continuous_fieldCircleAverage α₀ (dyadicScale_pos n))
      (fun z _ => ⟨_, by
        simp only [fieldCircleAverage]
        exact (hGFF.measurable_circle _ z (dyadicScale_pos n)).sub_const _,
        Filter.Eventually.of_forall fun _ => rfl⟩)
    exact ⟨d, hdm, hdeq.mono fun _ h z => h z (mem_univ z)⟩
  choose d hdm hdeq using hv
  let idx : ℝ → ℕ := fun r => if hr : ∃ n, dyadicScale n = r then Nat.find hr else 0
  have hidx (n : ℕ) : dyadicScale (idx (dyadicScale n)) = dyadicScale n := by
    have hex : ∃ k : ℕ, dyadicScale k = dyadicScale n := ⟨n, rfl⟩
    simp only [idx, hex, ↓reduceDIte]
    exact Nat.find_spec hex
  let g : (Ω × ℂ) → ℝ → ℂ → ℝ := fun x r z => d (idx r) x.1 (z + x.2)
  refine ⟨g, ?_, ?_⟩
  · intro n
    exact (hdm (idx (dyadicScale n))).comp
      ((measurable_fst.comp measurable_fst).prodMk
        (measurable_snd.add (measurable_snd.comp measurable_fst)))
  · let K := weightedRestrictionKernel P μ hm B hB w hw
    have heq : ∀ᵐ ω ∂P, ∀ n z, d n ω z =
        fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) z := ae_all_iff.mpr hdeq
    have hc : ∀ᵐ ω ∂P, ∀ n,
        Continuous (fieldCircleAverage α₀ (hcirc ω) (dyadicScale n)) :=
      ae_all_iff.mpr fun n => hGFF.ae_continuous_fieldCircleAverage α₀ (dyadicScale_pos n)
    filter_upwards [ae_fst_of_ae_compProd P K heq, ae_fst_of_ae_compProd P K hc,
      ae_fst_of_ae_compProd P K hμ] with x hx hcx hμx
    have hg : ∀ n z, g x (dyadicScale n) z =
        fieldCircleAverage α₀ (hcirc x.1) (dyadicScale n) (z + x.2) := by
      intro n z
      dsimp only [g]
      rw [hx, hidx]
    have hgcont : ∀ n, Continuous (g x (dyadicScale n)) := by
      intro n
      have he : g x (dyadicScale n) = fun z =>
          fieldCircleAverage α₀ (hcirc x.1) (dyadicScale n) (z + x.2) := funext (hg n)
      rw [he]
      exact (hcx n).comp (continuous_id.add continuous_const)
    refine ⟨hg, hgcont, ?_⟩
    have hlim := Section6.isLQGLimit_translate hμx hcx x.2
    refine ⟨hlim.isLocallyFiniteMeasure, ?_⟩
    intro f hf hfc
    convert hlim.tendsto_integral f hf hfc using 1
    funext n
    congr 1
    unfold lqgApprox
    congr 1
    funext z
    rw [hg]

end HarmonicBalls
