import HarmonicBalls.FirstPass.S11h.GreenField11_17

/-!
# Measurable versions of the annular Green potential supremum (fp-S11p, owner n4)

Step N2 of `notes/fp-gaps/CHATGPT-n4-B2-z3-N1N2.md` section 6 (ChatGPT chat 105): the supremum
`SG(μ) = annulusGreenPotentialSup μ x₀ a b` is almost surely equal to a random variable measurable for an ARBITRARY
sub-σ-algebra `𝓖` of the ambient one, provided the masses of the open subsets of the annulus are almost surely equal to
`𝓖`-measurable random variables. The proof is the countable-supremum argument of `exists_annulusGreenField`
(`FirstPass/S11h/GreenField11_17.lean`, section 11.17 coordinate 6), with the mass decoders taken from the hypothesis
`hMass` instead of the distribution σ-algebra. No input is frozen here.

Terminology: annular Green potential (Armitage-Gardiner, Green kernel of the disc `B_b` with the diagonal value `+∞`).
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric
open scoped ENNReal

/-- Measurable version of `SG_{a,b}(x₀)` for a sub-σ-algebra `𝓖`: if every open subset `U` of the annulus
`𝔸_{a,b}(x₀)` has almost surely a `𝓖`-measurable mass `μ ω U`, then `ω ↦ SG(μ ω)` is almost surely equal to a
`𝓖`-measurable function. The supremum is taken over a countable set of centres `S ⊆ 𝔸_{a,b}(x₀)` and over the dyadic
levels of the lower semicontinuous kernel `annulusKernelExt x₀ b`, as in `exists_countable_annulusGreenPotentialSup`. -/
theorem exists_measurable_annulusGreenPotentialSup_version {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (𝓖 : MeasurableSpace Ω) (μ : Ω → Measure ℂ) (x₀ : ℂ) (a b : ℝ)
    (hMass : ∀ U : Set ℂ, IsOpen U → U ⊆ annulus x₀ a b →
      ∃ g : Ω → ℝ≥0∞, Measurable[𝓖] g ∧ ∀ᵐ ω ∂P, μ ω U = g ω) :
    ∃ G : Ω → ℝ≥0∞, Measurable[𝓖] G ∧ ∀ᵐ ω ∂P, G ω = annulusGreenPotentialSup (μ ω) x₀ a b := by
  obtain ⟨S, hSA, hSc, hSup⟩ := exists_countable_annulusGreenPotentialSup x₀ a b
  have : Countable S := hSc.to_subtype
  have hκ : ∀ x : ℂ, LowerSemicontinuous (fun y => annulusKernelExt x₀ b (x, y)) :=
    fun x => lowerSemicontinuous_annulusKernel_section x₀ b x
  have hU : ∀ (x : ℂ) (n k : ℕ),
      IsOpen (annulus x₀ a b ∩ dyadicLevel (fun y => annulusKernelExt x₀ b (x, y)) n k) :=
    fun x n k => (isOpen_annulus x₀ a b).inter
      ((hκ x).isOpen_preimage (ENNReal.ofReal (((k : ℝ) + 1) / 2 ^ n)))
  choose F hFm hFeq using fun (x : ℂ) (n k : ℕ) =>
    hMass _ (hU x n k) inter_subset_left
  have hae : ∀ᵐ ω ∂P, ∀ (x : S) (n k : ℕ),
      μ ω (annulus x₀ a b ∩ dyadicLevel (fun y => annulusKernelExt x₀ b ((x : ℂ), y)) n k) =
        F (x : ℂ) n k ω := by
    refine ae_all_iff.2 fun x => ae_all_iff.2 fun n => ae_all_iff.2 fun k => ?_
    exact hFeq (x : ℂ) n k
  -- the countable supremum over the centres and the dyadic levels, as a function of the measure
  have key : ∀ ν : Measure ℂ,
      (⨆ x : S, ⨆ n : ℕ, ∑ k ∈ Finset.range (n * 2 ^ n), ENNReal.ofReal ((2 ^ n : ℝ)⁻¹) *
        ν (annulus x₀ a b ∩ dyadicLevel (fun y => annulusKernelExt x₀ b ((x : ℂ), y)) n k)) =
        annulusGreenPotentialSup ν x₀ a b := by
    intro ν
    rw [hSup ν]
    refine Eq.trans (iSup_subtype'' S (fun x : ℂ => ⨆ n : ℕ, ∑ k ∈ Finset.range (n * 2 ^ n),
      ENNReal.ofReal ((2 ^ n : ℝ)⁻¹) * ν (annulus x₀ a b ∩ dyadicLevel (fun y => annulusKernelExt x₀ b (x, y)) n k))) ?_
    refine iSup_congr fun x => iSup_congr fun hx => ?_
    rw [lintegral_restrict_eq_iSup_dyadic ν (annulus x₀ a b) (hκ x)]
    exact iSup_congr fun n => (lintegral_restrict_dyadicFun_eq_sum ν _ (hκ x) n).symm
  refine ⟨fun ω => ⨆ x : S, ⨆ n : ℕ, ∑ k ∈ Finset.range (n * 2 ^ n),
      ENNReal.ofReal ((2 ^ n : ℝ)⁻¹) * F (x : ℂ) n k ω, ?_, ?_⟩
  · exact Measurable.iSup fun x => Measurable.iSup fun n =>
      Finset.measurable_sum _ fun k _ => (hFm (x : ℂ) n k).const_mul _
  · filter_upwards [hae] with ω hω
    have hω' : ∀ (x : S) (n k : ℕ), F (x : ℂ) n k ω =
        μ ω (annulus x₀ a b ∩ dyadicLevel (fun y => annulusKernelExt x₀ b ((x : ℂ), y)) n k) :=
      fun x n k => (hω x n k).symm
    simp only [hω']
    exact key (μ ω)

end HarmonicBalls
