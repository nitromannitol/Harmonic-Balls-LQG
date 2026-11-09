import HarmonicBalls.Audit.GreenSubharmonicTestClass
import HarmonicBalls.Defs.Green
import HarmonicBalls.Proofs.Potential.BoundedDomainGreenMeasurability
import HarmonicBalls.Proofs.Potential.GreenPotentialExceptionalSet

/-! # Fatou step and Jensen bound for the bounded Jensen representative argument

Bou-Rabee and Gwynne, *Harmonic balls in Liouville quantum gravity* (arXiv:2208.11795), proof of the bounded Jensen
representative lemma (steps3 Section 1, lines 238-299). This file holds two independent pieces.

* `jensen_fatou_of_common_lower_bound` is a generic Fatou inequality for approximants bounded below by a common constant
  on a set `S` of finite measure. It uses only Mathlib measure theory and mentions no Green function. It is the Fatou
  step of the source argument (lines 286-298), stated for an arbitrary sequence with the listed properties. It is not the
  bounded representative theorem.
* `greenPotential_jensen_of_bounded_witness` treats a bounded witness domain `O`. The witness `(O, K, 0, ν, 0)` places
  `-greenPotential O ν` in `boundedSubharmonicBallTestClass S z` by definition, so the sub-mean hypothesis gives the
  integrability and the Jensen bound of the real Bochner potential with no approximation. It does not identify the
  classical extended potential (ℝ≥0∞, value `⊤` on the diagonal) with the Bochner potential; that identification needs
  smooth approximants of the Green potential and is not proved here.

The potential-theoretic infrastructure reached through the import closure uses work of Leonardo Bonanno, through the
pinned Lattice-Probability (lean-v4.35) port.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HarmonicBalls.BoundedJensenFatou

variable {μ : Measure ℂ}

/-- **Fatou step with a common lower bound (generic).** Let `S` be measurable with `μ S < ∞` and `z ∈ S`. Let `u n` be
measurable and `μ`-integrable on `S`, bounded below by `-c` on `S`, satisfy the sub-mean inequality
`∫_S u n dμ ≤ μ(S) u n(z)`, and converge at the centre, `u n z → L`. Let `V` be a function (values in `ℝ≥0∞`, `⊤`
allowed for classical infinite values) lying below the `liminf` of `ofReal (u n x + c)` on `S`. Then

* `∫_S V dμ ≤ ofReal ((L + c) μ(S))`;
* `V < ⊤` `μ`-almost everywhere on `S`;
* `V.toReal` is `μ`-integrable on `S`, and `∫_S ((V x).toReal - c) dμ ≤ L μ(S)`.

The argument is Fatou's lemma for the nonnegative functions `ofReal (u n + c)`, followed by the sub-mean bound and the
pole limit. -/
theorem jensen_fatou_of_common_lower_bound {S : Set ℂ} {z : ℂ} {c L : ℝ} {u : ℕ → ℂ → ℝ} {V : ℂ → ℝ≥0∞}
    (hS : MeasurableSet S) (hμS : μ S ≠ ⊤) (hz : z ∈ S)
    (hVm : AEMeasurable V (μ.restrict S))
    (hmeas : ∀ n, Measurable (u n)) (hint : ∀ n, IntegrableOn (u n) S μ)
    (hlb : ∀ n, ∀ x ∈ S, -c ≤ u n x)
    (hsub : ∀ n, ∫ x in S, u n x ∂μ ≤ μ.real S * u n z)
    (hpole : Tendsto (fun n => u n z) atTop (𝓝 L))
    (hV : ∀ x ∈ S, V x ≤ liminf (fun n => ENNReal.ofReal (u n x + c)) atTop) :
    (∫⁻ x in S, V x ∂μ ≤ ENNReal.ofReal ((L + c) * μ.real S)) ∧
      (∀ᵐ x ∂(μ.restrict S), V x < ⊤) ∧
      Integrable (fun x => (V x).toReal) (μ.restrict S) ∧
      ∫ x in S, ((V x).toReal - c) ∂μ ≤ L * μ.real S := by
  have hfin : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.2 hμS
  have hLc : -c ≤ L := ge_of_tendsto' hpole (fun n => hlb n z hz)
  have hμnn : 0 ≤ μ.real S := measureReal_nonneg
  have hfm : ∀ n, Measurable (fun x => ENNReal.ofReal (u n x + c)) := fun n =>
    ((hmeas n).add_const c).ennreal_ofReal
  have hfatou : ∫⁻ x, liminf (fun n => ENNReal.ofReal (u n x + c)) atTop ∂(μ.restrict S) ≤
      liminf (fun n => ∫⁻ x, ENNReal.ofReal (u n x + c) ∂(μ.restrict S)) atTop :=
    lintegral_liminf_le hfm
  -- Each lower integral is bounded by the sub-mean value at the centre.
  have hbound : ∀ n, ∫⁻ x, ENNReal.ofReal (u n x + c) ∂(μ.restrict S) ≤
      ENNReal.ofReal ((u n z + c) * μ.real S) := by
    intro n
    have hi : Integrable (fun x => u n x + c) (μ.restrict S) :=
      (hint n).add (integrable_const c)
    have hnn : 0 ≤ᵐ[μ.restrict S] (fun x => u n x + c) := by
      filter_upwards [ae_restrict_mem hS] with x hx
      show 0 ≤ u n x + c
      linarith [hlb n x hx]
    rw [← ofReal_integral_eq_lintegral_ofReal hi hnn]
    apply ENNReal.ofReal_le_ofReal
    rw [integral_add (hint n) (integrable_const c), integral_const, measureReal_restrict_apply_univ,
      smul_eq_mul, show (u n z + c) * μ.real S = μ.real S * u n z + μ.real S * c by ring]
    linarith [hsub n]
  -- The pole limit gives the right-hand limit.
  have hlim : Tendsto (fun n => ENNReal.ofReal ((u n z + c) * μ.real S)) atTop
      (𝓝 (ENNReal.ofReal ((L + c) * μ.real S))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp ((hpole.add_const c).mul_const (μ.real S))
  have hmain : ∫⁻ x in S, V x ∂μ ≤ ENNReal.ofReal ((L + c) * μ.real S) := by
    calc ∫⁻ x in S, V x ∂μ
        ≤ ∫⁻ x, liminf (fun n => ENNReal.ofReal (u n x + c)) atTop ∂(μ.restrict S) := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem hS] with x hx
          exact hV x hx
      _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (u n x + c) ∂(μ.restrict S)) atTop := hfatou
      _ ≤ liminf (fun n => ENNReal.ofReal ((u n z + c) * μ.real S)) atTop :=
          liminf_le_liminf (Eventually.of_forall hbound)
      _ = ENNReal.ofReal ((L + c) * μ.real S) := hlim.liminf_eq
  have hne : ∫⁻ x in S, V x ∂μ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmain
  have hfin_ae : ∀ᵐ x ∂(μ.restrict S), V x < ⊤ := ae_lt_top' hVm hne
  have hint_V : Integrable (fun x => (V x).toReal) (μ.restrict S) :=
    integrable_toReal_of_lintegral_ne_top hVm hne
  refine ⟨hmain, hfin_ae, hint_V, ?_⟩
  have hI : ∫ x in S, (V x).toReal ∂μ = (∫⁻ x in S, V x ∂μ).toReal := integral_toReal hVm hfin_ae
  have hIle : (∫⁻ x in S, V x ∂μ).toReal ≤ (L + c) * μ.real S := by
    have hnn : 0 ≤ (L + c) * μ.real S := mul_nonneg (by linarith) hμnn
    calc (∫⁻ x in S, V x ∂μ).toReal ≤ (ENNReal.ofReal ((L + c) * μ.real S)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hmain
      _ = (L + c) * μ.real S := ENNReal.toReal_ofReal hnn
  rw [integral_sub hint_V (integrable_const c), integral_const, measureReal_restrict_apply_univ,
    smul_eq_mul, hI]
  linarith [show (L + c) * μ.real S = L * μ.real S + c * μ.real S by ring]

/-- **Real Bochner potential of a bounded witness.** Let `O` be a bounded open set with `closure S ⊆ O`, and let `ν` be a
finite measure concentrated on a compact `K ⊆ O` with `ν {z} = 0` and `greenFunction O z` `ν`-integrable (the conditions
of `boundedSubharmonicBallTestClass`). If the sub-mean inequality holds for every bounded test function, then the real
Green potential `greenPotential O ν` is `μ`-integrable on `S` and
`∫_S greenPotential O ν dμ ≤ μ(S) · greenPotential O ν z`.

The proof uses the witness `(O, K, 0, ν, 0)`, which places `-greenPotential O ν` in the bounded test class. This covers
the Bochner potential only; the agreement with the classical extended potential `∫⁻ greenKernelExtended O x y dν` at
`μ`-almost every point is not part of this statement. -/
theorem greenPotential_jensen_of_bounded_witness {S : Set ℂ} {z : ℂ}
    (hJ : ∀ F ∈ boundedSubharmonicBallTestClass S z, HasSubMeanValueProperty μ S z F)
    {O K : Set ℂ} (hO : IsOpen O) (hOb : Bornology.IsBounded O) (hSO : closure S ⊆ O)
    (hK : IsCompact K) (hKO : K ⊆ O) {ν : Measure ℂ} [IsFiniteMeasure ν] (hνK : ν Kᶜ = 0)
    (hνz : ν {z} = 0) (hνi : Integrable (greenFunction O z) ν) :
    IntegrableOn (greenPotential O ν) S μ ∧
      ∫ x in S, greenPotential O ν x ∂μ ≤ μ.real S * greenPotential O ν z := by
  have hmem : (fun x => -greenPotential O ν x) ∈ boundedSubharmonicBallTestClass S z := by
    refine ⟨O, K, 0, ν, 0, hO, hOb, hSO, hK, hKO, inferInstance, inferInstance, by simp,
      hνK, by simp, InnerProductSpace.harmonicOnNhd_const 0, hνz, hνi, ?_⟩
    funext x
    simp [greenPotential]
  obtain ⟨hint, hsub⟩ := hJ _ hmem
  simp only [integral_neg] at hsub
  refine ⟨integrable_neg_iff.mp hint, ?_⟩
  rw [neg_mul] at hsub
  linarith

/-- **Classical finiteness forces agreement with the Bochner potential (pointwise).** Let `O` be bounded and open, and
let `ν` be a measure. If the classical extended potential `∫⁻ greenKernelExtended O x y ∂ν` (ℝ≥0∞-valued, `⊤` on the
diagonal) is finite at `x`, then `ν {x} = 0`, the Green kernel `greenFunction O x` is `ν`-integrable, and the real
Bochner value `greenPotential O ν x` equals the real part of the classical value. This is pointwise. The
almost-everywhere finiteness of the classical potential on `S` is the open input of `jensen_fatou_of_common_lower_bound`
and is not supplied here. -/
theorem greenPotential_eq_toReal_of_classical_lt_top {O : Set ℂ} (hO : IsOpen O) (hOb : Bornology.IsBounded O)
    {ν : Measure ℂ} {x : ℂ} (hx : ∫⁻ y, greenKernelExtended O x y ∂ν < ⊤) :
    ν {x} = 0 ∧ Integrable (greenFunction O x) ν ∧
      greenPotential O ν x = (∫⁻ y, greenKernelExtended O x y ∂ν).toReal := by
  have hatom : ν {x} = 0 := by
    by_contra hne
    have h1 : ∫⁻ y, Set.indicator {x} (fun _ => (⊤ : ℝ≥0∞)) y ∂ν ≤
        ∫⁻ y, greenKernelExtended O x y ∂ν := by
      apply lintegral_mono
      intro y
      by_cases hy : y = x
      · subst hy
        simp [greenKernelExtended]
      · simp [hy]
    rw [lintegral_indicator_const (measurableSet_singleton x), ENNReal.top_mul hne] at h1
    exact lt_irrefl _ (lt_of_le_of_lt h1 hx)
  have hae : ∀ᵐ y ∂ν, y ≠ x := ae_iff.mpr (by simpa using hatom)
  have hcongr : ∫⁻ y, greenKernelExtended O x y ∂ν = ∫⁻ y, ENNReal.ofReal (greenFunction O x y) ∂ν := by
    apply lintegral_congr_ae
    filter_upwards [hae] with y hy
    simp [greenKernelExtended, hy]
  have hmeas : Measurable (greenFunction O x) :=
    (measurable_greenFunction_uncurry hO).comp (measurable_const.prodMk measurable_id)
  have hi : Integrable (greenFunction O x) ν := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun y => greenFunction_nonneg hOb x y))]
    rw [← hcongr]
    exact hx
  have hP : 0 ≤ greenPotential O ν x := integral_nonneg (fun y => greenFunction_nonneg hOb x y)
  refine ⟨hatom, hi, ?_⟩
  rw [lintegral_greenKernelExtended_eq hOb hatom hi, ENNReal.toReal_ofReal hP]

end HarmonicBalls.BoundedJensenFatou
