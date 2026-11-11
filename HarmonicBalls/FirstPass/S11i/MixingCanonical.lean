import HarmonicBalls.FirstPass.S11i.CylinderFactor
import HarmonicBalls.FirstPass.S11i.Faithful
import HarmonicBalls.Proofs.MeasureTheory.CylinderMixingExtension
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Step 8 helper: the canonical dilation is measure preserving

Source: corrected paper, `s11-pinch:lem:mixing` (tex lines 3769-3812), the identification of the dilation `𝒯 g = g(·/2)`
on whole-plane fields modulo constants. On the canonical space `ModConstTestPairings univ` (pairings with mean-zero test
functions) the law `P_c = P.map (fun ω φ => hC ω φ)` is invariant under the dual dilation `(T L) φ = L (κ₁ φ)`:
equal finite-dimensional laws (Gaussian with equal covariance, `cov_dilated_eq`) and uniqueness on cylinders.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ProbabilityTheory

namespace HarmonicBalls

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The real inner product of `toLp v` with `t` in `EuclideanSpace ℝ ι`. -/
theorem inner_toLp_fun {ι : Type*} [Fintype ι] (v : ι → ℝ) (t : EuclideanSpace ℝ ι) :
    inner ℝ (WithLp.toLp 2 v) t = ∑ j, WithLp.ofLp t j * v j := by
  simp [PiLp.inner_apply, mul_comm]

/-- Centred jointly Gaussian vectors with equal covariance have equal laws (charFun uniqueness on
`EuclideanSpace`, transferred to `ι → ℝ`). -/
theorem map_eq_of_gaussian_cov {ι : Type*} [Fintype ι] [IsProbabilityMeasure P] {Y Y' : ι → Ω → ℝ}
    (hm : ∀ j, Measurable (Y j)) (hm' : ∀ j, Measurable (Y' j))
    (hY : HasGaussianLaw (fun ω (j : ι) => Y j ω) P) (hY' : HasGaussianLaw (fun ω (j : ι) => Y' j ω) P)
    (h0 : ∀ j, ∫ ω, Y j ω ∂P = 0) (h0' : ∀ j, ∫ ω, Y' j ω ∂P = 0)
    (hcov : ∀ j l, cov[Y j, Y l; P] = cov[Y' j, Y' l; P]) :
    P.map (fun ω (j : ι) => Y j ω) = P.map (fun ω (j : ι) => Y' j ω) := by
  have hV : Measurable (fun ω => (WithLp.toLp 2 (fun j => Y j ω) : EuclideanSpace ℝ ι)) :=
    (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 hm)
  have hV' : Measurable (fun ω => (WithLp.toLp 2 (fun j => Y' j ω) : EuclideanSpace ℝ ι)) :=
    (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 hm')
  have hchar : charFun (P.map (fun ω => (WithLp.toLp 2 (fun j => Y j ω) : EuclideanSpace ℝ ι))) =
      charFun (P.map (fun ω => (WithLp.toLp 2 (fun j => Y' j ω) : EuclideanSpace ℝ ι))) := by
    funext t
    rw [charFun_apply, charFun_apply,
      integral_map hV.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop)),
      integral_map hV'.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))]
    simp only [inner_toLp_fun]
    rw [integral_exp_linComb_eq hY h0 (WithLp.ofLp t), integral_exp_linComb_eq hY' h0' (WithLp.ofLp t)]
    simp only [hcov]
  have hmeas := Measure.ext_of_charFun hchar
  calc P.map (fun ω (j : ι) => Y j ω)
      = ((P.map (fun ω => (WithLp.toLp 2 (fun j => Y j ω) : EuclideanSpace ℝ ι))).map
          (WithLp.ofLp)) := by
        rw [Measure.map_map (WithLp.measurable_ofLp 2 _) hV]; rfl
    _ = ((P.map (fun ω => (WithLp.toLp 2 (fun j => Y' j ω) : EuclideanSpace ℝ ι))).map
          (WithLp.ofLp)) := by rw [hmeas]
    _ = P.map (fun ω (j : ι) => Y' j ω) := by
        rw [Measure.map_map (WithLp.measurable_ofLp 2 _) hV']; rfl

/-- The index set of the canonical space: mean-zero test functions. -/
abbrev CanonIdx := {φ : ℂ → ℝ // IsTestFunction (univ : Set ℂ) φ ∧ ∫ x, φ x = 0}

/-- The dual dilation on the canonical space: `(T L) φ = L (κ₁ φ)` with `κ₁ = dilateTest 1` (`(g(·/2), k) = (g, κ₁ k)`). -/
noncomputable def dilOp : ModConstTestPairings (univ : Set ℂ) → ModConstTestPairings (univ : Set ℂ) :=
  fun L (i : CanonIdx) => L ⟨dilateTest 1 i.1, isTestFunction_dilateTest i.2.1 1, (integral_dilateTest 1 i.1).trans i.2.2⟩

/-- The canonical law: the law of the pairings `φ ↦ hC ω φ` with mean-zero test functions `φ`. -/
noncomputable def canonicalLaw (hC : Ω → (ℂ → ℝ) → ℝ) (P : Measure Ω) :
    Measure (ModConstTestPairings (univ : Set ℂ)) :=
  P.map (fun ω i => hC ω i.1)

theorem measurable_dilOp :
    Measurable (dilOp : ModConstTestPairings (univ : Set ℂ) → ModConstTestPairings (univ : Set ℂ)) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

theorem measurable_canonical (hh : IsWholePlaneGFF P hC hcirc) :
    Measurable (fun ω (i : CanonIdx) => hC ω i.1) :=
  measurable_pi_iff.2 fun i => hh.measurable_pairing i.1 i.2.1

/-- The finite-dimensional laws of the dilated canonical field agree with those of the field: the joint law of
`(hC ω (κ₁ φ_j))_j` equals that of `(hC ω φ_j)_j`, by equal covariances (`cov_dilated_eq`, `n = 1`). -/
theorem map_dilate_eq [IsProbabilityMeasure P] (hh : IsWholePlaneGFF P hC hcirc) :
    P.map (fun ω (i : CanonIdx) => hC ω (dilateTest 1 i.1)) =
      P.map (fun ω (i : CanonIdx) => hC ω i.1) := by
  refine MeasureTheory.ext_of_generate_finite (measurableCylinders fun _ : CanonIdx => ℝ)
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders ?_ ?_
  · intro s hs
    simp only [measurableCylinders, mem_iUnion, mem_singleton_iff, exists_prop] at hs
    obtain ⟨J, B, hB, rfl⟩ := hs
    have hY : Measurable (fun ω (j : J) => hC ω (dilateTest 1 j.1.1)) :=
      measurable_pi_iff.2 fun j => hh.measurable_pairing _ (isTestFunction_dilateTest j.1.2.1 1)
    have hY0 : Measurable (fun ω (j : J) => hC ω j.1.1) :=
      measurable_pi_iff.2 fun j => hh.measurable_pairing _ j.1.2.1
    have hJ := map_eq_of_gaussian_cov (ι := J) (Y := fun j ω => hC ω j.1.1)
      (Y' := fun j ω => hC ω (dilateTest 1 j.1.1))
      (fun j => hh.measurable_pairing _ j.1.2.1)
      (fun j => hh.measurable_pairing _ (isTestFunction_dilateTest j.1.2.1 1))
      (hasGaussianLaw_pairing_family hh (fun j : J => j.1.1) (fun j => j.1.2.1))
      (hasGaussianLaw_pairing_family hh (fun j : J => dilateTest 1 j.1.1)
        (fun j => isTestFunction_dilateTest j.1.2.1 1))
      (fun j => integral_pairing_eq_zero hh j.1.2.1)
      (fun j => integral_pairing_eq_zero hh (isTestFunction_dilateTest j.1.2.1 1))
      (fun j l => (cov_dilated_eq hh j.1.2.1 l.1.2.1 j.1.2.2 l.1.2.2 1).symm)
    have hm1 : Measurable (fun ω (i : CanonIdx) => hC ω (dilateTest 1 i.1)) :=
      measurable_pi_iff.2 fun i => hh.measurable_pairing _ (isTestFunction_dilateTest i.2.1 1)
    have hg : Measurable (fun (f : CanonIdx → ℝ) (i : J) => f i.1) :=
      measurable_pi_iff.2 fun i => measurable_pi_apply i.1
    have hcyl : MeasurableSet (cylinder J B) := hg hB
    rw [Measure.map_apply hm1 hcyl, Measure.map_apply (measurable_canonical hh) hcyl]
    show P ((fun ω (j : J) => hC ω (dilateTest 1 j.1.1)) ⁻¹' B) =
      P ((fun ω (j : J) => hC ω j.1.1) ⁻¹' B)
    rw [← Measure.map_apply hY hB, ← Measure.map_apply hY0 hB, hJ]
  · simp

theorem dilateTest_one_comp (n : ℕ) (k : ℂ → ℝ) : dilateTest n (dilateTest 1 k) = dilateTest (n + 1) k := by
  funext y
  have h2 : (2 : ℝ) ^ 1 * (2 : ℝ) ^ n = (2 : ℝ) ^ (n + 1) := by ring
  simp only [dilateTest]
  rw [smul_smul, h2]
  ring

/-- Iterates of the dual dilation: `(T^[n] L) φ = L (κₙ φ)`. -/
theorem iterate_dilOp (n : ℕ) (L : ModConstTestPairings (univ : Set ℂ)) (i : CanonIdx) :
    (dilOp^[n] L) i = L ⟨dilateTest n i.1, isTestFunction_dilateTest i.2.1 n, (integral_dilateTest n i.1).trans i.2.2⟩ := by
  induction n generalizing i with
  | zero =>
    have hk : dilateTest 0 i.1 = i.1 := funext fun y => by simp [dilateTest]
    exact congrArg L (Subtype.ext hk.symm)
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have h := ih ⟨dilateTest 1 i.1, isTestFunction_dilateTest i.2.1 1, (integral_dilateTest 1 i.1).trans i.2.2⟩
    exact h.trans (congrArg L (Subtype.ext (dilateTest_one_comp n i.1)))

theorem measurePreserving_dilOp [IsProbabilityMeasure P] (hh : IsWholePlaneGFF P hC hcirc) :
    MeasurePreserving (dilOp : ModConstTestPairings (univ : Set ℂ) → ModConstTestPairings (univ : Set ℂ))
      (canonicalLaw hC P) (canonicalLaw hC P) := by
  refine ⟨measurable_dilOp, ?_⟩
  unfold canonicalLaw
  rw [Measure.map_map measurable_dilOp (measurable_canonical hh)]
  exact map_dilate_eq hh

theorem isProbabilityMeasure_canonicalLaw [IsProbabilityMeasure P] (hh : IsWholePlaneGFF P hC hcirc) :
    IsProbabilityMeasure (canonicalLaw hC P) :=
  (Measure.isProbabilityMeasure_map_iff (measurable_canonical hh).aemeasurable).2 inferInstance

/-- The canonical dilation satisfies the finite-dimensional factorization (`tendsto_integral_dilate_factor`). -/
theorem cylinderFactorization_canonical [IsProbabilityMeasure P] (hh : IsWholePlaneGFF P hC hcirc) :
    cylinderFactorization (canonicalLaw hC P) (fun (i : CanonIdx) (L : CanonIdx → ℝ) => L i) dilOp := by
  intro m k a b f g
  have hmeas : Measurable (fun ω (i : CanonIdx) => hC ω i.1) := measurable_canonical hh
  have h1 : ∀ n : ℕ, ∫ L, f (fun i => L (a i)) * g (fun j => (dilOp^[n] L) (b j)) ∂(canonicalLaw hC P) =
      ∫ ω, f (fun i => hC ω (a i).1) * g (fun j => hC ω (dilateTest n (b j).1)) ∂P := by
    intro n
    unfold canonicalLaw
    have hF : Measurable (fun L : CanonIdx → ℝ => f (fun i => L (a i)) * g (fun j => (dilOp^[n] L) (b j))) :=
      (f.continuous.measurable.comp (measurable_pi_iff.2 fun i => measurable_pi_apply (a i))).mul
        (g.continuous.measurable.comp (measurable_pi_iff.2 fun j =>
          (measurable_pi_apply (b j)).comp (measurable_dilOp.iterate n)))
    rw [integral_map hmeas.aemeasurable hF.aestronglyMeasurable]
    congr 1
    funext ω
    simp only [iterate_dilOp]
  have h2a : ∫ L, f (fun i => L (a i)) ∂(canonicalLaw hC P) = ∫ ω, f (fun i => hC ω (a i).1) ∂P := by
    unfold canonicalLaw
    have hF : Measurable (fun L : CanonIdx → ℝ => f (fun i => L (a i))) :=
      f.continuous.measurable.comp (measurable_pi_iff.2 fun i => measurable_pi_apply (a i))
    rw [integral_map hmeas.aemeasurable hF.aestronglyMeasurable]
  have h2b : ∫ L, g (fun j => L (b j)) ∂(canonicalLaw hC P) = ∫ ω, g (fun j => hC ω (b j).1) ∂P := by
    unfold canonicalLaw
    have hG : Measurable (fun L : CanonIdx → ℝ => g (fun j => L (b j))) :=
      g.continuous.measurable.comp (measurable_pi_iff.2 fun j => measurable_pi_apply (b j))
    rw [integral_map hmeas.aemeasurable hG.aestronglyMeasurable]
  have key := tendsto_integral_dilate_factor hh (fun i => (a i).2.1) (fun j => (b j).2.1)
    (fun j => (b j).2.2) f g
  show Tendsto (fun n : ℕ => ∫ L, f (fun i => L (a i)) * g (fun j => (dilOp^[n] L) (b j)) ∂(canonicalLaw hC P))
    atTop (𝓝 ((∫ L, f (fun i => L (a i)) ∂(canonicalLaw hC P)) * ∫ L, g (fun j => L (b j)) ∂(canonicalLaw hC P)))
  rw [h2a, h2b]
  exact Tendsto.congr (fun n => (h1 n).symm) key

/-- Coordinate-sigma mixing of the canonical dilation (`cylinderMixingExtensionStatement_holds`). -/
theorem coordinateSigmaMixing_canonical [IsProbabilityMeasure P] (hh : IsWholePlaneGFF P hC hcirc) :
    coordinateSigmaMixing (canonicalLaw hC P) (fun (i : CanonIdx) (L : CanonIdx → ℝ) => L i) dilOp := by
  have := isProbabilityMeasure_canonicalLaw hh
  exact cylinderMixingExtensionStatement_holds (canonicalLaw hC P)
    (fun (i : CanonIdx) (L : CanonIdx → ℝ) => L i) dilOp (fun i => measurable_pi_apply i)
    (measurePreserving_dilOp hh) (cylinderFactorization_canonical hh)

/-- The canonical dilation is ergodic (paper `lem:mixing`, the 0-1 law for invariant events). -/
theorem ergodic_dilOp [IsProbabilityMeasure P] (hh : IsWholePlaneGFF P hC hcirc) :
    Ergodic (dilOp : ModConstTestPairings (univ : Set ℂ) → ModConstTestPairings (univ : Set ℂ))
      (canonicalLaw hC P) := by
  refine ⟨measurePreserving_dilOp hh, ⟨fun s hs hinv => ?_⟩⟩
  have hiter : ∀ n : ℕ, (dilOp^[n]) ⁻¹' s = s := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ, Set.preimage_comp, ih, hinv]
  have hsA : MeasurableSet[coordinateSigma (fun (i : CanonIdx) (L : CanonIdx → ℝ) => L i)] s := by
    rw [coordinateSigma_eq_comap]
    exact ⟨s, hs, rfl⟩
  have h := coordinateSigmaMixing_canonical hh s s hsA hsA
  simp only [hiter, Set.inter_self] at h
  have hx := tendsto_nhds_unique tendsto_const_nhds h
  have := isProbabilityMeasure_canonicalLaw hh
  have hmul : ((canonicalLaw hC P) s).toReal * (((canonicalLaw hC P) s).toReal - 1) = 0 := by
    linear_combination -hx
  rw [eventuallyEmptyOrUniv_iff']
  rcases mul_eq_zero.1 hmul with h0 | h1
  · left
    rw [ae_eq_empty]
    exact ((ENNReal.toReal_eq_zero_iff _).1 h0).resolve_right (measure_ne_top _ _)
  · right
    rw [ae_eq_univ]
    have h1' : (canonicalLaw hC P) s = 1 := (ENNReal.toReal_eq_one_iff _).1 (by linarith)
    exact (prob_compl_eq_zero_iff hs).2 h1'

end HarmonicBalls
