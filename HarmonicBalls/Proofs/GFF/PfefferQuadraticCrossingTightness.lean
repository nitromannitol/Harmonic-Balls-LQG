import HarmonicBalls.Proofs.GFF.QuadraticShiftAnnulusComparison
import HarmonicBalls.Proofs.Metric.CompactDistanceMeasurable

/-! # Measurability of normalized annular crossings

For a random Euclidean-compatible length metric, pointwise measurability
implies almost-everywhere measurability of normalized crossing distances.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped ENNReal

/-- A normalized crossing distance is a.e. measurable when its normalization
and point evaluations are a.e. measurable and the metric is compatible. -/
theorem aemeasurable_normalized_pfefferAcross
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {D : Ω → ℂ → ℂ → ℝ} {N : Ω → ℝ≥0∞} {z : ℂ} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hpoint : ∀ x y, AEMeasurable (fun ω => D ω x y) P)
    (hN : AEMeasurable N P) :
    AEMeasurable (fun ω => N ω * pfefferAcross (D ω) z a b) P := by
  obtain ⟨u, hu⟩ := exists_dense_seq_of_nonempty (sphere z a)
    (NormedSpace.sphere_nonempty.mpr ha)
  obtain ⟨v, hv⟩ := exists_dense_seq_of_nonempty (sphere z b)
    (NormedSpace.sphere_nonempty.mpr hb)
  exact hN.mul (aemeasurable_pfefferAcross_of_dense_seq z ha hb u v hu hv hD
    (fun n m => hpoint _ _))

/-- Four tight families with a.e. measurable values admit a common event
of arbitrarily high probability at every positive scale. -/
theorem PfefferTightAcrossScales.four_simultaneous
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Fin 4 → ℝ → Ω → ℝ≥0∞}
    (htight : ∀ i, PfefferTightAcrossScales P (X i))
    (hmeas : ∀ i r, 0 < r → AEMeasurable (X i r) P)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ M : Fin 4 → ℝ, (∀ i, 0 < M i) ∧ ∀ r, 0 < r →
      ENNReal.ofReal (1 - ε) ≤ P {ω | ∀ i,
        ENNReal.ofReal (M i)⁻¹ ≤ X i r ω ∧ X i r ω ≤ ENNReal.ofReal (M i)} := by
  classical
  choose M hM hbound using fun i => htight i (ε / 4) (by linarith) (by linarith)
  refine ⟨M, hM, ?_⟩
  intro r hr
  let A : Fin 4 → Set Ω := fun i => {ω |
    ENNReal.ofReal (M i)⁻¹ ≤ X i r ω ∧ X i r ω ≤ ENNReal.ofReal (M i)}
  have hA : ∀ i, NullMeasurableSet (A i) P := by
    intro i
    exact (nullMeasurableSet_le aemeasurable_const (hmeas i r hr)).inter
      (nullMeasurableSet_le (hmeas i r hr) aemeasurable_const)
  have hbad : ∀ i, P (A i)ᶜ ≤ ENNReal.ofReal (ε / 4) := by
    intro i
    have h := hbound i r hr
    change ENNReal.ofReal (1 - ε / 4) ≤ P (A i) at h
    rw [measure_compl₀ (hA i) (measure_ne_top P _), measure_univ]
    calc
      1 - P (A i) ≤ 1 - ENNReal.ofReal (1 - ε / 4) := tsub_le_tsub_left h 1
      _ = ENNReal.ofReal (ε / 4) := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (by linarith : 0 ≤ 1 - ε / 4)]
        congr 1
        ring
  have hbadall : P (⋃ i, (A i)ᶜ) ≤ ENNReal.ofReal ε := by
    calc
      P (⋃ i, (A i)ᶜ) ≤ ∑ i, P (A i)ᶜ := measure_iUnion_fintype_le P _
      _ ≤ ∑ _i : Fin 4, ENNReal.ofReal (ε / 4) := Finset.sum_le_sum fun i _ => hbad i
      _ = ENNReal.ofReal ε := by
        simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
        norm_num1
        rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
        congr 1
        ring
  have hgood : NullMeasurableSet (⋂ i, A i) P := NullMeasurableSet.iInter hA
  have hcomp : (⋂ i, A i)ᶜ = ⋃ i, (A i)ᶜ := compl_iInter A
  have hc := measure_add_measure_compl₀ hgood
  rw [hcomp, measure_univ] at hc
  have hsplit : ENNReal.ofReal (1 - ε) + ENNReal.ofReal ε = 1 := by
    rw [← ENNReal.ofReal_add (by linarith) hε.le]
    norm_num
  have hresult : ENNReal.ofReal (1 - ε) ≤ P (⋂ i, A i) := by
    apply (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp
    calc
      ENNReal.ofReal (1 - ε) + ENNReal.ofReal ε = 1 := hsplit
      _ = P (⋂ i, A i) + P (⋃ i, (A i)ᶜ) := hc.symm
      _ ≤ P (⋂ i, A i) + ENNReal.ofReal ε := add_le_add_right hbadall _
  have heq : (⋂ i, A i) = {ω | ∀ i,
      ENNReal.ofReal (M i)⁻¹ ≤ X i r ω ∧ X i r ω ≤ ENNReal.ofReal (M i)} := by
    ext ω
    simp [A]
  rw [← heq]
  exact hresult

/-- The two nested original crossings and two shifted crossings used in
quadratic Weyl comparisons, with their respective normalizations. -/
noncomputable def quadraticCrossingFamily {Ω : Type*}
    (D E : Ω → ℂ → ℂ → ℝ) (N K : ℝ → Ω → ℝ≥0∞) :
    Fin 4 → ℝ → Ω → ℝ≥0∞ :=
  ![fun r ω => N r ω * pfefferAcross (D ω) 0 ((19 / 10 : ℝ) * r) (2 * r),
    fun r ω => N r ω * pfefferAcross (D ω) 0 (r / 2) ((6 / 5 : ℝ) * r),
    fun r ω => K r ω * pfefferAcross (E ω) 0 r (2 * r),
    fun r ω => K r ω * pfefferAcross (E ω) 0 r ((11 / 10 : ℝ) * r)]

/-- Axiom V for two fields supplies tightness of the four crossings used
in the quadratic comparison. -/
theorem quadraticCrossingFamily_tight_of_pfefferAxiomVScale
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ξ : ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {f g : Ω → ℂ → ℝ} {c d : ℝ → ℝ}
    (hf : PfefferAxiomVScale P ξ 𝔇 hC hcirc f c)
    (hg : PfefferAxiomVScale P ξ 𝔇 hC hcirc g d) :
    ∀ i, PfefferTightAcrossScales P
      (quadraticCrossingFamily (fun ω => 𝔇 (pfefferField hC f ω))
        (fun ω => 𝔇 (pfefferField hC g ω))
        (pfefferNormalization ξ hcirc f c) (pfefferNormalization ξ hcirc g d) i) := by
  intro i
  fin_cases i
  · simpa [quadraticCrossingFamily, mul_comm] using
      (hf.2.1 0 (19 / 10) 2 (by norm_num) (by norm_num)).1
  · simpa [quadraticCrossingFamily, mul_comm, div_eq_mul_inv] using
      (hf.2.1 0 (1 / 2) (6 / 5) (by norm_num) (by norm_num)).1
  · simpa [quadraticCrossingFamily, mul_comm] using
      (hg.2.1 0 1 2 (by norm_num) (by norm_num)).1
  · simpa [quadraticCrossingFamily, mul_comm] using
      (hg.2.1 0 1 (11 / 10) (by norm_num) (by norm_num)).1

/-- The four normalized crossings satisfy their tightness bounds together
with both quadratic Weyl comparisons on an event of arbitrarily high probability at every positive radius. -/
theorem quadraticCrossingFamily_simultaneous
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {D E : Ω → ℂ → ℂ → ℝ} {N K : ℝ → Ω → ℝ≥0∞} {ξ : ℝ}
    (hξ : 0 < ξ)
    (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hE : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (E ω))
    (hpointD : ∀ x y, AEMeasurable (fun ω => D ω x y) P)
    (hpointE : ∀ x y, AEMeasurable (fun ω => E ω x y) P)
    (hN : ∀ r, 0 < r → AEMeasurable (N r) P)
    (hK : ∀ r, 0 < r → AEMeasurable (K r) P)
    (hscale : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (E ω x y) =
      weylScaling (D ω) ξ (fun z => ‖z‖ ^ 2) x y)
    (htight : ∀ i, PfefferTightAcrossScales P (quadraticCrossingFamily D E N K i))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ M : Fin 4 → ℝ, (∀ i, 0 < M i) ∧ ∀ r, 0 < r →
      ENNReal.ofReal (1 - ε) ≤ P {ω |
        (∀ i, ENNReal.ofReal (M i)⁻¹ ≤ quadraticCrossingFamily D E N K i r ω ∧
          quadraticCrossingFamily D E N K i r ω ≤ ENNReal.ofReal (M i)) ∧
        ENNReal.ofReal (Real.exp (ξ * ((19 / 10 : ℝ) * r) ^ 2)) *
          pfefferAcross (D ω) 0 ((19 / 10 : ℝ) * r) (2 * r) ≤
          pfefferAcross (E ω) 0 r (2 * r) ∧
        pfefferAcross (E ω) 0 r ((11 / 10 : ℝ) * r) ≤
          ENNReal.ofReal (Real.exp (ξ * ((11 / 10 : ℝ) * r) ^ 2)) *
            pfefferAcross (D ω) 0 (r / 2) ((6 / 5 : ℝ) * r)} := by
  have hm : ∀ i r, 0 < r →
      AEMeasurable (quadraticCrossingFamily D E N K i r) P := by
    intro i r hr
    fin_cases i <;> simp [quadraticCrossingFamily] <;>
      apply aemeasurable_normalized_pfefferAcross <;>
      first | positivity | exact hD | exact hE | exact hpointD | exact hpointE |
        exact hN r hr | exact hK r hr
  obtain ⟨M, hM, hMbound⟩ := PfefferTightAcrossScales.four_simultaneous htight hm hε hε1
  refine ⟨M, hM, fun r hr => ?_⟩
  have hevent : ∀ᵐ ω ∂P,
      ENNReal.ofReal (Real.exp (ξ * ((19 / 10 : ℝ) * r) ^ 2)) *
        pfefferAcross (D ω) 0 ((19 / 10 : ℝ) * r) (2 * r) ≤
        pfefferAcross (E ω) 0 r (2 * r) ∧
      pfefferAcross (E ω) 0 r ((11 / 10 : ℝ) * r) ≤
        ENNReal.ofReal (Real.exp (ξ * ((11 / 10 : ℝ) * r) ^ 2)) *
          pfefferAcross (D ω) 0 (r / 2) ((6 / 5 : ℝ) * r) := by
    filter_upwards [hD, hscale] with ω hd hs
    exact ⟨pfefferAcross_quadratic_weyl_lower hd hξ hr hs,
      pfefferAcross_quadratic_weyl_upper hd hξ hr hs⟩
  have heq : P {ω |
      (∀ i, ENNReal.ofReal (M i)⁻¹ ≤ quadraticCrossingFamily D E N K i r ω ∧
        quadraticCrossingFamily D E N K i r ω ≤ ENNReal.ofReal (M i)) ∧
      ENNReal.ofReal (Real.exp (ξ * ((19 / 10 : ℝ) * r) ^ 2)) *
        pfefferAcross (D ω) 0 ((19 / 10 : ℝ) * r) (2 * r) ≤
        pfefferAcross (E ω) 0 r (2 * r) ∧
      pfefferAcross (E ω) 0 r ((11 / 10 : ℝ) * r) ≤
        ENNReal.ofReal (Real.exp (ξ * ((11 / 10 : ℝ) * r) ^ 2)) *
          pfefferAcross (D ω) 0 (r / 2) ((6 / 5 : ℝ) * r)} =
      P {ω | ∀ i, ENNReal.ofReal (M i)⁻¹ ≤ quadraticCrossingFamily D E N K i r ω ∧
        quadraticCrossingFamily D E N K i r ω ≤ ENNReal.ofReal (M i)} := by
    exact measure_congr (hevent.mono fun ω hω => by simp [hω])
  rw [heq]
  exact hMbound r hr

end HarmonicBalls
