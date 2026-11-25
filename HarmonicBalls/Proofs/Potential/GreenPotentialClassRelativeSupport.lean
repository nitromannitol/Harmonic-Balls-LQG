import HarmonicBalls.Proofs.Potential.GreenPotentialClassSupport
import HarmonicBalls.Proofs.Sec4.GreenAwayFromPole

/-!
# The test class of Theorem 1.1 with support closed relative to `O`

The enlarged test class of Theorem 1.1 (eq:harmonic-fns, corrected paper lines 136-146) consists of
the Green potentials `∫_O G_O(·, y) ν(dy)` of signed Radon measures `ν` with support in `O \ D`. If
`ν` is read as a signed Radon measure on the open set `O`, then `ν = ν₁ - ν₂` with `ν₁, ν₂` finite on
compact subsets of `O` only, so that their mass may accumulate at `∂O`, and the support is a closed
subset `S = C ∩ O` of `O` (`C` closed in `ℂ`). `relGreenPotentialClass O D` is the class of these
potentials, with the integrals `∫ G_O(x, y) νᵢ(dy)` convergent at every `x ∈ O \ S`, where the
potential is the function `∫_O G_O(·, y) ν(dy)` of the source. It contains `greenPotentialClass O D`
(`greenPotentialClass_subset_relGreenPotentialClass`).

**The two classes define the same harmonic balls** (`isHarmonicBallGen_iff_rel`,
`isHarmonicBallGen_eq_rel`), with no hypothesis on `μ`, `Λ` or `z`; hence Theorem 1.1 reads the same
for the two classes. If `Λ` is a harmonic ball for the compact class and `closure Λ ⊆ O`, then `S` is
the increasing union of the compact sets `K_n = S ∩ {y | (n + 1)⁻¹ ≤ dist(y, Oᶜ)}`
(`exists_compact_exhaustion_inter`), the mean value property holds for the finite measures
`νᵢ|_{K_n}` (`IsHarmonicBallGen.lintegral_greenPotentialENN_compact`), and monotone convergence in
`[0, ∞]` gives `∫_Λ ∫ G_O(x, y) νᵢ(dy) μ(dx) = μ(Λ) ∫ G_O(z, y) νᵢ(dy)`
(`IsHarmonicBallGen.lintegral_greenPotentialENN_relative`), which is finite since `z ∈ O \ S`.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter InnerProductSpace

open scoped ENNReal

/-- The Green potential `x ↦ ∫ G_O(x, y) ν(dy)` with values in `[0, ∞]`. -/
noncomputable def greenPotentialENN (O : Set ℂ) (ν : Measure ℂ) (x : ℂ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (greenFunction O x y) ∂ν

/-- The Green potentials `G_O ν₁ - G_O ν₂` of signed Radon measures `ν₁ - ν₂` on `O` with support in
`O \ D` closed in `O`: `ν₁, ν₂` are finite on compact subsets of `O` and vanish off `C ∩ O` with `C`
closed, and the potentials converge off the support. -/
def relGreenPotentialClass (O D : Set ℂ) : Set (ℂ → ℝ) :=
  {f | ∃ (C : Set ℂ) (ν₁ ν₂ : Measure ℂ), IsClosed C ∧ C ∩ O ⊆ O \ D ∧
    (∀ K, IsCompact K → K ⊆ O → ν₁ K < ⊤ ∧ ν₂ K < ⊤) ∧ ν₁ (C ∩ O)ᶜ = 0 ∧ ν₂ (C ∩ O)ᶜ = 0 ∧
    (∀ x ∈ O \ C, Integrable (greenFunction O x) ν₁ ∧ Integrable (greenFunction O x) ν₂) ∧
    f = greenPotential O ν₁ - greenPotential O ν₂}

/-- The enlarged class of test functions of lines 143-146 with `relGreenPotentialClass`. -/
def relHarmonicBallTestClass (Λ : Set ℂ) : Set (ℂ → ℝ) :=
  {f | ∃ (f₁ f₂ : ℂ → ℝ) (O : Set ℂ), HarmonicOnNhd f₁ (closure Λ) ∧ IsOpen O ∧
    Bornology.IsBounded O ∧ closure Λ ⊆ O ∧ f₂ ∈ relGreenPotentialClass O Λ ∧ f = f₁ + f₂}

/-- `Λ` is a harmonic ball for `μ` centered at `z` with respect to `relHarmonicBallTestClass`. -/
def IsHarmonicBallGenRel (μ : Measure ℂ) (Λ : Set ℂ) (z : ℂ) : Prop :=
  IsHarmonicBall μ Λ z ∧ ∀ f ∈ relHarmonicBallTestClass Λ, HasMeanValueProperty μ Λ z f

theorem HasMeanValueProperty.add {μ : Measure ℂ} {Λ : Set ℂ} {z : ℂ} {f g : ℂ → ℝ}
    (hf : HasMeanValueProperty μ Λ z f) (hg : HasMeanValueProperty μ Λ z g) :
    HasMeanValueProperty μ Λ z (f + g) := by
  refine ⟨hf.1.add hg.1, ?_⟩
  simp only [Pi.add_apply]
  rw [integral_add hf.1 hg.1, ← hf.2, ← hg.2, add_mul]

theorem HasMeanValueProperty.sub {μ : Measure ℂ} {Λ : Set ℂ} {z : ℂ} {f g : ℂ → ℝ}
    (hf : HasMeanValueProperty μ Λ z f) (hg : HasMeanValueProperty μ Λ z g) :
    HasMeanValueProperty μ Λ z (f - g) := by
  refine ⟨hf.1.sub hg.1, ?_⟩
  simp only [Pi.sub_apply]
  rw [integral_sub hf.1 hg.1, ← hf.2, ← hg.2, sub_mul]

/-- The Green potential is the real part of its `[0, ∞]`-valued version. -/
theorem greenPotential_eq_toReal_greenPotentialENN {O : Set ℂ} (hO : IsOpen O)
    (hOb : Bornology.IsBounded O) (ν : Measure ℂ) (x : ℂ) :
    greenPotential O ν x = (greenPotentialENN O ν x).toReal :=
  integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (greenFunction_nonneg hOb x))
    (measurable_greenFunction hO x).aestronglyMeasurable

/-- `G_O(x, ·)` is integrable for a finite measure concentrated on a compact `K ⊆ O` with `x ∉ K`. -/
theorem integrable_greenFunction_of_compact {O K : Set ℂ} (hO : IsOpen O) {ν : Measure ℂ}
    [IsFiniteMeasure ν] (hK : IsCompact K) (hKO : K ⊆ O) (hν : ν Kᶜ = 0) {x : ℂ} (hx : x ∉ K) :
    Integrable (greenFunction O x) ν := by
  by_cases hxO : x ∈ O
  · obtain ⟨C, hC⟩ := exists_bound_greenFunction hxO hK hKO hx
    refine Integrable.of_bound (measurable_greenFunction hO x).aestronglyMeasurable C ?_
    have hae : ∀ᵐ y ∂ν, y ∈ K := measure_mono_null (fun y hy => hy) hν
    filter_upwards [hae] with y hy
    rw [Real.norm_eq_abs]
    exact hC y hy
  · have h0 : greenFunction O x = fun _ => 0 := funext (greenFunction_of_notMem_left hxO)
    rw [h0]
    exact integrable_zero _ _ _

/-- The compact class is contained in the class with relatively closed support. -/
theorem greenPotentialClass_subset_relGreenPotentialClass {O D : Set ℂ} (hO : IsOpen O) :
    greenPotentialClass O D ⊆ relGreenPotentialClass O D := by
  rintro f ⟨K, ν₁, ν₂, hK, hKO, h₁, h₂, hν₁, hν₂, rfl⟩
  have hKO' : K ⊆ O := hKO.trans sdiff_subset
  have hKeq : K ∩ O = K := inter_eq_left.2 hKO'
  refine ⟨K, ν₁, ν₂, hK.isClosed, by rw [hKeq]; exact hKO,
    fun _ _ _ => ⟨measure_lt_top _ _, measure_lt_top _ _⟩, by rw [hKeq]; exact hν₁,
    by rw [hKeq]; exact hν₂, fun x hx => ⟨?_, ?_⟩, rfl⟩
  · exact integrable_greenFunction_of_compact hO hK hKO' hν₁ hx.2
  · exact integrable_greenFunction_of_compact hO hK hKO' hν₂ hx.2

theorem harmonicBallTestClass_subset_relHarmonicBallTestClass (Λ : Set ℂ) :
    harmonicBallTestClass Λ ⊆ relHarmonicBallTestClass Λ := by
  rintro f ⟨f₁, f₂, O, hf₁, hO, hOb, hΛO, hf₂, rfl⟩
  exact ⟨f₁, f₂, O, hf₁, hO, hOb, hΛO, greenPotentialClass_subset_relGreenPotentialClass hO hf₂, rfl⟩

/-- A closed subset `C ∩ O` of a bounded open set `O` is an increasing union of compact sets. -/
theorem exists_compact_exhaustion_inter {O C : Set ℂ} (hO : IsOpen O) (hOb : Bornology.IsBounded O)
    (hC : IsClosed C) : ∃ K : ℕ → Set ℂ, (∀ n, IsCompact (K n)) ∧ (∀ n, K n ⊆ C ∩ O) ∧
      Monotone K ∧ ⋃ n, K n = C ∩ O := by
  have hne : (Oᶜ).Nonempty := by
    rw [nonempty_compl]
    rintro rfl
    exact NormedSpace.unbounded_univ ℝ ℂ hOb
  have hsub : ∀ n : ℕ, {y | ((n : ℝ) + 1)⁻¹ ≤ infDist y Oᶜ} ⊆ O := by
    intro n y hy
    by_contra hyO
    have h0 := infDist_zero_of_mem (show y ∈ Oᶜ from hyO)
    have hpos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
    simp only [mem_ofPred_eq] at hy
    linarith
  refine ⟨fun n => C ∩ {y | ((n : ℝ) + 1)⁻¹ ≤ infDist y Oᶜ}, fun n => ?_,
    fun n => inter_subset_inter_right C (hsub n), fun m n hmn => ?_, ?_⟩
  · exact Metric.isCompact_of_isClosed_isBounded
      (hC.inter (isClosed_le continuous_const (continuous_infDist_pt _)))
      (hOb.subset (inter_subset_right.trans (hsub n)))
  · rintro y ⟨hyC, hy⟩
    refine ⟨hyC, ?_⟩
    simp only [mem_ofPred_eq] at hy ⊢
    refine le_trans ?_ hy
    gcongr
  · refine Subset.antisymm (iUnion_subset fun n => inter_subset_inter_right C (hsub n)) ?_
    rintro y ⟨hyC, hyO⟩
    have hpos : 0 < infDist y Oᶜ := by
      refine (infDist_pos_iff_notMem_closure hne).1 ?_
      rw [hO.isClosed_compl.closure_eq]
      exact not_not.2 hyO
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
    refine mem_iUnion.2 ⟨n, hyC, ?_⟩
    rw [one_div] at hn
    exact hn.le

/-- **The mean value property for a finite piece**, in `[0, ∞]`: for a harmonic ball `Λ` of
Theorem 1.1, a finite measure `ν` concentrated on a compact `K ⊆ O \ Λ` and `closure Λ ⊆ O`,
`∫_Λ G_O ν dμ = μ(Λ) G_O ν(z)`. -/
theorem IsHarmonicBallGen.lintegral_greenPotentialENN_compact {μ : Measure ℂ} {Λ : Set ℂ} {z : ℂ}
    (h : IsHarmonicBallGen μ Λ z) {O K : Set ℂ} (hO : IsOpen O) (hOb : Bornology.IsBounded O)
    (hΛO : closure Λ ⊆ O) (hK : IsCompact K) (hKO : K ⊆ O \ Λ) {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hν : ν Kᶜ = 0) :
    AEMeasurable (greenPotentialENN O ν) (μ.restrict Λ) ∧
      ∫⁻ x in Λ, greenPotentialENN O ν x ∂μ = greenPotentialENN O ν z * μ Λ := by
  have hΛ : IsOpen Λ := h.1.1
  have hzΛ : z ∈ Λ := h.1.2.1
  have hμΛ : μ Λ ≠ ⊤ := h.1.2.2.2.1.ne
  have hfin : ∀ x ∈ Λ, greenPotentialENN O ν x ≠ ⊤ := fun x hx =>
    (integrable_greenFunction_of_compact hO hK (hKO.trans sdiff_subset) hν
      (fun hxK => (hKO hxK).2 hx)).lintegral_lt_top.ne
  have hmem : greenPotential O ν ∈ harmonicBallTestClass Λ := by
    refine ⟨0, greenPotential O ν, O, harmonicOnNhd_const 0, hO, hOb, hΛO,
      ⟨K, ν, 0, hK, hKO, inferInstance, inferInstance, hν, by simp, ?_⟩,
      (zero_add _).symm⟩
    funext x
    simp [greenPotential]
  obtain ⟨hint, hmv⟩ := h.2 _ hmem
  have hpot : greenPotential O ν = fun x => (greenPotentialENN O ν x).toReal :=
    funext (greenPotential_eq_toReal_greenPotentialENN hO hOb ν)
  simp only [hpot] at hint hmv
  have hae : ∀ᵐ x ∂μ.restrict Λ, ENNReal.ofReal (greenPotentialENN O ν x).toReal =
      greenPotentialENN O ν x :=
    ae_restrict_of_forall_mem hΛ.measurableSet fun x hx => ENNReal.ofReal_toReal (hfin x hx)
  have hgm : AEMeasurable (greenPotentialENN O ν) (μ.restrict Λ) :=
    (ENNReal.measurable_ofReal.comp_aemeasurable hint.aestronglyMeasurable.aemeasurable).congr hae
  refine ⟨hgm, ?_⟩
  have hlt : ∫⁻ x in Λ, greenPotentialENN O ν x ∂μ ≠ ⊤ := by
    rw [← lintegral_congr_ae hae]
    exact hint.lintegral_lt_top.ne
  rw [integral_toReal hgm (ae_restrict_of_forall_mem hΛ.measurableSet fun x hx => (hfin x hx).lt_top),
    measureReal_def, ← ENNReal.toReal_mul] at hmv
  exact (ENNReal.toReal_eq_toReal_iff' hlt (ENNReal.mul_ne_top (hfin z hzΛ) hμΛ)).1 hmv.symm

/-- **The mean value property for a Radon measure on `O`**, in `[0, ∞]`: for a harmonic ball `Λ` of
Theorem 1.1, `closure Λ ⊆ O` and a measure `ν` finite on compact subsets of `O` and vanishing off
`C ∩ O ⊆ O \ Λ` with `C` closed, `∫_Λ G_O ν dμ = μ(Λ) G_O ν(z)`. -/
theorem IsHarmonicBallGen.lintegral_greenPotentialENN_relative {μ : Measure ℂ} {Λ : Set ℂ} {z : ℂ}
    (h : IsHarmonicBallGen μ Λ z) {O C : Set ℂ} (hO : IsOpen O) (hOb : Bornology.IsBounded O)
    (hΛO : closure Λ ⊆ O) (hC : IsClosed C) (hCO : C ∩ O ⊆ O \ Λ) {ν : Measure ℂ}
    (hloc : ∀ K, IsCompact K → K ⊆ O → ν K < ⊤) (hν : ν (C ∩ O)ᶜ = 0) :
    AEMeasurable (greenPotentialENN O ν) (μ.restrict Λ) ∧
      ∫⁻ x in Λ, greenPotentialENN O ν x ∂μ = greenPotentialENN O ν z * μ Λ := by
  obtain ⟨K, hK, hKS, hKmono, hKU⟩ := exists_compact_exhaustion_inter hO hOb hC
  have hpiece : ∀ n, AEMeasurable (greenPotentialENN O (ν.restrict (K n))) (μ.restrict Λ) ∧
      ∫⁻ x in Λ, greenPotentialENN O (ν.restrict (K n)) x ∂μ =
        greenPotentialENN O (ν.restrict (K n)) z * μ Λ := by
    intro n
    have : IsFiniteMeasure (ν.restrict (K n)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hloc _ (hK n) ((hKS n).trans inter_subset_right)⟩
    refine h.lintegral_greenPotentialENN_compact hO hOb hΛO (hK n) ((hKS n).trans hCO) ?_
    rw [Measure.restrict_apply (hK n).isClosed.measurableSet.compl, compl_inter_self, measure_empty]
  have hae : ∀ᵐ y ∂ν, y ∈ C ∩ O := measure_mono_null (fun y hy => hy) hν
  have hsup : ∀ x, greenPotentialENN O ν x = ⨆ n, greenPotentialENN O (ν.restrict (K n)) x := by
    intro x
    simp only [greenPotentialENN]
    rw [← setLIntegral_iUnion_of_directed _ hKmono.directed_le, hKU,
      Measure.restrict_eq_self_of_ae_mem hae]
  have hmono : ∀ x, Monotone fun n => greenPotentialENN O (ν.restrict (K n)) x :=
    fun x _ _ hmn => lintegral_mono' (Measure.restrict_mono (hKmono hmn) le_rfl) le_rfl
  have hfun : greenPotentialENN O ν = fun x => ⨆ n, greenPotentialENN O (ν.restrict (K n)) x :=
    funext hsup
  refine ⟨hfun ▸ AEMeasurable.iSup fun n => (hpiece n).1, ?_⟩
  rw [hfun, lintegral_iSup' (fun n => (hpiece n).1) (Eventually.of_forall hmono), ENNReal.iSup_mul]
  exact iSup_congr fun n => (hpiece n).2

/-- **The mean value property for the Green potential of a signed Radon measure on `O`** whose
potentials converge at the centre. -/
theorem IsHarmonicBallGen.hasMeanValueProperty_relative {μ : Measure ℂ} {Λ : Set ℂ} {z : ℂ}
    (h : IsHarmonicBallGen μ Λ z) {O C : Set ℂ} (hO : IsOpen O) (hOb : Bornology.IsBounded O)
    (hΛO : closure Λ ⊆ O) (hC : IsClosed C) (hCO : C ∩ O ⊆ O \ Λ) {ν₁ ν₂ : Measure ℂ}
    (hloc₁ : ∀ K, IsCompact K → K ⊆ O → ν₁ K < ⊤) (hloc₂ : ∀ K, IsCompact K → K ⊆ O → ν₂ K < ⊤)
    (hν₁ : ν₁ (C ∩ O)ᶜ = 0) (hν₂ : ν₂ (C ∩ O)ᶜ = 0) (hz₁ : greenPotentialENN O ν₁ z ≠ ⊤)
    (hz₂ : greenPotentialENN O ν₂ z ≠ ⊤) :
    HasMeanValueProperty μ Λ z (greenPotential O ν₁ - greenPotential O ν₂) := by
  have key : ∀ ν : Measure ℂ, (∀ K, IsCompact K → K ⊆ O → ν K < ⊤) → ν (C ∩ O)ᶜ = 0 →
      greenPotentialENN O ν z ≠ ⊤ → HasMeanValueProperty μ Λ z (greenPotential O ν) := by
    intro ν hloc hν hz
    obtain ⟨hm, heq⟩ := h.lintegral_greenPotentialENN_relative hO hOb hΛO hC hCO hloc hν
    have hpot : greenPotential O ν = fun x => (greenPotentialENN O ν x).toReal :=
      funext (greenPotential_eq_toReal_greenPotentialENN hO hOb ν)
    have hne : ∫⁻ x in Λ, greenPotentialENN O ν x ∂μ ≠ ⊤ := by
      rw [heq]
      exact ENNReal.mul_ne_top hz h.1.2.2.2.1.ne
    rw [hpot]
    refine ⟨integrable_toReal_of_lintegral_ne_top hm hne, ?_⟩
    show (greenPotentialENN O ν z).toReal * μ.real Λ = ∫ x in Λ, (greenPotentialENN O ν x).toReal ∂μ
    rw [integral_toReal hm (ae_lt_top' hm hne), heq, ENNReal.toReal_mul, measureReal_def]
  exact (key ν₁ hloc₁ hν₁ hz₁).sub (key ν₂ hloc₂ hν₂ hz₂)

/-- **Theorem 1.1: harmonic balls for the test class with support closed relative to `O`** are the
harmonic balls for the formal test class. -/
theorem isHarmonicBallGen_iff_rel {μ : Measure ℂ} {Λ : Set ℂ} {z : ℂ} :
    IsHarmonicBallGen μ Λ z ↔ IsHarmonicBallGenRel μ Λ z := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    rintro f ⟨f₁, f₂, O, hf₁, hO, hOb, hΛO, ⟨C, ν₁, ν₂, hC, hCO, hloc, hν₁, hν₂, hint, rfl⟩, rfl⟩
    have hzO : z ∈ O := hΛO (subset_closure h.1.2.1)
    have hzC : z ∈ O \ C := ⟨hzO, fun hz => (hCO ⟨hz, hzO⟩).2 h.1.2.1⟩
    have h1 : HasMeanValueProperty μ Λ z f₁ :=
      h.2 _ ⟨f₁, 0, O, hf₁, hO, hOb, hΛO, zero_mem_greenPotentialClass _ _, (add_zero f₁).symm⟩
    exact h1.add (h.hasMeanValueProperty_relative hO hOb hΛO hC hCO (fun K hK hKO => (hloc K hK hKO).1)
      (fun K hK hKO => (hloc K hK hKO).2) hν₁ hν₂ (hint z hzC).1.lintegral_lt_top.ne
      (hint z hzC).2.lintegral_lt_top.ne)
  · intro h
    exact ⟨h.1, fun f hf => h.2 f (harmonicBallTestClass_subset_relHarmonicBallTestClass Λ hf)⟩

/-- The notions of harmonic ball of Theorem 1.1 for the two readings of the support are equal. -/
theorem isHarmonicBallGen_eq_rel : IsHarmonicBallGen = IsHarmonicBallGenRel := by
  funext μ Λ z
  exact propext isHarmonicBallGen_iff_rel

end HarmonicBalls
