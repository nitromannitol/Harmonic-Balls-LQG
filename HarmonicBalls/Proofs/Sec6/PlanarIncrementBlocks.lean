import HarmonicBalls.Proofs.Sec6.BrownianIncrementBlocks
import Mathlib.Probability.Independence.InfinitePi

/-! # Planar Brownian increment blocks -/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory MarkovProcess Filter
open scoped NNReal

/-- Independent families on independent probability spaces remain independent
when paired coordinatewise. -/
theorem iIndepFun_pair_prod
    {ι Ω₁ Ω₂ A B : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure Ω₁} {ν : Measure Ω₂} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : ι → Ω₁ → A} {g : ι → Ω₂ → B}
    (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i))
    (hfi : iIndepFun f μ) (hgi : iIndepFun g ν) :
    iIndepFun (fun i p => (f i p.1, g i p.2)) (μ.prod ν) := by
  classical
  rw [iIndepFun_iff_finset]
  intro s
  let F : Ω₁ → s → A := fun ω i => f i ω
  let G : Ω₂ → s → B := fun ω i => g i ω
  have hF : Measurable F := Measurable.of_eval fun i => hf i
  have hG : Measurable G := Measurable.of_eval fun i => hg i
  let u : s → Measure A := fun i => μ.map (f i)
  let v : s → Measure B := fun i => ν.map (g i)
  have hu : μ.map F = Measure.pi u := by
    exact (hfi.restrict s).map_fun_eq_pi_map (fun i => (hf i).aemeasurable)
  have hv : ν.map G = Measure.pi v := by
    exact (hgi.restrict s).map_fun_eq_pi_map (fun i => (hg i).aemeasurable)
  have hzip := (measurePreserving_arrowProdEquivProdArrow A B s u v).symm.map_eq
  have hpair : (μ.prod ν).map (fun p (i : s) => (f i p.1, g i p.2)) =
      Measure.pi (fun i : s => (μ.map (f i)).prod (ν.map (g i))) := by
    rw [← hzip, ← hu, ← hv, Measure.map_prod_map μ ν hF hG,
      Measure.map_map (MeasurableEquiv.arrowProdEquivProdArrow A B s).symm.measurable
        (hF.prodMap hG)]
    rfl
  apply (iIndepFun_iff_map_fun_eq_pi_map ?_).2
  · convert hpair using 1
    congr 1
    congr 1
    funext i
    symm
    exact Measure.map_prod_map μ ν (hf i) (hg i)
  · intro i
    exact ((hf i).comp measurable_fst |>.prodMk ((hg i).comp measurable_snd)).aemeasurable

/-- Independence descends through a measurable pushforward. -/
theorem iIndepFun_map_of_comp
    {ι Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {A : ι → Type*} [∀ i, MeasurableSpace (A i)] {μ : Measure Ω}
    (h : Ω → Ω') (hh : Measurable h) (f : (i : ι) → Ω' → A i)
    (hf : ∀ i, Measurable (f i))
    (hi : iIndepFun (fun i => f i ∘ h) μ) :
    iIndepFun f (μ.map h) := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at hi ⊢
  intro S sets hs
  have hsets : MeasurableSet (⋂ i ∈ S, f i ⁻¹' sets i) := by
    exact MeasurableSet.biInter S.finite_toSet.countable fun i hi =>
      (hf i) (hs i hi)
  rw [Measure.map_apply hh hsets]
  have hprod : ∀ i ∈ S, (μ.map h) (f i ⁻¹' sets i) = μ ((f i ∘ h) ⁻¹' sets i) := by
    intro i hi
    rw [Measure.map_apply hh ((hf i) (hs i hi))]
    rfl
  simp_rw [Finset.prod_congr rfl hprod]
  simpa only [Set.preimage_iInter, Set.preimage_comp] using hi S hs

/-- Planar Brownian increment processes on disjoint time intervals are
independent. -/
theorem iIndepFun_planarBrownian_increment_blocks
    {ι S : Type*} (x : ℂ) (a b : ι → S → NNReal)
    (hab : ∀ i s, a i s ≤ b i s)
    (hdisjoint : ∀ i j, i ≠ j → ∀ s t,
      b i s ≤ a j t ∨ b j t ≤ a i s) :
    iIndepFun (fun i (ω : ContinuousPath ℂ) s => ω (b i s) - ω (a i s))
      (planarBrownianMotion x) := by
  let f : ι → ContinuousPath ℝ → S → ℝ := fun i ω s => ω (b i s) - ω (a i s)
  have hf : ∀ i, Measurable (f i) := by
    intro i
    exact Measurable.of_eval fun s =>
      (ContinuousPath.measurable_coordinateProcess _).sub
        (ContinuousPath.measurable_coordinateProcess _)
  have hi := iIndepFun_pair_prod (μ := brownianMotion x.re) (ν := brownianMotion x.im)
    hf hf (iIndepFun_realBrownian_increment_blocks x.re a b hab hdisjoint)
      (iIndepFun_realBrownian_increment_blocks x.im a b hab hdisjoint)
  have hcombine : Measurable (fun p : (S → ℝ) × (S → ℝ) =>
      fun s => (p.1 s : ℂ) + (p.2 s : ℂ) * Complex.I) := by
    apply Measurable.of_eval
    intro s
    fun_prop
  have hc := hi.comp (fun _ p s => (p.1 s : ℂ) + (p.2 s : ℂ) * Complex.I)
    (fun _ => hcombine)
  rw [planarBrownianMotion_apply]
  apply iIndepFun_map_of_comp complexPathOfReIm measurable_complexPathOfReIm
    (fun i ω s => ω (b i s) - ω (a i s))
  · intro i
    exact Measurable.of_eval fun s =>
      (ContinuousPath.measurable_coordinateProcess _).sub
        (ContinuousPath.measurable_coordinateProcess _)
  · convert hc using 1
    funext i p s
    simp only [Function.comp_apply, complexPathOfReIm_apply, f, Complex.ofReal_sub]
    ring

/-- The tail sigma-algebra of disjoint planar Brownian increment blocks is
independent of itself. -/
theorem planarBrownian_increment_block_tail_indep_self
    {S : Type*} (x : ℂ) (a b : ℕ → S → NNReal)
    (hab : ∀ i s, a i s ≤ b i s)
    (hdisjoint : ∀ i j, i ≠ j → ∀ s t,
      b i s ≤ a j t ∨ b j t ≤ a i s) :
    let m : ℕ → MeasurableSpace (ContinuousPath ℂ) := fun i =>
      (inferInstance : MeasurableSpace (S → ℂ)).comap
        (fun ω s => ω (b i s) - ω (a i s))
    Indep (limsup m atTop) (limsup m atTop) (planarBrownianMotion x) := by
  dsimp only
  apply indep_limsup_atTop_self
  · intro i
    apply Measurable.comap_le
    exact Measurable.of_eval fun s =>
      (ContinuousPath.measurable_coordinateProcess _).sub
        (ContinuousPath.measurable_coordinateProcess _)
  · exact (iIndepFun_iff_iIndep _ _ _).mp
      (iIndepFun_planarBrownian_increment_blocks x a b hab hdisjoint)

/-- A sigma-algebra has the zero-one property if it becomes a sub-sigma-algebra
of a self-independent sigma-algebra after an almost-sure identity map. -/
theorem indep_self_of_ae_identity_comap_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m n : MeasurableSpace Ω} (h : Ω → Ω) (hae : h =ᵐ[μ] id)
    (hle : m.comap h ≤ n) (hn : Indep n n μ) : Indep m m μ := by
  rw [Indep_iff] at hn ⊢
  intro A B hA hB
  have hA' : MeasurableSet[n] (h ⁻¹' A) := hle _ ⟨A, hA, rfl⟩
  have hB' : MeasurableSet[n] (h ⁻¹' B) := hle _ ⟨B, hB, rfl⟩
  have hAc : μ A = μ (h ⁻¹' A) := measure_congr (by
    filter_upwards [hae] with ω hω
    simp only [Set.mem_preimage, hω, id_eq])
  have hBc : μ B = μ (h ⁻¹' B) := measure_congr (by
    filter_upwards [hae] with ω hω
    simp only [Set.mem_preimage, hω, id_eq])
  have hAB : μ (A ∩ B) = μ (h ⁻¹' A ∩ h ⁻¹' B) := measure_congr (by
    filter_upwards [hae] with ω hω
    simp only [Set.mem_inter_iff, Set.mem_preimage, hω, id_eq])
  rw [hAB, hAc, hBc]
  exact hn _ _ hA' hB'

/-- Reset the initial value of a planar path to `x` while preserving all its
increments. -/
noncomputable def resetPlanarPathInitialValue (x : ℂ) (ω : ContinuousPath ℂ) :
    ContinuousPath ℂ :=
  ⟨fun t => ω t - ω 0 + x, by fun_prop⟩

/-- Resetting the initial value is almost surely the identity under planar
Brownian motion started at `x`. -/
theorem ae_resetPlanarPathInitialValue (x : ℂ) :
    resetPlanarPathInitialValue x =ᵐ[planarBrownianMotion x] id := by
  filter_upwards [ae_planarBrownianMotion_eval_zero x] with ω hω
  ext t
  simp [resetPlanarPathInitialValue, hω]

/-- If the recentered germ is contained in a disjoint-block tail, the planar
Brownian germ is independent of itself. -/
theorem planarBrownian_germ_indep_of_recentered_tail
    {S : Type*} (x : ℂ) (a b : ℕ → S → NNReal)
    (hab : ∀ i s, a i s ≤ b i s)
    (hdisjoint : ∀ i j, i ≠ j → ∀ s t,
      b i s ≤ a j t ∨ b j t ≤ a i s)
    (htail : (⨅ (t : NNReal) (_ : 0 < t),
        ContinuousPath.canonicalFiltration (alpha := ℂ) t).comap
          (resetPlanarPathInitialValue x) ≤
      limsup (fun i : ℕ => (inferInstance : MeasurableSpace (S → ℂ)).comap
        (fun ω : ContinuousPath ℂ => fun s => ω (b i s) - ω (a i s))) atTop) :
    Indep
      (⨅ (t : NNReal) (_ : 0 < t), ContinuousPath.canonicalFiltration (alpha := ℂ) t)
      (⨅ (t : NNReal) (_ : 0 < t), ContinuousPath.canonicalFiltration (alpha := ℂ) t)
      (planarBrownianMotion x) :=
  indep_self_of_ae_identity_comap_le (resetPlanarPathInitialValue x)
    (ae_resetPlanarPathInitialValue x) htail
    (planarBrownian_increment_block_tail_indep_self x a b hab hdisjoint)

end HarmonicBalls.Section6
