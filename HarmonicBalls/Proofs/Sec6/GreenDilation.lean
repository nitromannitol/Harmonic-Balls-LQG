import HarmonicBalls.Proofs.Sec6.GreenTranslation

/-! # Dilation of planar Green functions -/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter Topology InnerProductSpace Laplacian

/-- The planar Laplacian scales quadratically under a nonzero real dilation. -/
theorem laplacian_comp_real_dilation (f : ℂ → ℝ) {k : ℝ} (hk : k ≠ 0) (x : ℂ) :
    Δ (fun z => f (k • z)) x = k ^ 2 * Δ f (k • x) := by
  let L : ℂ ≃L[ℝ] ℂ := ContinuousLinearEquiv.smulLeft (Units.mk0 k hk)
  have hderiv : iteratedFDeriv ℝ 2 (fun z => f (k • z)) x =
      (iteratedFDeriv ℝ 2 f (k • x)).compContinuousLinearMap
        (fun _ => (L : ℂ →L[ℝ] ℂ)) := by
    simpa [L, Function.comp_def, iteratedFDerivWithin_univ] using
      L.iteratedFDerivWithin_comp_right f (s := Set.univ) uniqueDiffOn_univ
        (x := x) (by simp) 2
  rw [laplacian_eq_iteratedFDeriv_complexPlane, laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [hderiv, ContinuousMultilinearMap.compContinuousLinearMap_apply, L,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.smulLeft_apply_apply, Units.smul_def, Units.val_mk0]
  have hscale (v : Fin 2 → ℂ) :
      (iteratedFDeriv ℝ 2 f (k • x)) (fun i => k • v i) =
        k ^ 2 * (iteratedFDeriv ℝ 2 f (k • x)) v := by
    simpa [Finset.prod_const, Fintype.card_fin, smul_eq_mul] using
      (iteratedFDeriv ℝ 2 f (k • x)).map_smul_univ (fun _ => k) v
  rw [hscale, hscale]
  ring

/-- Harmonicity is preserved by a nonzero dilation of the plane. -/
theorem harmonicAt_comp_real_dilation {f : ℂ → ℝ} {x : ℂ} {k : ℝ} (hk : k ≠ 0)
    (hf : HarmonicAt f (k • x)) : HarmonicAt (fun z => f (k • z)) x := by
  refine ⟨hf.1.comp x (by fun_prop), ?_⟩
  have hm : Tendsto (fun z : ℂ => k • z) (𝓝 x) (𝓝 (k • x)) :=
    (continuous_const_smul k).continuousAt.tendsto
  filter_upwards [hm.eventually hf.2] with z hz
  rw [laplacian_comp_real_dilation f hk, hz]
  simp

/-- Greatest harmonic minorants commute with nonzero dilations. -/
theorem greatestHarmonicMinorant_dilation (O : Set ℂ) (u : ℂ → EReal)
    {k : ℝ} (hk : k ≠ 0) (y : ℂ) :
    greatestHarmonicMinorant ((fun z : ℂ => k • z) '' O)
      (fun z => u (k⁻¹ • z)) (k • y) = greatestHarmonicMinorant O u y := by
  apply le_antisymm
  · apply iSup₂_le
    intro h hh
    let v : ℂ → ℝ := fun z => h (k • z)
    have hv : IsHarmonicMinorant O u v := by
      constructor
      · intro z hz
        exact harmonicAt_comp_real_dilation hk (hh.1 (k • z) ⟨z, hz, rfl⟩)
      · intro z hz
        simpa only [v, inv_smul_smul₀ hk] using hh.2 (k • z) ⟨z, hz, rfl⟩
    exact hv.le_greatestHarmonicMinorant y
  · apply iSup₂_le
    intro h hh
    let v : ℂ → ℝ := fun z => h (k⁻¹ • z)
    have hv : IsHarmonicMinorant ((fun z : ℂ => k • z) '' O)
        (fun z => u (k⁻¹ • z)) v := by
      constructor
      · rintro z ⟨w, hw, rfl⟩
        have hharm := harmonicAt_comp_real_dilation (x := k • w) (inv_ne_zero hk)
          (by simpa only [inv_smul_smul₀ hk] using hh.1 w hw)
        exact hharm
      · rintro z ⟨w, hw, rfl⟩
        simpa only [v, inv_smul_smul₀ hk] using hh.2 w hw
    have hvle := hv.le_greatestHarmonicMinorant (k • y)
    simpa only [v, inv_smul_smul₀ hk] using hvle

/-- The greatest harmonic minorant commutes with addition of a real constant. -/
theorem greatestHarmonicMinorant_add_const (O : Set ℂ) (u : ℂ → EReal)
    (c : ℝ) (y : ℂ) :
    greatestHarmonicMinorant O (fun z => u z + (c : EReal)) y =
      greatestHarmonicMinorant O u y + (c : EReal) := by
  let e : EReal ≃o EReal :=
    { toFun := fun x => x + (c : EReal)
      invFun := fun x => x - (c : EReal)
      left_inv := fun _ => EReal.add_sub_cancel_right
      right_inv := fun _ => EReal.sub_add_cancel
      map_rel_iff' := (EReal.addLECancellable_coe c).add_le_add_iff_right }
  change greatestHarmonicMinorant O (fun z => u z + (c : EReal)) y =
    e (greatestHarmonicMinorant O u y)
  unfold greatestHarmonicMinorant
  rw [e.map_iSup₂]
  apply le_antisymm
  · apply iSup₂_le
    intro h hh
    let v : ℂ → ℝ := fun z => h z - c
    have hv : IsHarmonicMinorant O u v := by
      constructor
      · intro z hz
        exact (hh.1 z hz).sub (harmonicAt_const c)
      · intro z hz
        change ((h z - c : ℝ) : EReal) ≤ u z
        rw [EReal.coe_sub]
        exact (EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot c))
          (.inl (EReal.coe_ne_top c))).2 (hh.2 z hz)
    have hvle : (v y : EReal) + (c : EReal) ≤
        ⨆ h, ⨆ (_ : IsHarmonicMinorant O u h), (h y : EReal) + (c : EReal) :=
      le_iSup_of_le v (le_iSup_of_le hv le_rfl)
    have he : ((h y - c : ℝ) : EReal) + (c : EReal) = (h y : EReal) := by
      rw [← EReal.coe_add, sub_add_cancel]
    change (h y : EReal) ≤ ⨆ j, ⨆ (_ : IsHarmonicMinorant O u j),
      (j y : EReal) + (c : EReal)
    simpa only [v, he] using hvle
  · apply iSup₂_le
    intro h hh
    let v : ℂ → ℝ := fun z => h z + c
    have hv : IsHarmonicMinorant O (fun z => u z + (c : EReal)) v := by
      constructor
      · intro z hz
        exact (hh.1 z hz).add (harmonicAt_const c)
      · intro z hz
        change ((h z + c : ℝ) : EReal) ≤ u z + (c : EReal)
        rw [EReal.coe_add]
        simpa only [add_comm] using add_le_add_right (hh.2 z hz) (c : EReal)
    exact hv.le_greatestHarmonicMinorant y

/-- Away from its pole, the logarithmic kernel gains a constant under dilation. -/
theorem newtonKernel_dilation {k : ℝ} (hk : 0 < k) {x y : ℂ} (hxy : x ≠ y) :
    newtonKernel (k • x) (k • y) = newtonKernel x y -
      (2 * Real.pi)⁻¹ * Real.log k := by
  have hn : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  unfold newtonKernel
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hk, Real.log_mul hk.ne' hn]
  ring

/-- The extended logarithmic kernel scales also at its pole. -/
theorem newtonKernelEReal_dilation {k : ℝ} (hk : 0 < k) (x y : ℂ) :
    newtonKernelEReal (k • x) (k • y) = newtonKernelEReal x y +
      ((- (2 * Real.pi)⁻¹ * Real.log k : ℝ) : EReal) := by
  by_cases hxy : y = x
  · subst y
    simp only [newtonKernelEReal, ↓reduceIte, EReal.top_add_coe]
  · have hxy' : k • y ≠ k • x := by
      intro heq
      exact hxy (smul_right_injective ℂ hk.ne' heq)
    simp only [newtonKernelEReal, hxy, hxy', ↓reduceIte, ← EReal.coe_add]
    congr 1
    rw [newtonKernel_dilation hk (Ne.symm hxy)]
    ring

/-- The harmonic correction to the logarithmic kernel acquires the same
additive constant as the kernel. -/
theorem greatestHarmonicMinorant_newtonKernel_dilation (O : Set ℂ) {k : ℝ}
    (hk : 0 < k) (x y : ℂ) :
    greatestHarmonicMinorant ((fun z : ℂ => k • z) '' O)
        (newtonKernelEReal (k • x)) (k • y) =
      greatestHarmonicMinorant O (newtonKernelEReal x) y +
        ((- (2 * Real.pi)⁻¹ * Real.log k : ℝ) : EReal) := by
  have hkernel : newtonKernelEReal (k • x) = fun z =>
      newtonKernelEReal x (k⁻¹ • z) +
        ((- (2 * Real.pi)⁻¹ * Real.log k : ℝ) : EReal) := by
    funext z
    have heq : k • (k⁻¹ • z) = z := smul_inv_smul₀ hk.ne' z
    conv_lhs => rw [← heq]
    exact newtonKernelEReal_dilation hk x _
  rw [hkernel, greatestHarmonicMinorant_add_const,
    greatestHarmonicMinorant_dilation O (newtonKernelEReal x) hk.ne']

/-- Green functions on bounded planar domains are invariant under positive
dilations. -/
theorem greenFunction_dilation (O : Set ℂ) (hO : Bornology.IsBounded O)
    {k : ℝ} (hk : 0 < k) (x y : ℂ) :
    greenFunction ((fun z : ℂ => k • z) '' O) (k • x) (k • y) =
      greenFunction O x y := by
  have hinj : Function.Injective (fun z : ℂ => k • z) := smul_right_injective ℂ hk.ne'
  have hm (z : ℂ) : k • z ∈ (fun w : ℂ => k • w) '' O ↔ z ∈ O := by
    constructor
    · rintro ⟨w, hw, heq⟩
      have hwz : w = z := hinj heq
      simpa only [hwz] using hw
    · intro hz
      exact ⟨z, hz, rfl⟩
  have hcond : (k • x ∈ (fun z : ℂ => k • z) '' O ∧
      k • y ∈ (fun z : ℂ => k • z) '' O ∧ k • x ≠ k • y) ↔
      (x ∈ O ∧ y ∈ O ∧ x ≠ y) := by
    simp only [hm, ne_eq, hinj.eq_iff]
  unfold greenFunction
  split_ifs with h₁ h₂
  · have hy : y ∈ O := (hcond.mp h₁).2.1
    have hxy : x ≠ y := (hcond.mp h₁).2.2
    obtain ⟨R, hR⟩ := hO.subset_closedBall x
    have hbot : greatestHarmonicMinorant O (newtonKernelEReal x) y ≠ ⊥ :=
      ne_bot_of_le_ne_bot (EReal.coe_ne_bot _)
        ((isHarmonicMinorant_const_newtonKernelEReal hR).le_greatestHarmonicMinorant y)
    have hN : newtonKernelEReal x y ≠ ⊤ := by
      simp only [newtonKernelEReal, Ne.symm hxy, ↓reduceIte]
      exact EReal.coe_ne_top _
    have htop : greatestHarmonicMinorant O (newtonKernelEReal x) y ≠ ⊤ :=
      ne_top_of_le_ne_top hN (greatestHarmonicMinorant_le hy)
    rw [newtonKernel_dilation hk hxy, greatestHarmonicMinorant_newtonKernel_dilation O hk]
    rw [EReal.toReal_add htop hbot (EReal.coe_ne_top _) (EReal.coe_ne_bot _), EReal.toReal_coe]
    ring
  all_goals simp_all

/-- A Green potential on a dilated domain is the potential of the
inverse-dilated measure. -/
theorem greenPotential_dilation {O : Set ℂ} (hO : IsOpen O) (hOb : Bornology.IsBounded O)
    (μ : Measure ℂ) {k : ℝ} (hk : 0 < k) (x : ℂ) :
    greenPotential ((fun z : ℂ => k • z) '' O) μ (k • x) =
      greenPotential O (μ.map (fun z => k⁻¹ • z)) x := by
  apply greenPotential_of_greenFunction_pullback hO μ (fun z => k • z)
    (fun z => k⁻¹ • z) (by fun_prop)
  intro z w
  simpa only [smul_inv_smul₀ hk.ne'] using greenFunction_dilation O hOb hk z (k⁻¹ • w)

/-- A positive dilation preserves the Green-potential extrema ratio. -/
theorem greenPotentialExtremaRatio_dilation {O : Set ℂ} (hO : IsOpen O)
    (hOb : Bornology.IsBounded O) (K : Set ℂ) (μ : Measure ℂ) {k : ℝ} (hk : 0 < k) :
    greenPotentialExtremaRatio ((fun z : ℂ => k • z) '' O)
        ((fun z : ℂ => k • z) '' K) μ =
      greenPotentialExtremaRatio O K (μ.map (fun z => k⁻¹ • z)) := by
  have hinj : Function.Injective (fun z : ℂ => k • z) := smul_right_injective ℂ hk.ne'
  let eK := Equiv.Set.image (fun z : ℂ => k • z) K hinj
  let eO := Equiv.Set.image (fun z : ℂ => k • z) O hinj
  symm
  unfold greenPotentialExtremaRatio
  apply greenPotential_extrema_ratio_of_equiv O K _ _ _ μ 1 (by norm_num) eK eO
  · intro x
    simpa only [one_mul, eK, Equiv.Set.image_apply] using
      (greenPotential_dilation hO hOb μ hk x).symm
  · intro x
    simpa only [one_mul, eO, Equiv.Set.image_apply] using
      (greenPotential_dilation hO hOb μ hk x).symm

/-- The extrema ratio transforms by pullback under a positive affine map. -/
theorem greenPotentialExtremaRatio_affine {O : Set ℂ} (hO : IsOpen O)
    (hOb : Bornology.IsBounded O) (K : Set ℂ) (μ : Measure ℂ)
    {k : ℝ} (hk : 0 < k) (b : ℂ) :
    greenPotentialExtremaRatio ((fun z : ℂ => k • z + b) '' O)
        ((fun z : ℂ => k • z + b) '' K) μ =
      greenPotentialExtremaRatio O K (μ.map (fun z => k⁻¹ • (z - b))) := by
  have ho' : IsOpen ((fun z : ℂ => k • z) '' O) :=
    (Homeomorph.smulOfNeZero k hk.ne').isOpenMap _ hO
  have h := greenPotentialExtremaRatio_translate ho' ((fun z : ℂ => k • z) '' K) μ b
  rw [greenPotentialExtremaRatio_dilation hO hOb K _ hk] at h
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at h
  simpa only [image_image, Function.comp_def] using h

universe u

/-- Whole-plane LQG Green-potential ratios on dilated smooth domains have the
same law under the explicit affine and coordinate-change inputs. -/
theorem identDistrib_lqg_greenPotentialExtremaRatio_dilation
    (hholder : GreenPotentialHolderStmt.{u}) {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    {k : ℝ} (hk : 0 < k) {O K : Set ℂ} (hO : IsSmoothBoundedOpen O)
    (hK : K ⊆ closure O) :
    IdentDistrib (fun ω => greenPotentialExtremaRatio O K (μ ω))
      (fun ω => greenPotentialExtremaRatio ((fun z : ℂ => k • z) '' O)
        ((fun z : ℂ => k • z) '' K) (μ ω)) P P := by
  have hopen : IsOpen O := by
    obtain ⟨_, ρ, hρ, rfl, _⟩ := hO
    exact isOpen_lt hρ.continuous continuous_const
  have hd := identDistrib_lqg_greenPotentialExtremaRatio_affine hholder hγ hγ2 h hμ
    hAff hCC (a := (k : ℂ)) (by exact_mod_cast hk.ne') 0 hO hK
  apply hd.trans
  apply IdentDistrib.of_ae_eq hd.aemeasurable_snd
  filter_upwards [] with ω
  simpa only [sub_zero, div_eq_mul_inv, ← Complex.ofReal_inv, Complex.real_smul,
    mul_comm] using (greenPotentialExtremaRatio_dilation hopen hO.1 K (μ ω) hk).symm

/-- Whole-plane LQG Green-potential ratios on positive affine images of a
smooth domain have the same law under the explicit literature inputs. -/
theorem identDistrib_lqg_greenPotentialExtremaRatio_positive_affine
    (hholder : GreenPotentialHolderStmt.{u}) {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    {k : ℝ} (hk : 0 < k) (b : ℂ) {O K : Set ℂ} (hO : IsSmoothBoundedOpen O)
    (hK : K ⊆ closure O) :
    IdentDistrib (fun ω => greenPotentialExtremaRatio O K (μ ω))
      (fun ω => greenPotentialExtremaRatio ((fun z : ℂ => k • z + b) '' O)
        ((fun z : ℂ => k • z + b) '' K) (μ ω)) P P := by
  have hopen : IsOpen O := by
    obtain ⟨_, ρ, hρ, rfl, _⟩ := hO
    exact isOpen_lt hρ.continuous continuous_const
  have hd := identDistrib_lqg_greenPotentialExtremaRatio_affine hholder hγ hγ2 h hμ
    hAff hCC (a := (k : ℂ)) (by exact_mod_cast hk.ne') b hO hK
  apply hd.trans
  apply IdentDistrib.of_ae_eq hd.aemeasurable_snd
  filter_upwards [] with ω
  simpa only [div_eq_mul_inv, ← Complex.ofReal_inv, Complex.real_smul,
    mul_comm] using (greenPotentialExtremaRatio_affine hopen hO.1 K (μ ω) hk b).symm

end HarmonicBalls.Section6
