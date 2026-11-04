import HarmonicBalls.Proofs.Sec6.AffineMeasureLaw

/-! # Translation invariance of the planar Green function -/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter Topology InnerProductSpace Laplacian

/-- The planar Laplacian commutes with translation, even for functions that
are not differentiable. -/
theorem laplacian_comp_add_right (f : ℂ → ℝ) (b x : ℂ) :
    Δ (fun z => f (z + b)) x = Δ f (x + b) := by
  simp only [laplacian_eq_iteratedFDeriv_complexPlane, iteratedFDeriv_comp_add_right]

/-- Translating the argument of a harmonic function preserves harmonicity. -/
theorem harmonicAt_comp_add_right {f : ℂ → ℝ} {x b : ℂ}
    (hf : HarmonicAt f (x + b)) : HarmonicAt (fun z => f (z + b)) x := by
  refine ⟨?_, ?_⟩
  · exact hf.1.comp x (by fun_prop)
  · have hm : Tendsto (fun z : ℂ => z + b) (𝓝 x) (𝓝 (x + b)) :=
      (continuous_id.add continuous_const).continuousAt.tendsto
    filter_upwards [hm.eventually hf.2] with z hz
    rw [laplacian_comp_add_right]
    exact hz

/-- Greatest harmonic minorants commute with translation. -/
theorem greatestHarmonicMinorant_translate (O : Set ℂ) (u : ℂ → EReal) (b y : ℂ) :
    greatestHarmonicMinorant ((fun z : ℂ => z + b) '' O) (fun z => u (z - b)) (y + b) =
      greatestHarmonicMinorant O u y := by
  apply le_antisymm
  · apply iSup₂_le
    intro h hh
    let v : ℂ → ℝ := fun z => h (z + b)
    have hv : IsHarmonicMinorant O u v := by
      constructor
      · intro z hz
        exact harmonicAt_comp_add_right (hh.1 (z + b) ⟨z, hz, rfl⟩)
      · intro z hz
        simpa only [v, add_sub_cancel_right] using hh.2 (z + b) ⟨z, hz, rfl⟩
    exact hv.le_greatestHarmonicMinorant y
  · apply iSup₂_le
    intro h hh
    let v : ℂ → ℝ := fun z => h (z - b)
    have hv : IsHarmonicMinorant ((fun z : ℂ => z + b) '' O) (fun z => u (z - b)) v := by
      constructor
      · rintro z ⟨w, hw, rfl⟩
        have hharm := harmonicAt_comp_add_right (x := w + b) (b := -b) (by simpa using hh.1 w hw)
        simpa only [v, sub_eq_add_neg] using hharm
      · rintro z ⟨w, hw, rfl⟩
        simpa only [v, add_sub_cancel_right] using hh.2 w hw
    have hvle := hv.le_greatestHarmonicMinorant (y + b)
    simpa only [v, add_sub_cancel_right] using hvle

/-- The logarithmic kernel is invariant under simultaneous translation. -/
theorem newtonKernel_translate (x y b : ℂ) :
    newtonKernel (x + b) (y + b) = newtonKernel x y := by
  simp only [newtonKernel, add_sub_add_right_eq_sub]

/-- The extended logarithmic kernel, including its pole, translates with the
same rule. -/
theorem newtonKernelEReal_translate (x b : ℂ) :
    newtonKernelEReal (x + b) = fun z => newtonKernelEReal x (z - b) := by
  funext z
  obtain ⟨w, rfl⟩ : ∃ w : ℂ, z = w + b := ⟨z - b, by simp⟩
  simp only [newtonKernelEReal, add_right_cancel_iff, add_sub_cancel_right, newtonKernel_translate]

/-- Green functions of arbitrary planar domains are translation invariant. -/
theorem greenFunction_translate (O : Set ℂ) (b x y : ℂ) :
    greenFunction ((fun z : ℂ => z + b) '' O) (x + b) (y + b) = greenFunction O x y := by
  have hm (z : ℂ) : z + b ∈ (fun w : ℂ => w + b) '' O ↔ z ∈ O := by
    constructor
    · rintro ⟨w, hw, heq⟩
      have hwz : w = z := add_right_cancel heq
      simpa only [hwz] using hw
    · intro hz
      exact ⟨z, hz, rfl⟩
  have hcond : (x + b ∈ (fun z : ℂ => z + b) '' O ∧
      y + b ∈ (fun z : ℂ => z + b) '' O ∧ x + b ≠ y + b) ↔
      (x ∈ O ∧ y ∈ O ∧ x ≠ y) := by
    simp only [hm, ne_eq, add_right_cancel_iff]
  simp only [greenFunction, newtonKernel_translate, newtonKernelEReal_translate,
    greatestHarmonicMinorant_translate]
  split_ifs with h1 h2
  all_goals simp_all

/-- Translation of a Green potential is the potential of the translated-back
measure. -/
theorem greenPotential_translate {O : Set ℂ} (hO : IsOpen O) (μ : Measure ℂ)
    (b x : ℂ) :
    greenPotential ((fun z : ℂ => z + b) '' O) μ (x + b) =
      greenPotential O (μ.map (fun z => z - b)) x := by
  apply greenPotential_of_greenFunction_pullback hO μ (fun z => z + b) (fun z => z - b)
    (by fun_prop)
  intro z w
  simpa only [sub_add_cancel] using greenFunction_translate O b z (w - b)

/-- The Green-potential extrema ratio commutes with translating the domain,
the comparison set, and the measure. -/
theorem greenPotentialExtremaRatio_translate {O : Set ℂ} (hO : IsOpen O)
    (K : Set ℂ) (μ : Measure ℂ) (b : ℂ) :
    greenPotentialExtremaRatio ((fun z : ℂ => z + b) '' O)
        ((fun z : ℂ => z + b) '' K) μ =
      greenPotentialExtremaRatio O K (μ.map (fun z => z - b)) := by
  have hinj : Function.Injective (fun z : ℂ => z + b) := fun _ _ h => add_right_cancel h
  let eK := Equiv.Set.image (fun z : ℂ => z + b) K hinj
  let eO := Equiv.Set.image (fun z : ℂ => z + b) O hinj
  symm
  unfold greenPotentialExtremaRatio
  apply greenPotential_extrema_ratio_of_equiv O K _ _ _ μ 1 (by norm_num) eK eO
  · intro x
    simpa only [one_mul, eK, Equiv.Set.image_apply] using
      (greenPotential_translate hO μ b x).symm
  · intro x
    simpa only [one_mul, eO, Equiv.Set.image_apply] using
      (greenPotential_translate hO μ b x).symm

universe u

/-- Whole-plane LQG Green-potential ratios on translates of a smooth domain
have the same law, under the explicit affine and coordinate-change inputs. -/
theorem identDistrib_lqg_greenPotentialExtremaRatio_translate
    (hholder : GreenPotentialHolderStmt.{u}) {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (b : ℂ) {O K : Set ℂ} (hO : IsSmoothBoundedOpen O) (hK : K ⊆ closure O) :
    IdentDistrib (fun ω => greenPotentialExtremaRatio O K (μ ω))
      (fun ω => greenPotentialExtremaRatio ((fun z : ℂ => z + b) '' O)
        ((fun z : ℂ => z + b) '' K) (μ ω)) P P := by
  have hopen : IsOpen O := by
    obtain ⟨_, ρ, hρ, rfl, _⟩ := hO
    exact isOpen_lt hρ.continuous continuous_const
  have hd := identDistrib_lqg_greenPotentialExtremaRatio_affine hholder hγ hγ2 h hμ
    hAff hCC (a := (1 : ℂ)) one_ne_zero b hO hK
  apply hd.trans
  apply IdentDistrib.of_ae_eq hd.aemeasurable_snd
  filter_upwards [] with ω
  simpa only [div_one] using (greenPotentialExtremaRatio_translate hopen K (μ ω) b).symm

end HarmonicBalls.Section6
