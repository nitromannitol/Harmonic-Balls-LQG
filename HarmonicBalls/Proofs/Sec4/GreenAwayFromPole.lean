import HarmonicBalls.Steps.Sec4.ClusterSubharmonicBall

/-!
# Lemma 4.3, auxiliary step: the Green function of an open set is bounded away from its pole

`greenFunctionIntegrableAwayFromPoleStep_holds : GreenFunctionIntegrableAwayFromPoleStep`.

For an open set `O`, `z ∈ O` and a finite measure `ν` concentrated on a compact `K ⊆ O` with `z ∉ K`, the function
`G_O(z,·)` is `ν`-integrable. No harmonicity of the greatest harmonic minorant is needed:

* *Measurability.* The greatest harmonic minorant `I_O[N(z,·)]` (Defs/Green.lean) is a supremum of functions
  continuous on `O`, hence lower semicontinuous on the open set `O`; extended by `⊥` off `O` it is lower semicontinuous
  on `ℂ` (`lowerSemicontinuous_greatestHarmonicMinorant_extend`), hence Borel.
* *Boundedness on `K`.* If `N(z,·)` has a harmonic minorant `h₀` on `O` (Greenian `O`), then
  `h₀ ≤ I_O[N(z,·)] ≤ N(z,·)` on `O \ {z}`, and both bounds are continuous on `K`; otherwise `I_O[N(z,·)] = ⊥` and
  `G_O(z,·) = N(z,·)` on `O \ {z}`. In both cases `G_O(z,·)` is bounded on `K` (`z ∉ K`).
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

open Classical in
/-- The greatest harmonic minorant of any extended-real function on an open set `O`, extended by `⊥` off `O`, is lower
semicontinuous: it is a supremum of functions continuous on `O` (Armitage–Gardiner §3.1). -/
theorem lowerSemicontinuous_greatestHarmonicMinorant_extend {O : Set ℂ} (hO : IsOpen O) (u : ℂ → EReal) :
    LowerSemicontinuous (fun y => if y ∈ O then greatestHarmonicMinorant O u y else ⊥) := by
  intro x c hc
  dsimp only at hc ⊢
  by_cases hx : x ∈ O
  · rw [ite_eq_left hx] at hc
    obtain ⟨h, hc'⟩ := lt_iSup_iff.1 hc
    obtain ⟨hh, hch⟩ := lt_iSup_iff.1 hc'
    have hcont : ContinuousAt (fun y => (h y : EReal)) x :=
      continuous_coe_real_ereal.continuousAt.comp (hh.1 x hx).1.continuousAt
    filter_upwards [hO.mem_nhds hx, hcont.eventually (lt_mem_nhds hch)] with y hyO hy
    rw [ite_eq_left hyO]
    exact lt_of_lt_of_le hy (hh.le_greatestHarmonicMinorant y)
  · rw [ite_eq_right hx] at hc
    exact absurd hc not_lt_bot

theorem measurable_newtonKernel (z : ℂ) : Measurable (newtonKernel z) := by
  unfold newtonKernel
  exact (Real.measurable_log.comp (measurable_const.sub measurable_id).norm).const_mul _

open Classical in
/-- `y ↦ G_O(z,y)` is Borel measurable for every open `O`. -/
theorem measurable_greenFunction {O : Set ℂ} (hO : IsOpen O) (z : ℂ) : Measurable (greenFunction O z) := by
  by_cases hz : z ∉ O
  · have h0 : greenFunction O z = fun _ => 0 := funext (greenFunction_of_notMem_left hz)
    rw [h0]
    exact measurable_const
  rw [not_not] at hz
  set F : ℂ → EReal := fun y => if y ∈ O then greatestHarmonicMinorant O (newtonKernelEReal z) y else ⊥ with hF
  have hFm : Measurable F := (lowerSemicontinuous_greatestHarmonicMinorant_extend hO _).measurable
  have heq : greenFunction O z =
      (O ∩ {z}ᶜ).indicator (fun y => newtonKernel z y - (F y).toReal) := by
    funext y
    by_cases hy : y ∈ O ∩ {z}ᶜ
    · rw [indicator_of_mem hy, greenFunction, ite_eq_left ⟨hz, hy.1, Ne.symm hy.2⟩]
      simp only [hF, ite_eq_left hy.1]
    · rw [indicator_of_notMem hy, greenFunction, ite_eq_right (fun h => hy ⟨h.2.1, Ne.symm h.2.2⟩)]
  have hset : MeasurableSet (O ∩ {z}ᶜ) :=
    hO.measurableSet.inter (measurableSet_singleton z).compl
  rw [heq]
  exact ((measurable_newtonKernel z).sub hFm.ereal_toReal).indicator hset

/-- On a compact `K ⊆ O` not containing the pole, `G_O(z,·)` is bounded. -/
theorem exists_bound_greenFunction {O K : Set ℂ} {z : ℂ} (hzO : z ∈ O) (hK : IsCompact K) (hKO : K ⊆ O)
    (hzK : z ∉ K) : ∃ C : ℝ, ∀ y ∈ K, |greenFunction O z y| ≤ C := by
  have hNc : ContinuousOn (newtonKernel z) K := by
    unfold newtonKernel
    refine continuousOn_const.mul (ContinuousOn.log (continuousOn_const.sub continuousOn_id).norm ?_)
    intro y hy
    exact norm_ne_zero_iff.2 (sub_ne_zero.2 (fun h => hzK (h ▸ hy)))
  obtain ⟨C₁, hC₁⟩ := hK.exists_bound_of_continuousOn hNc
  by_cases hG : ∃ h₀, IsHarmonicMinorant O (newtonKernelEReal z) h₀
  · obtain ⟨h₀, hh₀⟩ := hG
    have hc : ContinuousOn h₀ K := fun y hy => (hh₀.1 y (hKO hy)).1.continuousAt.continuousWithinAt
    obtain ⟨C₂, hC₂⟩ := hK.exists_bound_of_continuousOn hc
    refine ⟨2 * C₁ + C₂, fun y hy => ?_⟩
    have hyz : y ≠ z := fun h => hzK (h ▸ hy)
    have hN := hC₁ y hy
    have hh := hC₂ y hy
    rw [Real.norm_eq_abs] at hN hh
    rw [greenFunction, ite_eq_left ⟨hzO, hKO hy, Ne.symm hyz⟩]
    have hlow := hh₀.le_greatestHarmonicMinorant y
    have hup : greatestHarmonicMinorant O (newtonKernelEReal z) y ≤ (newtonKernel z y : EReal) := by
      simpa [newtonKernelEReal, hyz] using greatestHarmonicMinorant_le (u := newtonKernelEReal z) (hKO hy)
    have hbot : greatestHarmonicMinorant O (newtonKernelEReal z) y ≠ ⊥ :=
      ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hlow
    have h1 := EReal.toReal_le_toReal hup hbot (EReal.coe_ne_top _)
    have h2 := EReal.toReal_le_toReal hlow (EReal.coe_ne_bot _) (ne_top_of_le_ne_top (EReal.coe_ne_top _) hup)
    rw [EReal.toReal_coe] at h1 h2
    rw [abs_le] at hN hh ⊢
    constructor <;> linarith
  · push Not at hG
    refine ⟨C₁, fun y hy => ?_⟩
    have hyz : y ≠ z := fun h => hzK (h ▸ hy)
    have hbot : greatestHarmonicMinorant O (newtonKernelEReal z) y = ⊥ := by
      simp [greatestHarmonicMinorant, hG]
    rw [greenFunction, ite_eq_left ⟨hzO, hKO hy, Ne.symm hyz⟩, hbot, EReal.toReal_bot, sub_zero]
    simpa [Real.norm_eq_abs] using hC₁ y hy

/-- **Lemma 4.3, auxiliary step** (`GreenFunctionIntegrableAwayFromPoleStep`). -/
theorem greenFunctionIntegrableAwayFromPoleStep_holds : GreenFunctionIntegrableAwayFromPoleStep := by
  intro O K z ν hO hzO hK hKO hzK hν hνK
  obtain ⟨C, hC⟩ := exists_bound_greenFunction hzO hK hKO hzK
  refine Integrable.of_bound (measurable_greenFunction hO z).aestronglyMeasurable C ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hνK] with y hy
  rw [Real.norm_eq_abs]
  exact hC y (by simpa using hy)

end HarmonicBalls
