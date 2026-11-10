import HarmonicBalls.Draft.Section11

/-!
# Assembly of the exterior event of Lemma 11.16 (fp-S11k, owner z3)

`PinchSecondExteriorEventStep` (`FirstPass/S11k.lean`) asks for constants `c₁, c₂ > 0` and an event `F` measurable for the
exterior sigma-algebra with `P F > 0` on which the first event, the lower bound `c₁ ≤ D(∂B_δ, ∂B_{2δ})` and the Green bound
`M · SG_{3,6}(0) ≤ c₂` hold a.s. The last step of its proof is pure measure theory and is isolated here:

* `exists_level_event`: given a measurable event `F₀` of positive measure, a measurable real `d` positive a.s. on `F₀`
  and a measurable `S` finite a.s. on `F₀`, there are levels `c₁, c₂ > 0` and a measurable `F ⊆ F₀` of positive measure
  with `c₁ ≤ d` and `S ≤ c₂` on `F`.
* `exists_pinchSecondExteriorEvent_of_versions`: the same statement with the pinch quantities; the inputs are the
  exterior versions named in the docstring, so the open steps of `PinchSecondExteriorEventStep` are exactly these inputs.

No measurability in the ambient sigma-algebra is needed: only `measure_iUnion_null` and `measure_mono_ae`.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric Filter
open scoped ENNReal

/-- Level-set selection (continuity of measure from below, done by contradiction). -/
theorem exists_level_event {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {m : MeasurableSpace Ω}
    {F₀ : Set Ω} (hF₀ : MeasurableSet[m] F₀) (hF₀pos : 0 < P F₀)
    {d : Ω → ℝ} (hd : Measurable[m] d) (hdpos : ∀ᵐ ω ∂P, ω ∈ F₀ → 0 < d ω)
    {S : Ω → ℝ≥0∞} (hS : Measurable[m] S) (hSfin : ∀ᵐ ω ∂P, ω ∈ F₀ → S ω ≠ ∞) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∃ F : Set Ω, MeasurableSet[m] F ∧
      (∀ᵐ ω ∂P, ω ∈ F → ω ∈ F₀ ∧ c₁ ≤ d ω ∧ S ω ≤ ENNReal.ofReal c₂) ∧ 0 < P F := by
  classical
  -- lower levels of `d` on `F₀`
  let A : ℕ → Set Ω := fun n => F₀ ∩ {ω | 1 / ((n : ℝ) + 1) ≤ d ω}
  have hAm : ∀ n, MeasurableSet[m] (A n) := fun n =>
    hF₀.inter (measurableSet_le measurable_const hd)
  have hcover : F₀ ≤ᵐ[P] ⋃ n, A n := by
    filter_upwards [hdpos] with ω hω hF
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (hω hF)
    exact Set.mem_iUnion.2 ⟨n, hF, hn.le⟩
  obtain ⟨n₀, hn₀⟩ : ∃ n : ℕ, 0 < P (A n) := by
    by_contra hcon
    push Not at hcon
    have h0 : P (⋃ n, A n) = 0 :=
      measure_iUnion_null fun n => le_antisymm (hcon n) zero_le
    exact hF₀pos.ne' (le_antisymm ((measure_mono_ae hcover).trans_eq h0) zero_le)
  -- upper levels of `S` on `A n₀`
  let B : ℕ → Set Ω := fun k => A n₀ ∩ {ω | S ω ≤ (k : ℝ≥0∞)}
  have hBm : ∀ k, MeasurableSet[m] (B k) := fun k =>
    (hAm n₀).inter (measurableSet_le hS measurable_const)
  have hcover2 : A n₀ ≤ᵐ[P] ⋃ k, B k := by
    filter_upwards [hSfin] with ω hω hA
    obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt (hω hA.1)
    exact Set.mem_iUnion.2 ⟨k, hA, hk.le⟩
  obtain ⟨k₀, hk₀⟩ : ∃ k : ℕ, 0 < P (B k) := by
    by_contra hcon
    push Not at hcon
    have h0 : P (⋃ k, B k) = 0 :=
      measure_iUnion_null fun k => le_antisymm (hcon k) zero_le
    exact hn₀.ne' (le_antisymm ((measure_mono_ae hcover2).trans_eq h0) zero_le)
  refine ⟨1 / ((n₀ : ℝ) + 1), (k₀ : ℝ) + 1, by positivity, by positivity, B k₀, hBm k₀, ?_, hk₀⟩
  refine Filter.Eventually.of_forall fun ω hω => ⟨hω.1.1, hω.1.2, hω.2.trans ?_⟩
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- The exterior event of `PinchSecondExteriorEventStep` from its named inputs. The exterior event `F₀` carries the first
event of `pinchFirstEvent` a.s. and has positive measure (`N3`); `d` is the exterior version of
`D(∂B_δ, ∂B_{2δ})` (`N1`, via `exists_outside_ofReal_setDist_of_internalMetric`); `S` is an exterior version of the Green
bound `M · SG_{3,6}(0)` (`N2`, via `exists_outside_green_of_singular_weyl`). -/
theorem exists_pinchSecondExteriorEvent_of_versions {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {m : MeasurableSpace Ω} (W T Q' Q : Set ℂ) (δ M : ℝ) {D : Ω → ℂ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {F₀ : Set Ω} (hF₀ : MeasurableSet[m] F₀) (hF₀pos : 0 < P F₀)
    (hF₀E : ∀ᵐ ω ∂P, ω ∈ F₀ → pinchFirstEvent (D ω) W T Q' Q δ)
    {d : Ω → ℝ} (hd : Measurable[m] d)
    (hdv : ∀ᵐ ω ∂P, d ω = setDist (D ω) (sphere 0 δ) (sphere 0 (2 * δ)))
    (hdpos : ∀ᵐ ω ∂P, ω ∈ F₀ → 0 < d ω)
    {S : Ω → ℝ≥0∞} (hS : Measurable[m] S)
    (hSv : ∀ᵐ ω ∂P, ENNReal.ofReal M * annulusGreenPotentialSup (μ ω) 0 3 6 ≤ S ω)
    (hSfin : ∀ᵐ ω ∂P, ω ∈ F₀ → S ω ≠ ∞) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∃ F : Set Ω, MeasurableSet[m] F ∧
      (∀ᵐ ω ∂P, ω ∈ F → pinchFirstEvent (D ω) W T Q' Q δ ∧
        c₁ ≤ setDist (D ω) (sphere 0 δ) (sphere 0 (2 * δ)) ∧
        ENNReal.ofReal M * annulusGreenPotentialSup (μ ω) 0 3 6 ≤ ENNReal.ofReal c₂) ∧ 0 < P F := by
  obtain ⟨c₁, c₂, h₁, h₂, F, hFm, hFae, hFpos⟩ :=
    exists_level_event (mΩ := mΩ) (m := m) hF₀ hF₀pos hd hdpos hS hSfin
  refine ⟨c₁, c₂, h₁, h₂, F, hFm, ?_, hFpos⟩
  filter_upwards [hFae, hF₀E, hdv, hSv] with ω h1 h2 h3 h4 hωF
  obtain ⟨hF₀ω, hc₁, hSc₂⟩ := h1 hωF
  refine ⟨h2 hF₀ω, ?_, h4.trans hSc₂⟩
  rw [← h3]
  exact hc₁

end HarmonicBalls
