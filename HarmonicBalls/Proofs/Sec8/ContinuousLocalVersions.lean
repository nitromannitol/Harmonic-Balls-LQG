import HarmonicBalls.Proofs.Sec8.ContinuityExhaustion

/-! # Joint local versions of continuous random functions

Pointwise local versions on an open set determine a jointly measurable local
version when the sample paths are almost surely continuous.

The Section 8 frequency results imported below use the pointwise ergodic
theorem from Leonardo Bonanno's LatticeProb formalization.
-/

open MeasureTheory Filter Set Metric
open scoped Topology

namespace HarmonicBalls

/-- Pointwise measurable versions on an open set combine into one jointly
measurable version, simultaneously at all points of that set. -/
theorem exists_joint_local_version_of_pointwise
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : @Measure Ω mΩ}
    (m : MeasurableSpace Ω) {U : Set ℂ} (hU : IsOpen U)
    (f : Ω → ℂ → ℝ)
    (hcont : ∀ᵐ ω ∂P, Continuous (f ω))
    (hpoint : ∀ z ∈ U, ∃ g : Ω → ℝ,
      @Measurable Ω ℝ m _ g ∧ (fun ω => f ω z) =ᵐ[P] g) :
    ∃ d : Ω → ℂ → ℝ,
      @Measurable (Ω × ℂ) ℝ (m.prod inferInstance) _ (Function.uncurry d) ∧
      ∀ᵐ ω ∂P, ∀ z ∈ U, d ω z = f ω z := by
  classical
  let g : ℂ → Ω → ℝ := fun z => if hz : z ∈ U then (hpoint z hz).choose else fun _ => 0
  have hg (z : ℂ) : @Measurable Ω ℝ m _ (g z) := by
    by_cases hz : z ∈ U
    · simpa [g, hz] using (hpoint z hz).choose_spec.1
    · simp only [g, hz, ↓reduceDIte]
      exact measurable_const
  have hgeq (z : ℂ) (hz : z ∈ U) : (fun ω => f ω z) =ᵐ[P] g z := by
    simpa [g, hz] using (hpoint z hz).choose_spec.2
  let a : ℕ → SimpleFunc ℂ ℂ := (stronglyMeasurable_id : StronglyMeasurable (id : ℂ → ℂ)).approx
  have ha (z : ℂ) : Tendsto (fun n => a n z) atTop (𝓝 z) := by
    exact (stronglyMeasurable_id : StronglyMeasurable (id : ℂ → ℂ)).tendsto_approx z
  let F : ℕ → ℂ × Ω → ℝ := fun n p => g (a n p.1) p.2
  have hF (n : ℕ) : @Measurable (ℂ × Ω) ℝ ((inferInstance : MeasurableSpace ℂ).prod m) _ (F n) := by
    have hfinite : @Measurable ((a n).range × Ω) ℝ
        ((inferInstance : MeasurableSpace (a n).range).prod m) _ (fun p => g p.1 p.2) := by
      apply measurable_from_prod_countable_right
      intro z
      exact hg z
    change @Measurable (ℂ × Ω) ℝ ((inferInstance : MeasurableSpace ℂ).prod m) _
      ((fun p : (a n).range × Ω => g p.1 p.2) ∘
        (fun p : ℂ × Ω => (⟨a n p.1, SimpleFunc.mem_range_self _ _⟩, p.2)))
    apply hfinite.comp
    exact ((a n).measurable.comp measurable_fst).subtype_mk |>.prodMk measurable_snd
  let D : ℂ × Ω → ℝ := fun p => liminf (fun n => F n p) atTop
  have hD : @Measurable (ℂ × Ω) ℝ ((inferInstance : MeasurableSpace ℂ).prod m) _ D :=
    Measurable.liminf hF
  have hae : ∀ᵐ ω ∂P, ∀ n (z : (a n).range), z.val ∈ U → f ω z = g z ω := by
    apply ae_all_iff.mpr
    intro n
    apply ae_all_iff.mpr
    intro z
    by_cases hz : z.val ∈ U
    · filter_upwards [hgeq z hz] with ω hω _
      exact hω
    · exact Filter.Eventually.of_forall (fun _ h => (hz h).elim)
  refine ⟨fun ω z => D (z, ω), ?_, ?_⟩
  · exact hD.comp measurable_swap
  · filter_upwards [hcont, hae] with ω hω hωeq z hz
    have hzmem : ∀ᶠ n in atTop, a n z ∈ U := (ha z).eventually (hU.mem_nhds hz)
    have heq : (fun n => F n (z, ω)) =ᶠ[atTop] (fun n => f ω (a n z)) := by
      filter_upwards [hzmem] with n hn
      exact (hωeq n ⟨a n z, SimpleFunc.mem_range_self _ _⟩ hn).symm
    have ht : Tendsto (fun n => F n (z, ω)) atTop (𝓝 (f ω z)) :=
      ((hω.tendsto z).comp (ha z)).congr' heq.symm
    exact ht.liminf_eq

/-- The centers of closed balls contained in an open set form an open set. -/
theorem isOpen_centers_closedBall_subset (r : ℝ) {V : Set ℂ} (hV : IsOpen V) :
    IsOpen {z : ℂ | closedBall z r ⊆ V} := by
  rw [Metric.isOpen_iff]
  intro z hz
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_closedBall z r).exists_thickening_subset_open hV hz
  refine ⟨δ, hδ, ?_⟩
  intro z' hz' y hy
  apply hsub
  apply Metric.mem_thickening_iff.mpr
  refine ⟨y + (z - z'), ?_, ?_⟩
  · apply mem_closedBall.mpr
    have hd : dist (y + (z - z')) z = dist y z' := by
      simp only [dist_eq_norm]
      congr 1
      abel
    rw [hd]
    exact mem_closedBall.mp hy
  · have hd : dist y (y + (z - z')) = dist z' z := by
      simp only [dist_eq_norm]
      congr 1
      abel
    rw [hd]
    exact mem_ball.mp hz'

/-- A local scalar version of each centered circle average supplies the joint
version needed for the LQG mass-ratio argument. -/
theorem IsWholePlaneGFF.exists_joint_centered_circle_version_of_pointwise
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) {ε r : ℝ} (hr : 0 < r)
    (hpoint : ∀ z, closedBall z r ⊆ ball 0 ε → ∃ g : Ω → ℝ,
      @Measurable Ω ℝ (Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε)) _ g ∧
      (fun ω => fieldCircleAverage α₀ (hcirc ω) r z -
        fieldCircleAverage α₀ (hcirc ω) r 0) =ᵐ[P] g) :
    ∃ d : Ω → ℂ → ℝ,
      @Measurable (Ω × ℂ) ℝ
        ((Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε)).prod inferInstance) _
        (Function.uncurry d) ∧
      ∀ᵐ ω ∂P, ∀ z, closedBall z r ⊆ ball 0 ε →
        d ω z = fieldCircleAverage α₀ (hcirc ω) r z -
          fieldCircleAverage α₀ (hcirc ω) r 0 := by
  apply exists_joint_local_version_of_pointwise
    (Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε))
    (isOpen_centers_closedBall_subset r isOpen_ball)
  · filter_upwards [hGFF.ae_continuous_fieldCircleAverage α₀ hr] with ω hω
    exact hω.sub continuous_const
  · exact hpoint

/-- A limit in probability of measurable functions admits a measurable
version for the original probability measure, without completing the smaller
sigma algebra. -/
theorem exists_measurable_version_of_tendstoInMeasure
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : @Measure Ω mΩ}
    (m : MeasurableSpace Ω) (F : ℕ → Ω → ℝ) (f : Ω → ℝ)
    (hF : ∀ n, @Measurable Ω ℝ m _ (F n))
    (hlim : TendstoInMeasure P F atTop f) :
    ∃ g : Ω → ℝ, @Measurable Ω ℝ m _ g ∧ f =ᵐ[P] g := by
  obtain ⟨s, _, hs⟩ := hlim.exists_seq_tendsto_ae
  refine ⟨fun ω => liminf (fun n => F (s n) ω) atTop,
    Measurable.liminf (fun n => hF (s n)), ?_⟩
  filter_upwards [hs] with ω hω
  exact hω.liminf_eq.symm

/-- A local zero-integral test-function pairing is measurable for the local
field modulo constants. -/
theorem measurable_fieldPairing_modConst {Ω : Type*} (α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (U : Set ℂ) (φ : ℂ → ℝ)
    (hφ : IsTestFunction U φ ∧ ∫ x, φ x = 0) :
    @Measurable Ω ℝ (Section6.fieldSigmaAlgebraModConst α₀ hC U) _
      (fun ω => fieldPairing α₀ (hC ω) φ) := by
  apply Measurable.of_comap_le
  exact le_iSup_of_le φ (le_iSup (fun h : IsTestFunction U φ ∧ ∫ x, φ x = 0 =>
    MeasurableSpace.comap (fun ω => fieldPairing α₀ (hC ω) φ) inferInstance) hφ)

/-- Approximation in probability by local zero-integral test pairings yields
jointly measurable centered circle averages. -/
theorem IsWholePlaneGFF.exists_joint_centered_circle_version_of_pairing_approximation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) {ε r : ℝ} (hr : 0 < r)
    (happrox : ∀ z, closedBall z r ⊆ ball 0 ε → ∃ φ : ℕ → ℂ → ℝ,
      (∀ n, IsTestFunction (ball 0 ε) (φ n) ∧ ∫ x, φ n x = 0) ∧
      TendstoInMeasure P (fun n ω => fieldPairing α₀ (hC ω) (φ n)) atTop
        (fun ω => fieldCircleAverage α₀ (hcirc ω) r z -
          fieldCircleAverage α₀ (hcirc ω) r 0)) :
    ∃ d : Ω → ℂ → ℝ,
      @Measurable (Ω × ℂ) ℝ
        ((Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε)).prod inferInstance) _
        (Function.uncurry d) ∧
      ∀ᵐ ω ∂P, ∀ z, closedBall z r ⊆ ball 0 ε →
        d ω z = fieldCircleAverage α₀ (hcirc ω) r z -
          fieldCircleAverage α₀ (hcirc ω) r 0 := by
  apply hGFF.exists_joint_centered_circle_version_of_pointwise hr
  intro z hz
  obtain ⟨φ, hφ, hlim⟩ := happrox z hz
  exact exists_measurable_version_of_tendstoInMeasure _ _ _
    (fun n => measurable_fieldPairing_modConst α₀ hC _ (φ n) (hφ n)) hlim

end HarmonicBalls
