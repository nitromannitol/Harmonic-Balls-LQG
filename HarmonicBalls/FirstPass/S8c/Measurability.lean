import HarmonicBalls.FirstPass.S8c.LocalObservation
import HarmonicBalls.Proofs.Sec8.RootedSamplingProbability

/-! # Measurability of the local observation maps (FIRST-PASS, fp-S8c-8-2-local, step M)

Joint measurability of the root observation `O_j = localRootObservation μ j` and the reference observation
`V_j = localReferenceObservation ν j` of `LocalObservation.lean`. They are needed for the joint transfer lemma
`ae_mem_of_map_absolutelyContinuous` and so that the frozen domination `LocalRootedFieldMeasureDomination`
is not vacuous (`Measure.map` of a non-measurable map is zero).

Route. Sections `ν p.1 {x | (x, p.2) ∈ W}` of a measurable family of finite measures are jointly measurable
(Dynkin induction over measurable rectangles, `sectionMeasure_of_finite`). Every measure is replaced by its
`finitePart`, a countable sum of capped pieces on the disjointed balls, which is finite on each ball for every
measure and equals the measure when it is locally finite. Local finiteness holds almost surely, so no
s-finiteness of the kernel is needed.
-/

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal

namespace HarmonicBalls

section Dynkin

variable {Ω X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]

/-- Section measures of a measurable family of finite measures are jointly measurable in the family and the
section parameter (Dynkin induction over measurable rectangles). -/
theorem measurable_sectionMeasure_of_finite {ν : Ω → Measure X} (hν : Measurable ν)
    (hfin : ∀ ω, IsFiniteMeasure (ν ω)) {W : Set (X × Y)} (hW : MeasurableSet W) :
    Measurable (fun p : Ω × Y => ν p.1 {x : X | (x, p.2) ∈ W}) := by
  have hfst : Measurable fun p : Ω × Y => ν p.1 := hν.comp measurable_fst
  have hsec : ∀ (t : Set (X × Y)), MeasurableSet t → ∀ y : Y, MeasurableSet {x : X | (x, y) ∈ t} :=
    fun t ht y => ht.preimage (measurable_id.prodMk measurable_const)
  let C : ∀ s : Set (X × Y), MeasurableSet s → Prop := fun s _ =>
    Measurable (fun p : Ω × Y => ν p.1 {x : X | (x, p.2) ∈ s})
  have key : ∀ (t : Set (X × Y)) (ht : MeasurableSet t), C t ht := by
    refine MeasurableSpace.induction_on_inter (C := C)
      (s := image2 (· ×ˢ ·) {A : Set X | MeasurableSet A} {B : Set Y | MeasurableSet B})
      generateFrom_prod.symm isPiSystem_prod ?_ ?_ ?_ ?_
    · show Measurable _
      have hz : (fun p : Ω × Y => ν p.1 {x : X | (x, p.2) ∈ (∅ : Set (X × Y))}) = fun _ => 0 := by
        funext p
        simp
      rw [hz]
      exact measurable_const
    · rintro t ⟨A, hA, B, hB, rfl⟩
      show Measurable _
      have heq : (fun p : Ω × Y => ν p.1 {x : X | (x, p.2) ∈ A ×ˢ B}) =
          (Prod.snd ⁻¹' B).indicator (fun p : Ω × Y => ν p.1 A) := by
        funext p
        by_cases hy : p.2 ∈ B <;> simp [Set.indicator, hy]
      rw [heq]
      exact ((Measure.measurable_coe hA).comp hfst).indicator (measurable_snd hB)
    · intro t ht hCt
      show Measurable _
      have hCt' : Measurable fun p : Ω × Y => ν p.1 {x : X | (x, p.2) ∈ t} := hCt
      have heq : (fun p : Ω × Y => ν p.1 {x : X | (x, p.2) ∈ tᶜ}) =
          fun p : Ω × Y => ν p.1 Set.univ - ν p.1 {x : X | (x, p.2) ∈ t} := by
        funext p
        have := hfin p.1
        have hc : {x : X | (x, p.2) ∈ tᶜ} = {x : X | (x, p.2) ∈ t}ᶜ := by
          ext x; simp
        rw [hc, measure_compl (hsec t ht p.2) (measure_ne_top _ _)]
      rw [heq]
      exact ((Measure.measurable_coe MeasurableSet.univ).comp hfst).sub hCt'
    · intro f hdisj hfm hCf
      show Measurable _
      have heq : (fun p : Ω × Y => ν p.1 {x : X | (x, p.2) ∈ ⋃ i, f i}) =
          fun p : Ω × Y => ∑' i, ν p.1 {x : X | (x, p.2) ∈ f i} := by
        funext p
        have hU : {x : X | (x, p.2) ∈ ⋃ i, f i} = ⋃ i, {x : X | (x, p.2) ∈ f i} := by
          ext x; simp
        rw [hU, measure_iUnion]
        · intro i j hij
          exact Set.disjoint_left.mpr fun x hx hx' =>
            Set.disjoint_left.mp (hdisj hij) (show (x, p.2) ∈ f i from hx)
              (show (x, p.2) ∈ f j from hx')
        · intro i
          exact hsec (f i) (hfm i) p.2
      rw [heq]
      exact Measurable.tsum fun i => hCf i
  exact key W hW

end Dynkin

section Pieces

/-- The disjointed closed balls `S_n = closedBall 0 n \ ⋃_{k<n} closedBall 0 k`. -/
noncomputable def ballShell (n : ℕ) : Set ℂ :=
  disjointed (fun k : ℕ => closedBall (0 : ℂ) k) n

theorem measurableSet_ballShell (n : ℕ) : MeasurableSet (ballShell n) :=
  MeasurableSet.disjointed (fun _ : ℕ => measurableSet_closedBall) n

theorem ballShell_subset (n : ℕ) : ballShell n ⊆ closedBall (0 : ℂ) n :=
  disjointed_subset _ _

/-- The capped piece of `η` on the shell `S_n`; it is zero when `η(closedBall 0 n) = ∞`. -/
noncomputable def ballPiece (n : ℕ) (η : Measure ℂ) : Measure ℂ :=
  if η (closedBall (0 : ℂ) n) < ∞ then η.restrict (ballShell n) else 0

/-- The finite-valued part of `η`: the sum of its capped pieces on the shells. -/
noncomputable def finitePart (η : Measure ℂ) : Measure ℂ :=
  Measure.sum fun n : ℕ => ballPiece n η

theorem isFiniteMeasure_ballPiece (n : ℕ) (η : Measure ℂ) : IsFiniteMeasure (ballPiece n η) := by
  unfold ballPiece
  split_ifs with h
  · exact isFiniteMeasure_restrict.mpr
      (ne_top_of_le_ne_top h.ne (measure_mono (ballShell_subset n)))
  · infer_instance

theorem measurable_ballPiece (n : ℕ) : Measurable (ballPiece n) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have h : (fun η : Measure ℂ => ballPiece n η s) =
      fun η => if η (closedBall (0 : ℂ) n) < ∞ then η (s ∩ ballShell n) else 0 := by
    funext η
    unfold ballPiece
    by_cases hη : η (closedBall (0 : ℂ) n) < ∞
    · simp [hη, Measure.restrict_apply hs]
    · simp [hη]
  rw [h]
  exact Measurable.ite
    (measurableSet_lt (Measure.measurable_coe measurableSet_closedBall) measurable_const)
    (Measure.measurable_coe (hs.inter (measurableSet_ballShell n))) measurable_const

theorem finitePart_apply {η : Measure ℂ} {s : Set ℂ} (hs : MeasurableSet s) :
    finitePart η s = ∑' n : ℕ, ballPiece n η s := by
  unfold finitePart
  exact Measure.sum_apply _ hs

/-- On a locally finite measure, the finite part is the measure itself. -/
theorem finitePart_eq_of_locallyFinite (η : Measure ℂ) [IsLocallyFiniteMeasure η] :
    finitePart η = η := by
  ext s hs
  rw [finitePart_apply hs]
  have hpiece : ∀ n : ℕ, ballPiece n η s = η (s ∩ ballShell n) := by
    intro n
    unfold ballPiece
    simp [measure_closedBall_lt_top, Measure.restrict_apply hs]
  simp_rw [hpiece]
  have hdisj : Pairwise (Function.onFun Disjoint fun n : ℕ => s ∩ ballShell n) := fun i j hij =>
    (disjoint_disjointed (fun k : ℕ => closedBall (0 : ℂ) k) hij).mono
      inter_subset_right inter_subset_right
  rw [← measure_iUnion hdisj fun n => hs.inter (measurableSet_ballShell n)]
  congr 1
  rw [← Set.inter_iUnion]
  have hcover : (⋃ n : ℕ, ballShell n) = Set.univ := by
    unfold ballShell
    rw [iUnion_disjointed, Metric.iUnion_closedBall_nat]
  rw [hcover, Set.inter_univ]

end Pieces

section Recentred

/-- The set `{(x, z) : x ∈ B_r(z), x - z ∈ s}` whose sections give the recentred restriction. -/
def recentredSet (r : ℝ) (s : Set ℂ) : Set (ℂ × ℂ) :=
  {q | q.1 ∈ ball q.2 r ∧ q.1 - q.2 ∈ s}

theorem measurableSet_recentredSet (r : ℝ) {s : Set ℂ} (hs : MeasurableSet s) :
    MeasurableSet (recentredSet r s) := by
  have h1 : MeasurableSet {q : ℂ × ℂ | dist q.1 q.2 < r} :=
    measurableSet_lt (continuous_fst.dist continuous_snd).measurable measurable_const
  have h2 : MeasurableSet {q : ℂ × ℂ | q.1 - q.2 ∈ s} :=
    (measurable_fst.sub measurable_snd) hs
  exact h1.inter h2

theorem recenteredRestriction_apply (η : Measure ℂ) (r : ℝ) (z : ℂ) {s : Set ℂ}
    (hs : MeasurableSet s) :
    recenteredRestriction η r z s = η {x : ℂ | (x, z) ∈ recentredSet r s} := by
  unfold recenteredRestriction
  rw [Measure.map_apply (measurable_sub_const z) hs,
    Measure.restrict_apply ((measurable_sub_const z) hs)]
  congr 1
  ext x
  simp [recentredSet, mem_ball, and_comm]

theorem measurable_restrict_set (s : Set ℂ) (hs : MeasurableSet s) :
    Measurable fun η : Measure ℂ => η.restrict s := by
  apply Measure.measurable_of_measurable_coe
  intro t ht
  simp only [Measure.restrict_apply ht]
  exact Measure.measurable_coe (ht.inter hs)

theorem measurable_massNormalize (r : ℝ) : Measurable (massNormalize r) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have h : (fun η : Measure ℂ => massNormalize r η s) =
      fun η => (η (ball 0 (r / 2)))⁻¹ * η s := by
    funext η
    simp [massNormalize, Measure.smul_apply, smul_eq_mul]
  rw [h]
  exact ((Measure.measurable_coe measurableSet_ball).inv).mul
    (Measure.measurable_coe hs)

/-- Sections of the finite part of a measurable family, jointly measurable. -/
theorem measurable_finitePart_section {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Ω' → Measure ℂ}
    (hμ' : Measurable μ') {W : Set (ℂ × ℂ)} (hW : MeasurableSet W) :
    Measurable (fun p : Ω' × ℂ => finitePart (μ' p.1) {x : ℂ | (x, p.2) ∈ W}) := by
  have hpiece : ∀ n : ℕ,
      Measurable (fun p : Ω' × ℂ => ballPiece n (μ' p.1) {x : ℂ | (x, p.2) ∈ W}) :=
    fun n => measurable_sectionMeasure_of_finite ((measurable_ballPiece n).comp hμ')
      (fun ω => isFiniteMeasure_ballPiece n (μ' ω)) hW
  have hsec : ∀ p : Ω' × ℂ, MeasurableSet {x : ℂ | (x, p.2) ∈ W} := fun p =>
    hW.preimage (measurable_id.prodMk measurable_const)
  have heq : (fun p : Ω' × ℂ => finitePart (μ' p.1) {x : ℂ | (x, p.2) ∈ W}) =
      fun p => ∑' n : ℕ, ballPiece n (μ' p.1) {x : ℂ | (x, p.2) ∈ W} := by
    funext p
    exact finitePart_apply (hsec p)
  rw [heq]
  exact Measurable.tsum fun n => hpiece n

theorem measurable_recentred_finitePart (r : ℝ) :
    Measurable (fun p : Measure ℂ × ℂ => recenteredRestriction (finitePart p.1) r p.2) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have heq : (fun p : Measure ℂ × ℂ => recenteredRestriction (finitePart p.1) r p.2 s) =
      fun p => finitePart p.1 {x : ℂ | (x, p.2) ∈ recentredSet r s} := by
    funext p
    exact recenteredRestriction_apply _ r _ hs
  rw [heq]
  exact measurable_finitePart_section measurable_id (measurableSet_recentredSet r hs)

/-- The recentred normalised output of the local observation, as a function of the measure and the root. -/
noncomputable def recentredOutput (r : ℝ) (p : Measure ℂ × ℂ) : ℂ × Measure ℂ :=
  (p.2, massNormalize r (recenteredRestriction (finitePart p.1) r p.2))

theorem measurable_recentredOutput (r : ℝ) : Measurable (recentredOutput r) :=
  measurable_snd.prodMk ((measurable_massNormalize r).comp (measurable_recentred_finitePart r))

end Recentred

section Observations

/-- The root observation is almost surely measurable under the rooted law. -/
theorem aemeasurable_localRootObservation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (κ : Kernel Ω ℂ) (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω)) (j : ℕ) (D : Set ℂ) :
    AEMeasurable (localRootObservation μ j) ((P ⊗ₘ κ).restrict (Prod.snd ⁻¹' D)) := by
  set μ' := hμ.mk μ with hμ'def
  have hμ'm : Measurable μ' := hμ.measurable_mk
  have hae : ∀ᵐ ω ∂P, μ ω = μ' ω ∧ IsLocallyFiniteMeasure (μ ω) :=
    hμ.ae_eq_mk.and hloc
  have hae2 := ae_fst_of_ae_compProd P κ
    (p := fun ω => μ ω = μ' ω ∧ IsLocallyFiniteMeasure (μ ω)) hae
  have hae3 := ae_restrict_of_ae (s := Prod.snd ⁻¹' D) hae2
  have hO' : Measurable (fun x : Ω × ℂ => recentredOutput (localRadius j) (μ' x.1, x.2)) :=
    (measurable_recentredOutput _).comp ((hμ'm.comp measurable_fst).prodMk measurable_snd)
  refine hO'.aemeasurable.congr ?_
  filter_upwards [hae3] with x hx
  obtain ⟨h1, h2⟩ := hx
  have key : finitePart (μ' x.1) = μ' x.1 := by
    rw [← h1]
    exact finitePart_eq_of_locallyFinite (μ x.1)
  simp only [recentredOutput, localRootObservation, key, h1]

/-- The reference observation is measurable under the product of the restricted root Lebesgue measure and `P`. -/
theorem aemeasurable_localReferenceObservation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [SFinite P] (ν : Ω → Measure ℂ) (hν : AEMeasurable ν P) (j : ℕ) (D : Set ℂ) :
    AEMeasurable (localReferenceObservation ν j) ((volume.restrict D).prod P) := by
  have hF : AEMeasurable
      (fun ω => massNormalize (localRadius j) ((ν ω).restrict (ball 0 (localRadius j)))) P :=
    ((measurable_massNormalize _).comp
      (measurable_restrict_set (ball 0 (localRadius j)) measurableSet_ball)).comp_aemeasurable hν
  exact (measurable_fst.aemeasurable).prodMk
    (hF.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)

end Observations

end HarmonicBalls
