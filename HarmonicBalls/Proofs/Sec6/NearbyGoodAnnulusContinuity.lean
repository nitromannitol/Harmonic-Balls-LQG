import HarmonicBalls.Proofs.Sec6.NearbyAnnulusCompactWitness

/-! # Stability of good annuli under displacement of the centre -/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter Metric MarkovProcess
open scoped ENNReal NNReal Topology

/-- A good annulus remains good at nearby centres after relaxing both thresholds.
The displacement is uniform over all measurable witnesses and starting points. -/
theorem exists_nearby_goodAnnulus_of_slack
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] (z : ℂ)
    {r a a' amid b b' : ℝ} (hr : 0 < r)
    (hnull3 : μ (sphere z (3 * r)) = 0) (hnull5 : μ (sphere z (5 * r)) = 0)
    (hpos : 0 < μ (annulus z (3 * r) (5 * r)))
    (hfin : μ (annulus z (3 * r) (5 * r)) ≠ ∞)
    (hamid : ENNReal.ofReal a' < ENNReal.ofReal amid)
    (haa : ENNReal.ofReal amid < ENNReal.ofReal a)
    (hg : IsGoodAnnulus μ r z a b) {ε : ℝ≥0∞} (hε : 0 < ε)
    (hbudget : ENNReal.ofReal b + 2 * ε + ε ≤ ENNReal.ofReal b') :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℂ, dist w z < δ → IsGoodAnnulus μ r w a' b' := by
  let A := annulus z (3 * r) (5 * r)
  let K : Set ℂ := {q | (7 / 2 : ℝ) * r ≤ dist q z ∧ dist q z ≤ (9 / 2 : ℝ) * r}
  have hKclosed : IsClosed K := by
    exact isClosed_le continuous_const (continuous_id.dist continuous_const) |>.inter
      (isClosed_le (continuous_id.dist continuous_const) continuous_const)
  have hK : IsCompact K := (isCompact_closedBall z ((9 / 2 : ℝ) * r)).of_isClosed_subset
    hKclosed (by intro q hq; exact mem_closedBall.mpr hq.2)
  have hKA : K ⊆ A := by
    intro q hq
    simp only [A, annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le]
    constructor <;> linarith [hq.1, hq.2]
  obtain ⟨η, δm, hδm, hδη, hmass⟩ :=
    exists_nearby_annulus_collar_witness_mass_transfer μ z (3*r) (5*r)
      hnull3 hnull5 hpos hfin hamid ENNReal.ofReal_ne_top
  have hη : 0 < η := hδm.trans hδη
  obtain ⟨δc, hδc, hcompare⟩ := exists_uniform_nearby_annulus_avoidance_comparison
    (z := z) (r := 3*r) (R := 5*r) (s := 3*r+η) (S := 5*r-η)
    (by positivity) (by linarith) (by linarith) (by linarith) hK hKA hε
  obtain ⟨δs, hδs, hstart⟩ := IsGoodAnnulus.uniform_avoidance_near_circle hr hfin hg hε
  let δ := min δm (min δc (min δs (r / 2)))
  refine ⟨δ, lt_min hδm (lt_min hδc (lt_min hδs (by positivity))), ?_⟩
  intro w hw Y hY hYsub hYmass u hu
  have hwm : dist w z < δm := hw.trans_le (min_le_left _ _)
  have hwc : dist w z < δc := hw.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hws : dist w z < δs := hw.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hwr : dist w z < r / 2 := hw.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hu' : dist u w = 4*r := mem_sphere.mp hu
  have hut := dist_triangle u w z
  have hwt := dist_triangle u z w
  have hdu : dist u z ≤ (9/2 : ℝ)*r := by linarith
  have hdl : (7/2 : ℝ)*r ≤ dist u z := by linarith [dist_comm z w]
  have huK : u ∈ K := ⟨hdl, hdu⟩
  let v := u + (z - w)
  have hvdist : dist v z = dist u w := by
    simp only [v, dist_eq_norm]
    change ‖u + (z - w) - z‖ = ‖u - w‖
    exact congrArg norm (show u + (z - w) - z = u - w by abel)
  have hv : v ∈ sphere z (4*r) := by rw [mem_sphere, hvdist, hu']
  have huv : dist u v = dist w z := by
    simp only [v, dist_eq_norm]
    change ‖u - (u + (z - w))‖ = ‖w - z‖
    exact congrArg norm (show u - (u + (z - w)) = w - z by abel)
  let C : Set ℂ := {q | 3*r+η ≤ dist q z ∧ dist q z ≤ 5*r-η}
  let X := (A ∩ Y) ∪ (A \ C)
  have hC : IsClosed C := by
    exact isClosed_le continuous_const (continuous_id.dist continuous_const) |>.inter
      (isClosed_le (continuous_id.dist continuous_const) continuous_const)
  have hA : MeasurableSet A := (isOpen_ball.sdiff isClosed_closedBall).measurableSet
  have hX : MeasurableSet X := (hA.inter hY).union (hA.diff hC.measurableSet)
  have hXA : X ⊆ A := by intro q hq; rcases hq with hq | hq <;> exact hq.1
  have hsub : X ⊆ (A ∩ Y) ∪ (A \ annulus z (3*r+η) (5*r-η)) := by
    intro q hq
    rcases hq with hq | ⟨hq, hn⟩
    · exact Or.inl hq
    · right; refine ⟨hq, ?_⟩
      intro hq'
      apply hn
      simp only [annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le] at hq'
      exact ⟨hq'.2.le, hq'.1.le⟩
  have hXm : μ X ≤ ENNReal.ofReal amid * μ A :=
    (measure_mono hsub).trans ((hmass w hwm).2 Y hYmass)
  have hXmlt : μ X < ENNReal.ofReal a * μ A :=
    hXm.trans_lt (ENNReal.mul_lt_mul_left hpos.ne' hfin haa)
  have hbound := hstart u v hv (by rw [huv]; exact hws) (hKA huK) X hX hXA hXmlt
  have hcomp := hcompare w hwc u huK Y
  calc
    _ ≤ _ + ε := hcomp
    _ ≤ (ENNReal.ofReal b + 2 * ε) + ε := add_le_add hbound le_rfl
    _ ≤ _ := hbudget

/-- Strict relaxation of the mass and avoidance thresholds gives a neighbourhood
of centres for which the annulus is good with the relaxed thresholds. -/
theorem exists_nearby_goodAnnulus
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] (z : ℂ)
    {r a a' b b' : ℝ} (hr : 0 < r)
    (hnull3 : μ (sphere z (3 * r)) = 0) (hnull5 : μ (sphere z (5 * r)) = 0)
    (hpos : 0 < μ (annulus z (3 * r) (5 * r)))
    (hfin : μ (annulus z (3 * r) (5 * r)) ≠ ∞)
    (ha' : 0 ≤ a') (ha : a' < a) (hb : 0 ≤ b) (hbb : b < b')
    (hg : IsGoodAnnulus μ r z a b) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℂ, dist w z < δ → IsGoodAnnulus μ r w a' b' := by
  let amid := (a' + a) / 2
  let e := (b' - b) / 4
  have he : 0 < e := by dsimp [e]; linarith
  have hmid : a' < amid := by dsimp [amid]; linarith
  have hmida : amid < a := by dsimp [amid]; linarith
  have he_budget : b + 2 * e + e ≤ b' := by dsimp [e]; linarith
  have hbudget : ENNReal.ofReal b + 2 * ENNReal.ofReal e + ENNReal.ofReal e ≤
      ENNReal.ofReal b' := by
    have he2 : 0 ≤ 2 * e := by positivity
    have hh : ENNReal.ofReal (b + 2*e + e) ≤ ENNReal.ofReal b' :=
      ENNReal.ofReal_le_ofReal he_budget
    rw [ENNReal.ofReal_add (add_nonneg hb he2) he.le,
      ENNReal.ofReal_add hb he2, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] at hh
    norm_num at hh ⊢
    exact hh
  exact exists_nearby_goodAnnulus_of_slack μ z hr hnull3 hnull5 hpos hfin
    ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha').2 hmid)
    ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_trans ha' hmid.le)).2 hmida)
    hg (ENNReal.ofReal_pos.mpr he) hbudget

/-- A finite collection of good radii remains good under one common
perturbation of the centre, after strict relaxation of the thresholds. -/
theorem exists_nearby_goodAnnuli_finite
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] (z : ℂ) (R : Finset ℝ)
    {a a' b b' : ℝ} (ha' : 0 ≤ a') (ha : a' < a)
    (hb : 0 ≤ b) (hbb : b < b')
    (hR : ∀ r ∈ R, 0 < r ∧ μ (sphere z (3*r)) = 0 ∧
      μ (sphere z (5*r)) = 0 ∧ 0 < μ (annulus z (3*r) (5*r)) ∧
      μ (annulus z (3*r) (5*r)) ≠ ∞ ∧ IsGoodAnnulus μ r z a b) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℂ, dist w z < δ →
      ∀ r ∈ R, IsGoodAnnulus μ r w a' b' := by
  classical
  induction R using Finset.induction_on with
  | empty =>
      refine ⟨1, by norm_num, ?_⟩
      simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true]
  | @insert r R hrR ih =>
      obtain ⟨hr, h3, h5, hp, hf, hg⟩ := hR r (Finset.mem_insert_self _ _)
      obtain ⟨δr, hδr, hgoodr⟩ := exists_nearby_goodAnnulus μ z hr h3 h5 hp hf
        ha' ha hb hbb hg
      have hRR : ∀ t ∈ R, 0 < t ∧ μ (sphere z (3*t)) = 0 ∧
          μ (sphere z (5*t)) = 0 ∧ 0 < μ (annulus z (3*t) (5*t)) ∧
          μ (annulus z (3*t) (5*t)) ≠ ∞ ∧ IsGoodAnnulus μ t z a b := by
        intro t ht
        exact hR t (Finset.mem_insert_of_mem ht)
      obtain ⟨δR, hδR, hgoodR⟩ := ih hRR
      refine ⟨min δr δR, lt_min hδr hδR, ?_⟩
      intro w hw t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact hgoodr w (hw.trans_le (min_le_left _ _))
      · exact hgoodR w (hw.trans_le (min_le_right _ _)) t ht

/-- The number of good radii in a finite window cannot decrease locally
when both thresholds are strictly relaxed. -/
theorem exists_nearby_goodAnnuli_count_lower_bound
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] (z : ℂ) {S : Set ℝ} (hS : S.Finite)
    {a a' b b' : ℝ} (ha' : 0 ≤ a') (ha : a' < a)
    (hb : 0 ≤ b) (hbb : b < b')
    (hregular : ∀ r ∈ S, IsGoodAnnulus μ r z a b →
      0 < r ∧ μ (sphere z (3*r)) = 0 ∧ μ (sphere z (5*r)) = 0 ∧
      0 < μ (annulus z (3*r) (5*r)) ∧ μ (annulus z (3*r) (5*r)) ≠ ∞) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℂ, dist w z < δ →
      {r ∈ S | IsGoodAnnulus μ r z a b}.ncard ≤
        {r ∈ S | IsGoodAnnulus μ r w a' b'}.ncard := by
  classical
  let T : Set ℝ := {r ∈ S | IsGoodAnnulus μ r z a b}
  have hT : T.Finite := hS.subset (by intro r hr; exact hr.1)
  have hregular' : ∀ r ∈ hT.toFinset, 0 < r ∧ μ (sphere z (3*r)) = 0 ∧
      μ (sphere z (5*r)) = 0 ∧ 0 < μ (annulus z (3*r) (5*r)) ∧
      μ (annulus z (3*r) (5*r)) ≠ ∞ ∧ IsGoodAnnulus μ r z a b := by
    intro r hr
    have hr' : r ∈ T := hT.mem_toFinset.mp hr
    obtain ⟨hrpos, h3, h5, hp, hf⟩ := hregular r hr'.1 hr'.2
    exact ⟨hrpos, h3, h5, hp, hf, hr'.2⟩
  obtain ⟨δ, hδ, hnear⟩ := exists_nearby_goodAnnuli_finite μ z hT.toFinset
    ha' ha hb hbb hregular'
  refine ⟨δ, hδ, ?_⟩
  intro w hw
  apply Set.ncard_le_ncard ?_ (hS.subset (by intro r hr; exact hr.1))
  intro r hr
  exact ⟨hr.1, hnear w hw r (hT.mem_toFinset.mpr hr)⟩

end HarmonicBalls.Section6
