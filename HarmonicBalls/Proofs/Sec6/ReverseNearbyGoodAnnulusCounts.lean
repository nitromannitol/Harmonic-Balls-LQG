import HarmonicBalls.Proofs.Sec6.ReverseNearbyGoodAnnulus

/-! # Upper bounds for nearby good-annulus counts -/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter Metric MarkovProcess
open scoped ENNReal NNReal Topology

/-- A good nearby annulus transfers to the reference centre after strict
relaxation of both thresholds. -/
theorem exists_reverse_nearby_goodAnnulus
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] (z : ℂ)
    {r a a' b b' : ℝ} (hr : 0 < r)
    (hnull3 : μ (sphere z (3*r)) = 0) (hnull5 : μ (sphere z (5*r)) = 0)
    (hpos : 0 < μ (annulus z (3*r) (5*r)))
    (hfin : μ (annulus z (3*r) (5*r)) ≠ ∞)
    (ha' : 0 ≤ a') (ha : a' < a) (hb : 0 ≤ b) (hbb : b < b') :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℂ, dist w z < δ →
      IsGoodAnnulus μ r w a b → IsGoodAnnulus μ r z a' b' := by
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
  exact exists_reverse_nearby_goodAnnulus_of_slack μ z hr hnull3 hnull5 hpos hfin
    ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha').2 hmid)
    ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_trans ha' hmid.le)).2 hmida)
    (ENNReal.ofReal_pos.mpr he) hbudget

/-- One displacement radius transfers all good annuli in a finite collection
to the reference centre, after strict threshold relaxation. -/
theorem exists_reverse_nearby_goodAnnuli_finite
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] (z : ℂ) (R : Finset ℝ)
    {a a' b b' : ℝ} (ha' : 0 ≤ a') (ha : a' < a)
    (hb : 0 ≤ b) (hbb : b < b')
    (hR : ∀ r ∈ R, 0 < r ∧ μ (sphere z (3*r)) = 0 ∧
      μ (sphere z (5*r)) = 0 ∧ 0 < μ (annulus z (3*r) (5*r)) ∧
      μ (annulus z (3*r) (5*r)) ≠ ∞) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℂ, dist w z < δ → ∀ r ∈ R,
      IsGoodAnnulus μ r w a b → IsGoodAnnulus μ r z a' b' := by
  classical
  induction R using Finset.induction_on with
  | empty =>
      refine ⟨1, by norm_num, ?_⟩
      simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true]
  | @insert r R hrR ih =>
      obtain ⟨hr, h3, h5, hp, hf⟩ := hR r (Finset.mem_insert_self _ _)
      obtain ⟨δr, hδr, hgoodr⟩ := exists_reverse_nearby_goodAnnulus μ z hr h3 h5 hp hf
        ha' ha hb hbb
      have hRR : ∀ t ∈ R, 0 < t ∧ μ (sphere z (3*t)) = 0 ∧
          μ (sphere z (5*t)) = 0 ∧ 0 < μ (annulus z (3*t) (5*t)) ∧
          μ (annulus z (3*t) (5*t)) ≠ ∞ := by
        intro t ht
        exact hR t (Finset.mem_insert_of_mem ht)
      obtain ⟨δR, hδR, hgoodR⟩ := ih hRR
      refine ⟨min δr δR, lt_min hδr hδR, ?_⟩
      intro w hw t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact hgoodr w (hw.trans_le (min_le_left _ _))
      · exact hgoodR w (hw.trans_le (min_le_right _ _)) t ht

/-- The number of good radii at a nearby centre is bounded by the count at
the reference centre with strictly relaxed thresholds. -/
theorem exists_nearby_goodAnnuli_count_upper_bound
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] (z : ℂ) {S : Set ℝ} (hS : S.Finite)
    {a a' b b' : ℝ} (ha' : 0 ≤ a') (ha : a' < a)
    (hb : 0 ≤ b) (hbb : b < b')
    (hregular : ∀ r ∈ S, 0 < r ∧ μ (sphere z (3*r)) = 0 ∧
      μ (sphere z (5*r)) = 0 ∧ 0 < μ (annulus z (3*r) (5*r)) ∧
      μ (annulus z (3*r) (5*r)) ≠ ∞) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℂ, dist w z < δ →
      {r ∈ S | IsGoodAnnulus μ r w a b}.ncard ≤
        {r ∈ S | IsGoodAnnulus μ r z a' b'}.ncard := by
  classical
  have hregular' : ∀ r ∈ hS.toFinset, 0 < r ∧ μ (sphere z (3*r)) = 0 ∧
      μ (sphere z (5*r)) = 0 ∧ 0 < μ (annulus z (3*r) (5*r)) ∧
      μ (annulus z (3*r) (5*r)) ≠ ∞ := by
    intro r hr
    exact hregular r (hS.mem_toFinset.mp hr)
  obtain ⟨δ, hδ, hnear⟩ := exists_reverse_nearby_goodAnnuli_finite μ z hS.toFinset
    ha' ha hb hbb hregular'
  refine ⟨δ, hδ, ?_⟩
  intro w hw
  apply Set.ncard_le_ncard ?_ (hS.subset (by intro r hr; exact hr.1))
  intro r hr
  exact ⟨hr.1, hnear w hw r (hS.mem_toFinset.mpr hr.1) hr.2⟩

end HarmonicBalls.Section6
