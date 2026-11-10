import HarmonicBalls.FirstPass.S11k.FirstLExterior
import HarmonicBalls.FirstPass.S11h.CorridorSup11_17
import HarmonicBalls.FirstPass.S11h.SphereSup11_17
import HarmonicBalls.FirstPass.S11k.BundleParts

/-!
# Exterior version of the local sup `A = sup_{∂B₅} D(0, · ; Ω_geom)` (note §6.3, E1 outside W)

The sup of the internal metric over `∂B₅` on the open component `Ω_geom = pinchOmegaGeom W Q δ` has a version
measurable for the field outside `closure W`. Route (as in `FirstLExterior.pinchFirstLExteriorStep_of_frozen`):

* `internalMetric_eq_iInf_exhaustSet`: on an open `V`, the internal metric is the infimum over an open exhaustion
  `exhaustSet V r₀ p`, `p : ℕ × ℕ`, of the internal metrics of the open subsets `exhaustSet V r₀ p ⊆ V`;
* `exists_exterior_sup_sphere`: each internal metric on the exhaustion has an exterior version
  (`FirstLExterior.exists_exterior_internalMetric_pt`), and the sup over `∂B₅` reduces to a countable dense set
  (`iSup_sphere_eq_of_dense`, continuity of the internal metric on the open set `V`).

The only input is the locality of the metric axioms (item II of `LQGMetricFieldAxiomsUnivFrozen`), as in `FirstLExterior`.
-/

open MeasureTheory Filter Set Metric Topology
open scoped ENNReal

namespace HarmonicBalls
namespace S11ad

universe u

/-- Open exhaustion of an open set `V ∋ 0` (with `Vᶜ ≠ ∅`): the points at distance `> (k+1)⁻¹` from `Vᶜ` and of norm
`< n+1`, together with a fixed ball `B(0, r₀) ⊆ V` which keeps `0` inside every member. -/
def exhaustSet (V : Set ℂ) (r₀ : ℝ) (p : ℕ × ℕ) : Set ℂ :=
  {x | ((p.2 : ℝ) + 1)⁻¹ < Metric.infDist x Vᶜ ∧ ‖x‖ < (p.1 : ℝ) + 1} ∪ ball (0 : ℂ) r₀

lemma exhaustSet_isOpen (V : Set ℂ) (r₀ : ℝ) (p : ℕ × ℕ) : IsOpen (exhaustSet V r₀ p) :=
  ((isOpen_lt continuous_const (Metric.continuous_infDist_pt _)).inter
    (isOpen_lt continuous_norm continuous_const)).union isOpen_ball

lemma exhaustSet_subset {V : Set ℂ} {r₀ : ℝ} (hball : ball (0 : ℂ) r₀ ⊆ V) (p : ℕ × ℕ) :
    exhaustSet V r₀ p ⊆ V := by
  rintro x (⟨hx, -⟩ | hx)
  · by_contra hxV
    have h0 : Metric.infDist x Vᶜ = 0 := Metric.infDist_zero_of_mem hxV
    rw [h0] at hx
    have hpos : (0 : ℝ) < ((p.2 : ℝ) + 1)⁻¹ := by positivity
    linarith
  · exact hball hx

lemma exhaustSet_cover {V : Set ℂ} (hV : IsOpen V) (hVc : Vᶜ.Nonempty) {r₀ : ℝ}
    {K : Set ℂ} (hK : IsCompact K) (hKV : K ⊆ V) : ∃ p : ℕ × ℕ, K ⊆ exhaustSet V r₀ p := by
  obtain ⟨δ, hδ, hthick⟩ := hK.exists_thickening_subset_open hV hKV
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨N, hN⟩ := exists_nat_gt R
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
  have hk' : (((k : ℕ) : ℝ) + 1)⁻¹ < δ := by rw [← one_div]; exact hk
  refine ⟨(N, k), fun x hxK => Or.inl ⟨?_, ?_⟩⟩
  · show ((k : ℝ) + 1)⁻¹ < Metric.infDist x Vᶜ
    have hle : δ ≤ Metric.infDist x Vᶜ := by
      refine (Metric.le_infDist hVc).2 fun y hy => ?_
      by_contra hlt
      rw [not_le] at hlt
      have hyT : y ∈ thickening δ K := mem_thickening_iff.2 ⟨x, hxK, by rw [dist_comm]; exact hlt⟩
      exact hy (hthick hyT)
    exact lt_of_lt_of_le hk' hle
  · show ‖x‖ < (N : ℝ) + 1
    have h1 : ‖x‖ ≤ R := mem_closedBall_zero_iff.1 (hR hxK)
    linarith

/-- The internal metric of an open set is the infimum over the open exhaustion. -/
lemma internalMetric_eq_iInf_exhaustSet {D : ℂ → ℂ → ℝ} {V : Set ℂ} (hV : IsOpen V) (hVc : Vᶜ.Nonempty)
    {r₀ : ℝ} (hball : ball (0 : ℂ) r₀ ⊆ V) (z w : ℂ) :
    internalMetric D V z w = ⨅ p : ℕ × ℕ, internalMetric D (exhaustSet V r₀ p) z w := by
  apply le_antisymm
  · refine le_iInf fun p => ?_
    unfold internalMetric
    refine le_iInf fun P => le_iInf fun hP => ?_
    exact iInf₂_le P fun t => exhaustSet_subset hball p (hP t)
  · refine le_iInf₂ fun P hP => ?_
    obtain ⟨p, hp⟩ := exhaustSet_cover hV hVc (r₀ := r₀) (isCompact_range P.continuous)
      (by rintro _ ⟨t, rfl⟩; exact hP t)
    refine iInf_le_of_le p ?_
    unfold internalMetric
    exact iInf₂_le P fun t => hp ⟨t, rfl⟩

/-- Exterior version of the sup of the internal metric over `∂B₅` on an open set `V ∋ 0` containing `∂B₅`, from a
family of exterior versions `hloc` of the internal metric on open sets. -/
theorem exists_exterior_sup_sphere {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc) (α₀ : ℝ) {E : Set ℂ} (hE : IsOpen E)
    (hsph1 : sphere (0 : ℂ) 1 ⊆ E) {D : Ω → ℂ → ℂ → ℝ} (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hloc : ∀ V' : Set ℂ, IsOpen V' → ∃ G : Ω → ℂ → ℂ → ℝ≥0∞,
      (∀ z w, Measurable[fieldSigmaAlgebra α₀ hC V'] fun ω => G ω z w) ∧
        ∀ᵐ ω ∂P, ∀ z ∈ V', ∀ w ∈ V', internalMetric (D ω) V' z w = G ω z w)
    {V : Set ℂ} (hV : IsOpen V) (hVE : V ⊆ E) (hVc : Vᶜ.Nonempty) (h0 : (0 : ℂ) ∈ V)
    (hS5 : sphere (0 : ℂ) 5 ⊆ V) :
    ∃ Y : Ω → ℝ≥0∞, Measurable[MeasurableSpace.comap (localModConstPairings α₀ hC E) inferInstance] Y ∧
      ∀ᵐ ω ∂P, Y ω = ⨆ x ∈ sphere (0 : ℂ) 5, internalMetric (D ω) V 0 x := by
  obtain ⟨r₀, hr₀, hball⟩ := Metric.isOpen_iff.1 hV 0 h0
  obtain ⟨S, hSsph, hSc, hSd⟩ := exists_countable_subset_sphere_dense (5 : ℝ)
  have : Countable S := hSc.to_subtype
  have hsubE : ∀ p : ℕ × ℕ, exhaustSet V r₀ p ⊆ E := fun p => (exhaustSet_subset hball p).trans hVE
  have h0p : ∀ p : ℕ × ℕ, (0 : ℂ) ∈ exhaustSet V r₀ p := fun p => Or.inr (mem_ball_self hr₀)
  choose Yf hYm hYa using fun q : (ℕ × ℕ) × S =>
    FirstLExterior.exists_exterior_internalMetric_pt hGFF α₀ hE hsph1 hmetric
      (exhaustSet_isOpen V r₀ q.1) (hsubE q.1) (hloc _ (exhaustSet_isOpen V r₀ q.1))
      (z := 0) (w := (q.2 : ℂ)) (h0p q.1)
  refine ⟨fun ω => ⨆ y : S, ⨅ p : ℕ × ℕ, Yf (p, y) ω, ?_, ?_⟩
  · exact Measurable.iSup fun y => Measurable.iInf fun p => hYm (p, y)
  · have hall : ∀ᵐ ω ∂P, ∀ q : (ℕ × ℕ) × S,
        Yf q ω = internalMetric (D ω) (exhaustSet V r₀ q.1) 0 (q.2 : ℂ) :=
      ae_all_iff.2 fun q => hYa q
    filter_upwards [hmetric, hall] with ω hω hωall
    have hpt : ∀ y : S, (⨅ p : ℕ × ℕ, Yf (p, y) ω) = internalMetric (D ω) V 0 (y : ℂ) := fun y =>
      (iInf_congr fun p => hωall (p, y)).trans
        (internalMetric_eq_iInf_exhaustSet hV hVc hball 0 (y : ℂ)).symm
    show (⨆ y : S, ⨅ p : ℕ × ℕ, Yf (p, y) ω) = _
    calc (⨆ y : S, ⨅ p : ℕ × ℕ, Yf (p, y) ω) = ⨆ y : S, internalMetric (D ω) V 0 (y : ℂ) :=
          iSup_congr fun y => hpt y
      _ = ⨆ y ∈ S, internalMetric (D ω) V 0 y := iSup_subtype'' S _
      _ = ⨆ x ∈ sphere (0 : ℂ) 5, internalMetric (D ω) V 0 x :=
          (iSup_sphere_eq_of_dense hω hV subset_rfl hS5 0 hSsph hSd).symm

/-- `Ω_geom = pinchOmegaGeom W Q δ` is a connected component of an open set, hence open. -/
lemma isOpen_pinchOmegaGeom (W Q : Set ℂ) (δ : ℝ) : IsOpen (pinchOmegaGeom W Q δ) :=
  IsOpen.connectedComponentIn (isOpen_ball.sdiff (isClosed_closure.union isClosed_closure))

/-- `Ω_geom` lies in the ball `B₇(0)`. -/
lemma pinchOmegaGeom_subset_ball (W Q : Set ℂ) (δ : ℝ) : pinchOmegaGeom W Q δ ⊆ ball (0 : ℂ) 7 :=
  fun _ hx => (connectedComponentIn_subset _ _ hx).1

/-- `Ω_geom` avoids `closure W` (for `δ > 0`). -/
lemma pinchOmegaGeom_subset_compl_closure {W Q : Set ℂ} {δ : ℝ} (hδ : 0 < δ) :
    pinchOmegaGeom W Q δ ⊆ (closure W)ᶜ := by
  intro x hx hxW
  have h2 := (connectedComponentIn_subset _ _ hx).2
  exact h2 (Or.inr (closure_mono (self_subset_thickening (by positivity) W) hxW))

/-- Exterior version of the local sup `A` of `pinchFirstEventLocal` (note §6.3): `pinchLocalA (D ω) W Q δ` agrees almost
surely with a random variable measurable for the field outside `closure W`. The only input is the locality item II of
the metric axioms `hAx`, used through the derivation of `FirstLExterior.pinchFirstLExteriorStep_of_frozen`. -/
theorem pinchLocalA_exterior_version (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (U V W T Q' Q : Set ℂ) (δ : ℝ) (hG : IsBufferedPinchGeometry U V W T Q' Q δ)
    (γ ξ α₀ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ) (hGFF : IsWholePlaneGFF P hC hcirc) (hDm : IsLQGMetricOfField P γ ξ α₀ hC D)
    (hOmega : ({0} ∪ sphere (0 : ℂ) 5) ⊆ pinchOmegaGeom W Q δ) :
    ∃ Y : Ω → ℝ≥0∞, Measurable[MeasurableSpace.comap (localModConstPairings α₀ hC (closure W)ᶜ) inferInstance] Y ∧
      ∀ᵐ ω ∂P, Y ω = pinchLocalA (D ω) W Q δ := by
  have hδ0 : 0 < δ := hG.delta_pos
  have hE : IsOpen (closure W)ᶜ := isClosed_closure.isOpen_compl
  have hsph1 : sphere (0 : ℂ) 1 ⊆ (closure W)ᶜ := by
    intro z hz
    rw [mem_compl_iff]
    intro hzW
    have h1 := BundleParts.closure_W_norm_gt_one hG hzW
    rw [mem_sphere_zero_iff_norm] at hz
    linarith
  obtain ⟨𝔇, h𝔇, hDae⟩ := hDm
  obtain ⟨hI, hII, -, -⟩ := hAx Ω P γ ξ α₀ hC hcirc hGFF hγ0 hγ2 hα 𝔇 h𝔇
  have hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω) := by
    filter_upwards [hI, hDae] with ω h1 h2
    have hDeq : D ω = fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal := by
      funext u v
      have h3 := ENNReal.toReal_ofReal (h2 u v).1
      rw [(h2 u v).2] at h3
      exact h3.symm
    rw [hDeq]
    exact h1.2
  have hloc : ∀ V' : Set ℂ, IsOpen V' → ∃ G : Ω → ℂ → ℂ → ℝ≥0∞,
      (∀ z w, Measurable[fieldSigmaAlgebra α₀ hC V'] fun ω => G ω z w) ∧
        ∀ᵐ ω ∂P, ∀ z ∈ V', ∀ w ∈ V', internalMetric (D ω) V' z w = G ω z w := by
    intro V' hV'
    obtain ⟨G, hGm, hGa⟩ := hII V' hV'
    refine ⟨G, hGm, ?_⟩
    filter_upwards [hGa, hmetric, hDae] with ω h1 h2 h3
    have hDeq : D ω = fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal := by
      funext u v
      have h4 := ENNReal.toReal_ofReal (h3 u v).1
      rw [(h3 u v).2] at h4
      exact h4.symm
    rw [hDeq]
    exact h1
  have hV : IsOpen (pinchOmegaGeom W Q δ) := isOpen_pinchOmegaGeom W Q δ
  have hVE : pinchOmegaGeom W Q δ ⊆ (closure W)ᶜ := pinchOmegaGeom_subset_compl_closure hδ0
  have hVc : (pinchOmegaGeom W Q δ)ᶜ.Nonempty :=
    ⟨8, fun h => by
      have h1 := mem_ball_zero_iff.1 (pinchOmegaGeom_subset_ball W Q δ h)
      norm_num at h1⟩
  exact exists_exterior_sup_sphere hGFF α₀ hE hsph1 hmetric hloc hV hVE hVc (hOmega (Or.inl rfl))
    (fun x hx => hOmega (Or.inr hx))

end S11ad
end HarmonicBalls
