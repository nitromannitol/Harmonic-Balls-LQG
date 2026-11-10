import HarmonicBalls.FirstPass.S11k.BundleParts
import HarmonicBalls.FirstPass.S11k.ExteriorPairings
import HarmonicBalls.FirstPass.S11k.ExteriorDistances
import HarmonicBalls.FirstPass.S11h.CorridorSup11_17
import HarmonicBalls.FirstPass.Frozen.S11g
import HarmonicBalls.FirstPass.S11t
import HarmonicBalls.FirstPass.S11u

/-!
# First pass, Section 11: the closed-corridor first conjunct `L` has an exterior version (fp-S11k, owner z3)

Proves `BundleParts.PinchFirstLExteriorStep` (the zero-mean exterior version of
`L = ⨆ x ∈ ∂B₅, internalMetric D (B_{2δ}(Q ∪ W))ᶜ 0 x`, Blocker 1 of `reports/z3.md`) from

* the FROZEN closed-domain identity `InternalMetricClosedEqIInfThickeningFrozen` (`FirstPass/Frozen/S11g.lean`,
  truth check TRUE), which writes the internal metric of a closed set as an infimum of suprema of internal metrics of
  open thickenings;
* item II (locality) of `LQGMetricFieldAxiomsUnivFrozen` on the open thickenings.

Route (as `FirstPass/S11h/CorridorSup11_17.lean`, with the open-set decoders replaced by exterior versions from
`ExteriorPairings.exists_exterior_iInf_internalMetric_version`):
* `F = (B_{2δ}(Q ∪ W))ᶜ` is closed, `0 ∈ F`, and `∂B₅ ⊆ O ⊆ F` for the open set `O = (closure B_{2δ}(Q ∪ W))ᶜ`
  (geometry from the buffer conditions `buffer_Q`, `W_subset`, `sphere_subset_closure_T`);
* for `N` with `1/(N+1) < 2δ/3`, the open thickenings `B_{(k+N+1)⁻¹}(F ∩ B̄(0,n+1))` avoid `closure W`
  (`thickening_subset_compl_closure`); the supremum over `k` is unchanged by the shift `k ↦ k + N` (monotonicity);
* the sphere supremum reduces to a countable dense set `S ⊆ ∂B₅` (`iSup_sphere_eq_of_dense`).
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric Topology
open scoped ENNReal

universe u

namespace FirstLExterior

open BundleParts

/-- Geometry: every point of `Q ∪ W` is at distance greater than `1` from the origin. -/
theorem one_lt_dist_origin_of_mem {U V W T Q' Q : Set ℂ} {δ : ℝ} (hG : IsBufferedPinchGeometry U V W T Q' Q δ)
    {a : ℂ} (ha : a ∈ Q ∪ W) : 1 < dist a 0 := by
  rcases ha with haQ | haW
  · have hann : a ∈ annulus 0 4 5 := (hG.closure_Q_subset (subset_closure haQ)).1
    simp only [annulus, Set.mem_sdiff, Metric.mem_ball, Metric.mem_closedBall, not_le] at hann
    linarith [hann.2]
  · have hann : a ∈ annulus 0 1 2 := hG.W_subset haW
    simp only [annulus, Set.mem_sdiff, Metric.mem_ball, Metric.mem_closedBall, not_le] at hann
    exact hann.2

/-- Geometry: points of `∂B₅(0)` are at distance at least `3δ` from `Q ∪ W`. -/
theorem three_delta_le_dist_sphere {U V W T Q' Q : Set ℂ} {δ : ℝ} (hG : IsBufferedPinchGeometry U V W T Q' Q δ)
    {y : ℂ} (hy : y ∈ sphere (0 : ℂ) 5) {a : ℂ} (ha : a ∈ Q ∪ W) : 3 * δ ≤ dist y a := by
  have hδ0 : 0 < δ := hG.delta_pos
  have hδ1 : δ < 1 / 1000 := hG.delta_lt
  have hy0 : dist y 0 = 5 := mem_sphere.1 hy
  rcases ha with haQ | haW
  · by_contra h
    rw [not_le] at h
    have hq1 : a ∈ thickening (10 * δ) (closure Q) :=
      self_subset_thickening (by linarith) _ (subset_closure haQ)
    have hq2 := hG.buffer_Q (subset_closure hq1)
    have hq3 : a ∈ thickening (10 * δ) (closure T) :=
      mem_thickening_iff.2 ⟨y, hG.sphere_subset_closure_T hy, by rw [dist_comm]; linarith⟩
    exact hq2.2 hq3
  · have hann : a ∈ annulus 0 1 2 := hG.W_subset haW
    simp only [annulus, Set.mem_sdiff, Metric.mem_ball, Metric.mem_closedBall, not_le] at hann
    have htri := dist_triangle y a 0
    linarith [hann.1]

/-- Deterministic: a thickening of a set `A` disjoint from `B_{2δ}(Q ∪ W)` with radius `ρ ≤ 2δ/3` avoids `closure W`. -/
theorem thickening_radius_subset_compl {Q W : Set ℂ} {δ ρ : ℝ}
    (hρ : 0 < ρ) (hρδ : ρ ≤ 2 * δ / 3) {A : Set ℂ} (hA : A ⊆ (thickening (2 * δ) (Q ∪ W))ᶜ) :
    thickening ρ A ⊆ (closure W)ᶜ := by
  refine ExteriorDistances.thickening_subset_compl_closure hρ fun x hx hxt => ?_
  have h2 : thickening (3 * ρ) W ⊆ thickening (2 * δ) (Q ∪ W) :=
    (thickening_mono (by linarith) W).trans (thickening_subset_of_subset _ subset_union_right)
  exact (mem_compl_iff _ _).1 (hA hx) (h2 hxt)

/-- Deterministic: the thickened radii `((k+1)⁻¹)` decrease in `k`, so the internal metric of the thickenings
increases in `k`. -/
theorem internalMetric_thickening_monotone (D : ℂ → ℂ → ℝ) (A : Set ℂ) (z w : ℂ) :
    Monotone (fun k : ℕ => internalMetric D (thickening (((k : ℝ) + 1)⁻¹) A) z w) := by
  intro k k' hkk'
  have hk : (k : ℝ) ≤ k' := by exact_mod_cast hkk'
  have hle : (((k' : ℝ) + 1)⁻¹) ≤ (((k : ℝ) + 1)⁻¹) := inv_anti₀ (by positivity) (by linarith)
  exact internalMetric_anti D (thickening_mono hle A) z w

/-- Deterministic: a supremum over `k` of a monotone sequence is unchanged by a shift of the index. -/
theorem iSup_shift_eq {f : ℕ → ℝ≥0∞} (hf : Monotone f) (N : ℕ) : ⨆ k, f (k + N) = ⨆ k, f k :=
  le_antisymm (iSup_le fun k => le_iSup f (k + N))
    (iSup_le fun k => (hf (Nat.le_add_right k N)).trans (le_iSup (fun j => f (j + N)) k))

/-- Exterior version of a single open-set internal metric value `internalMetric (D ω) V z w`, for an open `V ⊆ E`
containing `z`: if `w ∈ V` it is the infimum over `{z} × {w}` of Proposition-level item II (exterior version
`exists_exterior_iInf_internalMetric_version`); if `w ∉ V` no path lies in `V`, and the value is `⊤`. -/
theorem exists_exterior_internalMetric_pt
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (α₀ : ℝ) {E : Set ℂ} (hE : IsOpen E) (hsph : sphere (0 : ℂ) 1 ⊆ E)
    {D : Ω → ℂ → ℂ → ℝ} (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    {V : Set ℂ} (hV : IsOpen V) (hVE : V ⊆ E)
    (hII : ∃ G : Ω → ℂ → ℂ → ℝ≥0∞, (∀ z w, Measurable[fieldSigmaAlgebra α₀ hC V] fun ω => G ω z w) ∧
      ∀ᵐ ω ∂P, ∀ z ∈ V, ∀ w ∈ V, internalMetric (D ω) V z w = G ω z w)
    {z w : ℂ} (hz : z ∈ V) :
    ∃ Y : Ω → ℝ≥0∞, Measurable[MeasurableSpace.comap (localModConstPairings α₀ hC E) inferInstance] Y ∧
      ∀ᵐ ω ∂P, Y ω = internalMetric (D ω) V z w := by
  by_cases hw : w ∈ V
  · obtain ⟨Y, hYm, hYa⟩ := ExteriorPairings.exists_exterior_iInf_internalMetric_version hGFF α₀ hE hsph
      hmetric hV hVE hII (singleton_subset_iff.2 hz) (singleton_subset_iff.2 hw)
    refine ⟨Y, hYm, ?_⟩
    filter_upwards [hYa] with ω h
    simp only [iInf_singleton] at h
    exact h.symm
  · refine ⟨fun _ => ⊤, measurable_const, Filter.Eventually.of_forall fun ω => ?_⟩
    have hne : ∀ P : Path z w, ¬ (∀ t, P t ∈ V) := fun P hP => hw (by
      have h1 := hP 1
      rwa [P.target] at h1)
    show (⊤ : ℝ≥0∞) = internalMetric (D ω) V z w
    symm
    unfold internalMetric
    exact iInf_eq_top.2 fun P => iInf_eq_top.2 fun hP => absurd hP (hne P)

/-- OPEN step `PinchFirstLExteriorStep`, proved from the frozen closed-domain identity `hK1` and the item-II
locality of the metric axioms `hAx`. -/
theorem pinchFirstLExteriorStep_of_frozen
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) (hK1 : InternalMetricClosedEqIInfThickeningFrozen) :
    BundleParts.PinchFirstLExteriorStep.{u} := by
  have hb : WholePlaneCircleAverageLimitFrozen.{u} := wholePlaneCircleAverageLimit_derived.{u}
  intro U V W T Q' Q δ hG γ α₀ ξ hγ0 hγ2 hα Ω _ P hC hcirc D hGFF hD
  have hδ0 : 0 < δ := hG.delta_pos
  have hδ1 : δ < 1 / 1000 := hG.delta_lt
  have : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  obtain ⟨𝔇, h𝔇, hDae⟩ := hD
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
  -- the closed corridor `F = (B_{2δ}(Q ∪ W))ᶜ`
  obtain ⟨F, hF⟩ : ∃ F : Set ℂ, F = (thickening (2 * δ) (Q ∪ W))ᶜ := ⟨_, rfl⟩
  rw [← hF]
  have hFc : IsClosed F := by rw [hF]; exact isOpen_thickening.isClosed_compl
  have h0F : (0 : ℂ) ∈ F := by
    rw [hF, mem_compl_iff]
    intro h
    obtain ⟨a, ha, hda⟩ := mem_thickening_iff.1 h
    have h1 := one_lt_dist_origin_of_mem hG ha
    have h2 : dist 0 a = dist a 0 := dist_comm 0 a
    linarith
  have hOc : IsOpen (closure (thickening (2 * δ) (Q ∪ W)))ᶜ := isClosed_closure.isOpen_compl
  have hOF : (closure (thickening (2 * δ) (Q ∪ W)))ᶜ ⊆ F := by
    rw [hF]
    exact compl_subset_compl.2 subset_closure
  have hsph5 : sphere (0 : ℂ) 5 ⊆ (closure (thickening (2 * δ) (Q ∪ W)))ᶜ := by
    intro y hy
    rw [mem_compl_iff]
    intro hcl
    obtain ⟨b, hb', hyb⟩ := Metric.mem_closure_iff.1 hcl δ hδ0
    obtain ⟨a, ha, hba⟩ := mem_thickening_iff.1 hb'
    have h3 := three_delta_le_dist_sphere hG hy ha
    have htri := dist_triangle y b a
    linarith
  have hFsph : sphere (0 : ℂ) 5 ⊆ F := hsph5.trans hOF
  -- the shift `N` and the radii of the open thickenings
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (show (0 : ℝ) < 2 * δ / 3 by positivity)
  have hrad : ∀ k : ℕ, (((k + N : ℕ) : ℝ) + 1)⁻¹ ≤ 2 * δ / 3 := by
    intro k
    have hkN : ((N : ℝ) + 1) ≤ (((k + N : ℕ) : ℝ) + 1) := by
      push_cast
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    calc (((k + N : ℕ) : ℝ) + 1)⁻¹ ≤ ((N : ℝ) + 1)⁻¹ := inv_anti₀ (by positivity) hkN
      _ = 1 / ((N : ℝ) + 1) := (one_div _).symm
      _ ≤ 2 * δ / 3 := hN.le
  obtain ⟨Vn, hVn⟩ : ∃ Vn : ℕ → ℕ → Set ℂ, ∀ n k : ℕ,
      Vn n k = thickening ((((k + N : ℕ) : ℝ) + 1)⁻¹) (F ∩ closedBall (0 : ℂ) ((n : ℝ) + 1)) :=
    ⟨fun n k => thickening ((((k + N : ℕ) : ℝ) + 1)⁻¹) (F ∩ closedBall (0 : ℂ) ((n : ℝ) + 1)), fun _ _ => rfl⟩
  have hVopen : ∀ n k, IsOpen (Vn n k) := fun n k => by rw [hVn]; exact isOpen_thickening
  have h0V : ∀ n k, (0 : ℂ) ∈ Vn n k := fun n k => by
    rw [hVn]
    exact self_subset_thickening (by positivity) _ ⟨h0F, mem_closedBall_self (by positivity)⟩
  have hVE : ∀ n k, Vn n k ⊆ (closure W)ᶜ := fun n k => by
    rw [hVn]
    refine thickening_radius_subset_compl (Q := Q) (by positivity) (hrad k) ?_
    exact fun x hx => by rw [← hF]; exact hx.1
  have hE : IsOpen (closure W)ᶜ := isClosed_closure.isOpen_compl
  have hsph1 : sphere (0 : ℂ) 1 ⊆ (closure W)ᶜ := by
    intro z hz
    rw [mem_compl_iff]
    intro hzW
    have h1 := closure_W_norm_gt_one hG hzW
    rw [mem_sphere_zero_iff_norm] at hz
    linarith
  -- countable dense subset of the sphere, and the exterior versions
  obtain ⟨S, hSsph, hSc, hSd⟩ := exists_countable_subset_sphere_dense (5 : ℝ)
  have : Countable S := hSc.to_subtype
  choose Y hYm hYa using fun p : ℕ × ℕ × S =>
    exists_exterior_internalMetric_pt hGFF α₀ hE hsph1 hmetric (hVopen p.1 p.2.1) (hVE p.1 p.2.1)
      (hloc (Vn p.1 p.2.1) (hVopen p.1 p.2.1)) (z := 0) (w := (p.2.2 : ℂ)) (h0V p.1 p.2.1)
  refine ⟨fun ω => ⨆ y : S, ⨅ n : ℕ, ⨆ k : ℕ, Y (n, k, y) ω, ?_, ?_⟩
  · exact Measurable.iSup fun y => Measurable.iInf fun n => Measurable.iSup fun k => hYm (n, k, y)
  · have hall : ∀ᵐ ω ∂P, ∀ p : ℕ × ℕ × S, Y p ω = internalMetric (D ω) (Vn p.1 p.2.1) 0 (p.2.2 : ℂ) :=
      ae_all_iff.2 fun p => hYa p
    filter_upwards [hmetric, hall] with ω hω hωall
    have hpt : ∀ y : S, internalMetric (D ω) F 0 (y : ℂ) =
        ⨅ n : ℕ, ⨆ k : ℕ, internalMetric (D ω) (Vn n k) 0 (y : ℂ) := by
      intro y
      rw [hK1 (D ω) F hFc hω h0F (hFsph (hSsph y.2))]
      refine iInf_congr fun n => ?_
      refine (iSup_shift_eq (internalMetric_thickening_monotone (D ω) (F ∩ closedBall (0 : ℂ) ((n : ℝ) + 1))
        0 (y : ℂ)) N).symm.trans (iSup_congr fun k => ?_)
      simp only [hVn]
    have hYy : ∀ y : S, (⨅ n : ℕ, ⨆ k : ℕ, Y (n, k, y) ω) =
        ⨅ n : ℕ, ⨆ k : ℕ, internalMetric (D ω) (Vn n k) 0 (y : ℂ) :=
      fun y => iInf_congr fun n => iSup_congr fun k => hωall (n, k, y)
    have hfin : (⨆ y : S, ⨅ n : ℕ, ⨆ k : ℕ, Y (n, k, y) ω) = ⨆ y : S, internalMetric (D ω) F 0 (y : ℂ) :=
      iSup_congr fun y => by rw [hYy y, hpt y]
    show (⨆ y : S, ⨅ n : ℕ, ⨆ k : ℕ, Y (n, k, y) ω) = _
    rw [hfin]
    exact (iSup_subtype'' S _).trans (iSup_sphere_eq_of_dense hω hOc hOF hsph5 0 hSsph hSd).symm

/-- Lemma 11.16, corrected form, from the frozen closed-domain identity `hK1` and the item-II locality of the metric
axioms: the bundle now needs only the N2 step `PinchSecondAnnulusStep` (n4, task fp-S11t) as an explicit hypothesis;
`PinchFirstLExteriorStep` is no longer an input. -/
theorem firstPass_11_16_corrected_of_frozen (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hK1 : InternalMetricClosedEqIInfThickeningFrozen)
    (hS : BundleParts.PinchSecondAnnulusStep.{u}) (hPos : PinchFirstEventFaithfulStmt.{u})
    (hD : SmallMetricDiameterLargeMassStmt.{u}) (hM : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u}) (hMk : DomainMarkovConditionalPositiveFrozen.{u}) :
    PinchSecondEventFaithfulStmt.{u} :=
  BundleParts.firstPass_11_16_corrected_of_parts hAx (pinchFirstLExteriorStep_of_frozen hAx hK1) hS hPos hD
    hM hDiam hMk

end FirstLExterior

/-- Lemma 11.16, corrected form (`PinchSecondEventFaithfulStmt`, `FirstPass/S11h/Faithful.lean`). The bundle's open
parts are now proved: `PinchFirstLExteriorStep` (`FirstLExterior.pinchFirstLExteriorStep_of_frozen`, from the frozen
closed-domain identity `hK1`) and `PinchSecondAnnulusStep` (n4, `PinchSecondAnnulusS11t.pinchSecondAnnulusStep_of_N2_inputs`,
from its named inputs). Explicit hypotheses: the frozen inputs `hAx`, `hK1`, `hM`, `hDiam`, `hMk`; the Draft
statements `hPos` (Lemma 11.15) and `hD`; the N2 named inputs `hholder` (cited, Bou-Rabee-Gwynne Prop 2.5) and the
Proposed `hEx`, `hWeyl`, `hNa0`, `hNa`, pending operator source-check. -/
theorem firstPass_11_16_corrected (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hK1 : InternalMetricClosedEqIInfThickeningFrozen)
    (hholder : GreenPotentialHolderStmt.{u})
    (hEx : ∀ (γ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (hWeyl : ∀ (γ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hNa0 : ∀ (γ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ 0 hC hcirc)
    (hNa : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hPos : PinchFirstEventFaithfulStmt.{u}) (hD : SmallMetricDiameterLargeMassStmt.{u})
    (hM : LQGMassInnerMeasurableFrozen.{u}) (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
    (hMk : DomainMarkovConditionalPositiveFrozen.{u}) :
    PinchSecondEventFaithfulStmt.{u} :=
  FirstLExterior.firstPass_11_16_corrected_of_frozen hAx hK1
    (PinchSecondAnnulusS11t.pinchSecondAnnulusStep_of_N2_inputs hM hholder hEx hWeyl hNa0 hNa)
    hPos hD hM hDiam hMk

end HarmonicBalls
