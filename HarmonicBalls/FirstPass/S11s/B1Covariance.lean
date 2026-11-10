import HarmonicBalls.FirstPass.S11s.Covariance
import HarmonicBalls.FirstPass.S11s.Event
import HarmonicBalls.FirstPass.S11s.Uniqueness
import HarmonicBalls.FirstPass.S11s.Inverse
import HarmonicBalls.FirstPass.S11n
import HarmonicBalls.FirstPass.S11v.CovarianceDec

/-!
# B1: covariance of the canonical decoders under `dilOp` on a conull invariant set (fp-S11s-11-13-B1-covariance)

Ruling section 3, Proposition (eqs. (5)-(6)), with `T = dilOp`, `r = 1/2`, `S_r ν = ν.map (· / (1/2))`. For the frozen
canonical witnesses `K` (measure decoder), `d` (metric decoder) and `G` (the conull set of `LQGCanonicalDecodersMeasurableExistStmt`)
there is a measurable set `G0` of canonical fields with `P_α(G0) = 1`, `T⁻¹ G0 = G0`, and for every `L ∈ G0` constants
`a, b > 0` with `K (T L) = a • S_r (K L)` and `d (T L) (u, v) = b · d L (u/2, v/2)`.

Construction: the covariance event `covEvent` (`Event.lean`) intersected with `G` is measurable and, by the a.s. covariance on
realizations (`ae_covariance_canonical`, `Covariance.lean`), of full `P_α` measure. `G0` is the two-sided orbit intersection
`⋂_k T^[k]⁻¹ A ∩ ⋂_k S^[k]⁻¹ A` with `S = dilOpInv`; it is `T`-invariant (`dilOp_dilOpInv`, `dilOpInv_dilOp`) and
`P_α`-conull (`measurePreserving_dilOp_law`). On `G0` the measure covariance follows from the countable determining family
(`measure_ext_of_complex_pi`) and the metric covariance from a countable dense set (`Continuous.ext_on`).

Hypotheses: `hAff` (`WholePlaneGFFAffineInvariance`, caveat 1; to be derived as a theorem, P6 of operator note 01:44 UTC), and
the LQG measure `hμ` and metric `hD` of the model. No pathwise homogeneity `hhom` is used: the covariance of the decoders
is `ae_covariance_canonical_dec` (`S11v/CovarianceDec.lean`), which uses the coordinatewise identity
`ae_dilOp_alphaCanon_apply_eq` (`S11v/DilOpCoord.lean`) and the measurable-function principle
`ae_decoders_eq_of_coordwise_ae_eq` (`S11v/Decoders.lean`).
-/

namespace HarmonicBalls

open MeasureTheory Set Filter Topology Metric ProbabilityTheory
open scoped ENNReal

/-- The law `P_α` of the canonical field is invariant under the dual dilation `dilOp`. -/
theorem measurePreserving_dilOp_law {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {α : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc) :
    MeasurePreserving (dilOp : S11n.CanonSpace → S11n.CanonSpace) (P.map (alphaCanon α hC))
      (P.map (alphaCanon α hC)) := by
  have hcanon : Measurable (fun ω => fun i : {φ : ℂ → ℝ // IsTestFunction (univ : Set ℂ) φ ∧ ∫ x, φ x = 0} =>
      hC ω i.1) :=
    measurable_pi_iff.2 fun i => hG.measurable_pairing i.1 i.2.1
  have htr : Measurable (transl (logDrift α) : S11n.CanonSpace → S11n.CanonSpace) :=
    measurable_pi_iff.2 fun i => (measurable_pi_apply i).add_const _
  have hν : MeasurePreserving (dilOp : S11n.CanonSpace → S11n.CanonSpace)
      (P.map (fun ω => fun i : {φ : ℂ → ℝ // IsTestFunction (univ : Set ℂ) φ ∧ ∫ x, φ x = 0} => hC ω i.1))
      (P.map (fun ω => fun i : {φ : ℂ → ℝ // IsTestFunction (univ : Set ℂ) φ ∧ ∫ x, φ x = 0} => hC ω i.1)) :=
    measurePreserving_dilOp hG
  have hcomm : dilOp ∘ transl (logDrift α) = transl (logDrift α) ∘ dilOp :=
    funext fun L => dilOp_transl α L
  have hfun : alphaCanon α hC = transl (logDrift α) ∘
      (fun ω => fun i : {φ : ℂ → ℝ // IsTestFunction (univ : Set ℂ) φ ∧ ∫ x, φ x = 0} => hC ω i.1) :=
    funext fun ω => alphaCanon_eq α hC ω
  have hlaw : P.map (alphaCanon α hC)
      = (P.map (fun ω => fun i : {φ : ℂ → ℝ // IsTestFunction (univ : Set ℂ) φ ∧ ∫ x, φ x = 0} => hC ω i.1)).map
          (transl (logDrift α)) := by
    rw [hfun, ← Measure.map_map htr hcanon]
  rw [hlaw]
  refine ⟨measurable_dilOp, ?_⟩
  rw [Measure.map_map measurable_dilOp htr, hcomm, ← Measure.map_map htr measurable_dilOp, hν.map_eq]

/-- A measure-preserving map carries a.e. membership in a measurable set to a.e. membership of the image. -/
theorem ae_mem_of_preserve {X : Type} [MeasurableSpace X] {ν : Measure X} {F : X → X}
    (hF : MeasurePreserving F ν ν) {A : Set X} (hA : MeasurableSet A) (h : ∀ᵐ x ∂ν, x ∈ A) :
    ∀ᵐ x ∂ν, F x ∈ A := by
  have h1 : ∀ᵐ y ∂(ν.map F), y ∈ A := by
    rw [hF.map_eq]
    exact h
  exact (ae_map_iff hF.measurable.aemeasurable hA).1 h1

/-- Positive mass of balls for a measure with full support. -/
theorem ball_pos_of_support' {μ : Measure ℂ} (hμ : μ.support = univ) (r : ℝ) (hr : 0 < r) :
    0 < μ (ball 0 r) := by
  have h0 : (0 : ℂ) ∈ μ.support := by
    rw [hμ]
    exact mem_univ _
  exact (Measure.mem_support_iff_forall _).1 h0 _ (ball_mem_nhds 0 hr)

/-- The set `A = covEvent ∩ G` of realizations on which the measure and metric covariance hold with the explicit ratios. -/
def B1Event (K : Kernel S11n.CanonSpace ℂ) (d : S11n.CanonSpace → ContinuousMap (ℂ × ℂ) ℝ)
    (G : Set S11n.CanonSpace) (C : Set (Set ℂ)) (Q : Set (ℂ × ℂ)) : Set S11n.CanonSpace :=
  covEvent (fun L => K L) (fun L x y => d L (x, y)) C Q ∩ G

/-- The two-sided orbit intersection `⋂_k dilOp^[k]⁻¹' A ∩ ⋂_k dilOpInv^[k]⁻¹' A`. -/
def B1Orbit (A : Set S11n.CanonSpace) : Set S11n.CanonSpace :=
  (⋂ k : ℕ, dilOp^[k] ⁻¹' A) ∩ (⋂ k : ℕ, dilOpInv^[k] ⁻¹' A)

theorem mem_B1Orbit {A : Set S11n.CanonSpace} {L : S11n.CanonSpace} :
    L ∈ B1Orbit A ↔ (∀ k : ℕ, dilOp^[k] L ∈ A) ∧ (∀ k : ℕ, dilOpInv^[k] L ∈ A) := by
  constructor
  · intro h
    exact ⟨fun k => mem_iInter.1 h.1 k, fun k => mem_iInter.1 h.2 k⟩
  · intro h
    exact ⟨mem_iInter.2 fun k => h.1 k, mem_iInter.2 fun k => h.2 k⟩

/-- The two-sided orbit intersection is invariant under `dilOp`. -/
theorem preimage_B1Orbit (A : Set S11n.CanonSpace) : dilOp ⁻¹' B1Orbit A = B1Orbit A := by
  ext L
  rw [mem_preimage, mem_B1Orbit, mem_B1Orbit]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun k => ?_, fun k => ?_⟩
    · cases k with
      | zero => simpa [dilOpInv_dilOp] using h2 1
      | succ k => rw [Function.iterate_succ_apply]; exact h1 k
    · have h := h2 (k + 1)
      rw [Function.iterate_succ_apply, dilOpInv_dilOp] at h
      exact h
  · rintro ⟨h1, h2⟩
    refine ⟨fun k => ?_, fun k => ?_⟩
    · have h := h1 (k + 1)
      rw [Function.iterate_succ_apply] at h
      exact h
    · cases k with
      | zero => simpa using h1 1
      | succ k => rw [Function.iterate_succ_apply, dilOpInv_dilOp]; exact h2 k

/-- **B1 (covariance of the canonical decoders under `dilOp`).** Given the frozen witnesses `K`, `d`, `G` of the
measurable canonical decoders (`LQGCanonicalDecodersMeasurableExistStmt`, clauses 1-4 for the model), there is a measurable
`G0` of canonical fields, of full `P_α` measure, invariant under `dilOp`, on which `K` and `d` are covariant under the
dilation by `1/2`. The range hypotheses `γ < 2`, `α < Q_γ` are the frozen setting (not used by the argument). -/
theorem B1_covariance {γ ξ α : ℝ} (hγ0 : 0 < γ) (_hγ2 : γ < 2) (_hα : α < lqgQ γ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    {D : Ω → ℂ → ℂ → ℝ} (hD : IsLQGMetricOfField P γ ξ α hC D)
    (K : Kernel S11n.CanonSpace ℂ) (d : S11n.CanonSpace → ContinuousMap (ℂ × ℂ) ℝ) (hd : Measurable d)
    (hKf : ∀ L, IsFiniteMeasureOnCompacts (K L))
    (hid : S11n.LQGCanonicalIdentificationStmt.{0} γ ξ α (fun L => K L) (fun L x y => d L (x, y)))
    (G : Set S11n.CanonSpace) (hGm : MeasurableSet G) (hGa : ∀ᵐ ω ∂P, alphaCanon α hC ω ∈ G)
    (hGs : ∀ L ∈ G, (K L).support = univ ∧ IsEuclideanLengthMetric (fun x y => d L (x, y))) :
    ∃ G0 : Set S11n.CanonSpace, MeasurableSet G0 ∧ (∀ᵐ ω ∂P, alphaCanon α hC ω ∈ G0) ∧
      dilOp ⁻¹' G0 = G0 ∧
      ∀ L ∈ G0, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
        K (dilOp L) = ENNReal.ofReal a • (K L).map (fun w : ℂ => w / ((1 / 2 : ℝ) : ℂ)) ∧
        ∀ u v : ℂ, d (dilOp L) (u, v) = b * d L (((1 / 2 : ℝ) : ℂ) * u, ((1 / 2 : ℝ) : ℂ) * v) := by
  obtain ⟨C, hCc, hpi, hgen, B, hB, hcov, hcpt⟩ := exists_countable_pi_system_complex
  obtain ⟨Q, hQc, hQd⟩ := TopologicalSpace.exists_countable_dense (ℂ × ℂ)
  have hCm : ∀ S ∈ C, MeasurableSet S := fun S hS => by
    have h := MeasurableSpace.measurableSet_generateFrom hS
    rw [hgen] at h
    exact h
  have hdd : ∀ x y : ℂ, Measurable fun L => d L (x, y) := fun x y =>
    (ContinuousMap.measurable_eval (x, y)).comp hd
  have hAm : MeasurableSet (B1Event K d G C Q) :=
    (measurableSet_covEvent K (fun L x y => d L (x, y)) hdd hCc hCm hQc).inter hGm
  -- a.s. membership of the canonical field in `A`
  have hAae : ∀ᵐ ω ∂P, alphaCanon α hC ω ∈ B1Event K d G C Q := by
    filter_upwards [ae_covariance_canonical_dec P hγ0 hG hAff hμ hD K hKf d hd hid, hGa] with ω hω hGω
    obtain ⟨a, b, ha, hb, hT, hDb⟩ := hω
    have hT' : K (dilOp (alphaCanon α hC ω))
        = ENNReal.ofReal a • (K (alphaCanon α hC ω)).map (fun w : ℂ => w / ((1 / 2 : ℝ) : ℂ)) := hT
    have hDb' : ∀ u v : ℂ, d (dilOp (alphaCanon α hC ω)) (u, v)
        = b * d (alphaCanon α hC ω) (((1 / 2 : ℝ) : ℂ) * u, ((1 / 2 : ℝ) : ℂ) * v) := hDb
    obtain ⟨hsupp, hlen⟩ := hGs _ hGω
    have hpos : 0 < K (alphaCanon α hC ω) (ball 0 (1 / 2)) := ball_pos_of_support' hsupp _ (by norm_num)
    have hfin : K (alphaCanon α hC ω) (ball 0 (1 / 2)) < ∞ := by
      have := hKf (alphaCanon α hC ω)
      exact measure_ball_lt_top' _ _
    have hcovA := covA_eq_of_smul hpos hfin hT'
    have hX : 0 < d (alphaCanon α hC ω) (0, ((1 / 2 : ℝ) : ℂ)) :=
      euclideanLength_pos hlen (by norm_num)
    have hcovB : covB (fun L x y => d L (x, y)) (alphaCanon α hC ω) = b := by
      unfold covB
      show d (dilOp (alphaCanon α hC ω)) (0, 1) / d (alphaCanon α hC ω) (0, ((1 / 2 : ℝ) : ℂ)) = b
      have h01 := hDb' 0 1
      rw [mul_zero, mul_one] at h01
      rw [h01, mul_div_assoc, div_self hX.ne', mul_one]
    refine ⟨mem_covEvent.2 ⟨fun S _ => ?_, fun q _ => ?_⟩, hGω⟩
    · rw [hcovA, hT', Measure.smul_apply, smul_eq_mul]
    · rw [hcovB]
      exact hDb' q.1 q.2
  -- law-level invariance of `P_α` under `dilOp` and its inverse
  have hTinv := measurePreserving_dilOp_law P (α := α) hG
  have hmeasα : Measurable (alphaCanon α hC) := by
    refine measurable_pi_iff.2 fun i => ?_
    exact (hG.measurable_pairing i.1 i.2.1).sub_const (α * ∫ x, i.1 x * Real.log ‖x‖)
  have hTe : MeasurePreserving (dilOpEquiv : S11n.CanonSpace ≃ᵐ S11n.CanonSpace)
      (P.map (alphaCanon α hC)) (P.map (alphaCanon α hC)) := hTinv
  have hSinv : MeasurePreserving (dilOpInv : S11n.CanonSpace → S11n.CanonSpace)
      (P.map (alphaCanon α hC)) (P.map (alphaCanon α hC)) := hTe.symm
  have hA' : ∀ᵐ x ∂(P.map (alphaCanon α hC)), x ∈ B1Event K d G C Q :=
    (ae_map_iff hmeasα.aemeasurable hAm).2 hAae
  have hall : ∀ᵐ x ∂(P.map (alphaCanon α hC)),
      ∀ k : ℕ, dilOp^[k] x ∈ B1Event K d G C Q ∧ dilOpInv^[k] x ∈ B1Event K d G C Q := by
    rw [ae_all_iff]
    intro k
    exact (ae_mem_of_preserve (hTinv.iterate k) hAm hA').and (ae_mem_of_preserve (hSinv.iterate k) hAm hA')
  have hG0m : MeasurableSet (B1Orbit (B1Event K d G C Q)) :=
    (MeasurableSet.iInter fun k => (measurable_dilOp.iterate k) hAm).inter
      (MeasurableSet.iInter fun k => (measurable_dilOpInv.iterate k) hAm)
  have hG0ae : ∀ᵐ ω ∂P, alphaCanon α hC ω ∈ B1Orbit (B1Event K d G C Q) := by
    have h : ∀ᵐ x ∂(P.map (alphaCanon α hC)), x ∈ B1Orbit (B1Event K d G C Q) := by
      filter_upwards [hall] with x hx
      exact mem_B1Orbit.2 ⟨fun k => (hx k).1, fun k => (hx k).2⟩
    exact (ae_map_iff hmeasα.aemeasurable hG0m).1 h
  -- covariance on the orbit
  have hcovG0 : ∀ L ∈ B1Orbit (B1Event K d G C Q), ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      K (dilOp L) = ENNReal.ofReal a • (K L).map (fun w : ℂ => w / ((1 / 2 : ℝ) : ℂ)) ∧
      ∀ u v : ℂ, d (dilOp L) (u, v) = b * d L (((1 / 2 : ℝ) : ℂ) * u, ((1 / 2 : ℝ) : ℂ) * v) := by
    intro L hL
    obtain ⟨hL0, -⟩ := mem_B1Orbit.1 hL
    have hLA : L ∈ B1Event K d G C Q := by simpa using hL0 0
    have hTA : dilOp L ∈ B1Event K d G C Q := by simpa using hL0 1
    obtain ⟨hLcov, hLG⟩ : L ∈ covEvent (fun L => K L) (fun L x y => d L (x, y)) C Q ∧ L ∈ G := hLA
    obtain ⟨-, hTG⟩ : dilOp L ∈ covEvent (fun L => K L) (fun L x y => d L (x, y)) C Q ∧ dilOp L ∈ G := hTA
    obtain ⟨hsuppL, hlenL⟩ := hGs L hLG
    obtain ⟨hsuppT, hlenT⟩ := hGs (dilOp L) hTG
    have := hKf (dilOp L)
    -- measure covariance on the countable family
    have hmeasEq : K (dilOp L) = covA (fun L => K L) L • (K L).map (fun w : ℂ => w / ((1 / 2 : ℝ) : ℂ)) := by
      refine measure_ext_of_complex_pi C hpi hgen B hB hcov hcpt (fun S hS => ?_)
      rw [Measure.smul_apply, smul_eq_mul]
      exact (mem_covEvent.1 hLcov).1 S hS
    have hpos1 : 0 < K (dilOp L) (ball 0 1) := ball_pos_of_support' hsuppT _ one_pos
    have hfin1 : K (dilOp L) (ball 0 1) < ∞ := measure_ball_lt_top' _ _
    have hpos2 : 0 < K L (ball 0 (1 / 2)) := ball_pos_of_support' hsuppL _ (by norm_num)
    have hfin2 : K L (ball 0 (1 / 2)) < ∞ := measure_ball_lt_top' _ _
    have hcovA0 : covA (fun L => K L) L ≠ 0 := (ENNReal.div_pos hpos1.ne' hfin2.ne).ne'
    have hcovAtop : covA (fun L => K L) L ≠ ∞ := (ENNReal.div_lt_top hfin1.ne hpos2.ne').ne
    have hbpos : 0 < ((covA (fun L => K L) L).toReal) := ENNReal.toReal_pos hcovA0 hcovAtop
    have hcovA_eq : covA (fun L => K L) L = ENNReal.ofReal (covA (fun L => K L) L).toReal :=
      (ENNReal.ofReal_toReal hcovAtop).symm
    have hmeas' : K (dilOp L) = ENNReal.ofReal (covA (fun L => K L) L).toReal
        • (K L).map (fun w : ℂ => w / ((1 / 2 : ℝ) : ℂ)) := by
      rw [hmeasEq, ← hcovA_eq]
    -- metric covariance on the countable dense set, then everywhere by continuity
    have hbpos' : 0 < covB (fun L x y => d L (x, y)) L := covB_pos hlenT hlenL
    have hmetric : ∀ u v : ℂ, d (dilOp L) (u, v) = covB (fun L x y => d L (x, y)) L
        * d L (((1 / 2 : ℝ) : ℂ) * u, ((1 / 2 : ℝ) : ℂ) * v) := by
      intro u v
      have hc1 : Continuous (fun p : ℂ × ℂ => d (dilOp L) p) := (d (dilOp L)).continuous
      have hc2 : Continuous (fun p : ℂ × ℂ => covB (fun L x y => d L (x, y)) L
          * d L (((1 / 2 : ℝ) : ℂ) * p.1, ((1 / 2 : ℝ) : ℂ) * p.2)) :=
        continuous_const.mul ((d L).continuous.comp
          (Continuous.prodMk (continuous_const.mul continuous_fst) (continuous_const.mul continuous_snd)))
      have heq : EqOn (fun p : ℂ × ℂ => d (dilOp L) p)
          (fun p : ℂ × ℂ => covB (fun L x y => d L (x, y)) L
            * d L (((1 / 2 : ℝ) : ℂ) * p.1, ((1 / 2 : ℝ) : ℂ) * p.2)) Q :=
        fun q hq => (mem_covEvent.1 hLcov).2 q hq
      exact congrFun (Continuous.ext_on hQd hc1 hc2 heq) (u, v)
    exact ⟨(covA (fun L => K L) L).toReal, covB (fun L x y => d L (x, y)) L, hbpos, hbpos', hmeas', hmetric⟩
  exact ⟨B1Orbit (B1Event K d G C Q), hG0m, hG0ae, preimage_B1Orbit _, fun L hL => hcovG0 L hL⟩

end HarmonicBalls
