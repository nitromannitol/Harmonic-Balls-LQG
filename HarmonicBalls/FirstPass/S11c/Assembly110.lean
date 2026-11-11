import HarmonicBalls.FirstPass.S11c.AssemblyAux
import HarmonicBalls.FirstPass.S11c.ClassPigeon
import HarmonicBalls.FirstPass.S11c.EventBounds
import HarmonicBalls.FirstPass.S11c.ShiftBump
import HarmonicBalls.FirstPass.S11c.Conclusion
import HarmonicBalls.FirstPass.S11c.ShiftedEvent
import HarmonicBalls.FirstPass.S11c.ShiftedLength
import HarmonicBalls.FirstPass.S11c.PieceTranslate
import HarmonicBalls.FirstPass.S11c.ExteriorBound
import HarmonicBalls.FirstPass.S11c.MassPositive
import HarmonicBalls.FirstPass.S11c.Shifted
import HarmonicBalls.FirstPass.S11c.Finite
import HarmonicBalls.FirstPass.S11c.ClassClosed
import HarmonicBalls.FirstPass.S11c.ProbAssembly

/-!
# Proposition 11.10, the assembly of the shifted event

CONDITIONAL. The printed proof of `lemma:mass-diam` (paper lines 3071-3112) assembled from the lemmas of
`FirstPass/S11c/`: the square `S₁ ⊆ S₂` on a grid of mesh `2^{-(N+3)}`, the four parity classes of `S₁`, the piece event of
`DyadicCellDiamSmallFrozen`, the exterior bound, the Weyl shift by `a·φ`, and the Cameron-Martin transfer. The two
measurability premises `hM1`, `hM2` of the shifted event (blockers M1 and M2) are explicit hypotheses: this is
NOT a theorem until their source or frozen form is ruled.
-/

open MeasureTheory Set Filter Metric
open scoped ENNReal

namespace HarmonicBalls

universe u

theorem shifted_event_pos_11_10 {γ ξ α₀ : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hD : IsLQGMetricOfField P γ ξ α₀ hC D) (haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    {S₁ S₂ : Set ℂ} (hS₁ : IsClosedDyadicSquare S₁) (hS₂ : IsClosedDyadicSquare S₂) (hS12 : S₁ ⊆ S₂)
    (hdisj : Disjoint S₂ (sphere (0 : ℂ) 1)) {C ε : ℝ} (hε : 0 < ε) (hεC : ε < C)
    (hDC : DyadicCellDiamSmallFrozen.{u}) (hCM : CameronMartinEventTransferFrozen.{u})
    (hPos : LQGMeasureSquarePositiveFrozen.{u}) (hMassM : LQGMeasureSquareMeasurableFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u}) (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hW : WeylInternalClosedFrozen) (hFactI : LQGMetricContinuousShiftFactI.{u})
    (hM1 : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → (∀ z, f z ≤ 0) →
      AEMeasurable (fun ω => ⨆ u ∈ S₂, ⨆ v ∈ S₂,
        internalMetric (weylShiftPair γ ξ f (μ ω, D ω)).2 S₂ u v) P)
    (hM2 : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → (∀ z, f z ≤ 0) →
      AEMeasurable (fun ω => (weylShiftPair γ ξ f (μ ω, D ω)).1 S₁) P) :
    ∃ A ⊆ {ω | (∀ u ∈ S₂, ∀ v ∈ S₂, internalMetric (D ω) S₂ u v ≤ ENNReal.ofReal ε) ∧
      ENNReal.ofReal C ≤ μ ω S₁}, MeasurableSet A ∧ 0 < P A := by
  have hS₁c := hS₁
  have hS₂c := hS₂
  obtain ⟨m₁, J₁, K₁, e₁⟩ := hS₁c
  obtain ⟨m₂, J₂, K₂, e₂⟩ := hS₂c
  have hξ : 0 < ξ := by
    obtain ⟨𝔇, h𝔇, _⟩ := hD
    exact IsLQGMetric.weylExponent_pos h𝔇 hγ
  -- unshifted measurability and the mass event
  have hsupAE : AEMeasurable (fun ω => ⨆ u ∈ S₂, ⨆ v ∈ S₂, internalMetric (D ω) S₂ u v) P := by
    refine hSupM γ α₀ ξ hγ hγ₂ hα Ω P hC hcirc D hGFF hD S₂ ⟨{S₂}, ?_, ?_⟩
    · intro R hR
      rw [Finset.mem_singleton] at hR
      rw [hR, e₂]
      exact isClosedRectangle_closedDyadicSquare m₂ J₂ K₂
    · simp
  have hmassAE : AEMeasurable (fun ω => μ ω S₁) P :=
    hMassM γ α₀ hγ hγ₂ hα Ω P hC hcirc μ hGFF hμ S₁ hS₁
  have hpos : ∀ᵐ ω ∂P, 0 < μ ω S₁ :=
    hPos γ α₀ hγ hγ₂ hα Ω P hC hcirc μ hGFF hμ S₁ hS₁
  -- mass constant c = ofReal (C/2), so 2c = ofReal C
  have hc0 : 0 < ENNReal.ofReal (C / 2) := ENNReal.ofReal_pos.2 (by linarith)
  have hcfin : ENNReal.ofReal (C / 2) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hC2 : 2 * ENNReal.ofReal (C / 2) = ENNReal.ofReal C := two_mul_ofReal_half C
  set c : ℝ≥0∞ := ENNReal.ofReal (C / 2) with hc
  have h8c : 8 * c ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hcfin
  have h8pos : 0 < 8 * c := ENNReal.mul_pos (by norm_num) hc0.ne'
  have hmass0 : 0 < P {ω | 8 * c + 8 * c ≤ μ ω S₁} :=
    mass_event_pos_of_shift hγ hγ₂ hα hCM P hS₁ hS₂ hS12 hdisj hGFF hμ hD hsupAE hmassAE hpos
      (lt_of_lt_of_le h8pos le_add_self) (ENNReal.add_ne_top.2 ⟨h8c, h8c⟩)
  have hp0 : 0 < P {ω | 8 * c < μ ω S₁} :=
    lt_of_lt_of_le hmass0 (measure_mono (fun ω hω =>
      lt_of_lt_of_le (ENNReal.lt_add_right h8c h8pos.ne') hω))
  have hp₀t : P {ω | 8 * c < μ ω S₁} ≠ ⊤ := measure_ne_top P _
  have hp1 : (P {ω | 8 * c < μ ω S₁}).toReal ≤ 1 := by
    have := (ENNReal.toReal_le_toReal hp₀t ENNReal.one_ne_top).2 prob_le_one
    simpa using this
  set δ : ℝ := (P {ω | 8 * c < μ ω S₁}).toReal / 16 with hδdef
  have hδ : 0 < δ := div_pos (ENNReal.toReal_pos hp0.ne' hp₀t) (by norm_num)
  have hδ1 : δ ≤ 1 := by rw [hδdef]; linarith
  -- the piece event: uniform in the level N ≥ N0
  obtain ⟨N0, hN0⟩ := hDC γ α₀ ξ hγ hγ₂ hα Ω P hC hcirc D hGFF hD S₂ hS₂ hdisj (ε / 3) δ
    (by positivity) hδ
  set N : ℕ := N0 + m₁.toNat + m₂.toNat + 1 with hNdef
  have hN1 : m₁ + 4 ≤ (N : ℤ) + 3 := by
    have := Int.self_le_toNat m₁
    have := Int.self_le_toNat m₂
    omega
  have hN2 : m₂ + 4 ≤ (N : ℤ) + 3 := by
    have := Int.self_le_toNat m₁
    have := Int.self_le_toNat m₂
    omega
  have hS : closedDyadicSquare m₁ J₁ K₁ ⊆ closedDyadicSquare m₂ J₂ K₂ := by
    rw [← e₁, ← e₂]
    exact hS12
  -- the grid of mesh h = 2^{-(N+3)}
  obtain ⟨A₁, A₂, B₁, B₂, P₁, P₂, Q₁, Q₂, eS2, eS1, hP₁, hP₂, hQ₁, hQ₂, hPsz, hQsz,
    hAsz, hBsz, hA₁, hA₂, hB₁, hB₂⟩ :=
    exists_grid_of_closedDyadicSquare_subset (N := (N : ℤ)) hN1 hN2 hS
  set h : ℝ := (2 : ℝ) ^ (-((N : ℤ) + 3)) with hhdef
  have hh : 0 < h := by positivity
  have hS2eq : S₂ = gridBox h A₁ A₂ B₁ B₂ := by rw [e₂, eS2]
  have hS1eq : S₁ = gridBox h P₁ P₂ Q₁ Q₂ := by rw [e₁, eS1]
  -- the pieces at the level N
  obtain ⟨Apc, hApc_sub, hApc_m, hApc_P⟩ := hN0 N (by omega)
  -- the class choice
  have hcover : S₁ ⊆ ⋃ i : Fin 4, classFin4 h P₁ P₂ Q₁ Q₂ i := by
    rw [hS1eq]
    exact square_subset_iUnion_classFin4 hh hP₁ hP₂ hQ₁ hQ₂ hPsz hQsz
  obtain ⟨i, hi⟩ := exists_class_quarter_of_prob P μ (S := S₁)
    (C := classFin4 h P₁ P₂ Q₁ Q₂) (c := c) hcover
  have hq := two_mul_ofReal_lt_of_quarter hp0 hp₀t hi
  rw [two_mul] at hq
  -- class index sets and parities
  set Jx : Set ℤ := {j : ℤ | j % 2 = (((i : ℕ) / 2 : ℕ) : ℤ) ∧ P₁ ≤ 8 * j ∧ 8 * j + 8 ≤ P₂} with hJx
  set Jy : Set ℤ := {k : ℤ | k % 2 = (((i : ℕ) % 2 : ℕ) : ℤ) ∧ Q₁ ≤ 8 * k ∧ 8 * k + 8 ≤ Q₂} with hJy
  have hpi : (((i : ℕ) / 2 : ℕ) : ℤ) = 0 ∨ (((i : ℕ) / 2 : ℕ) : ℤ) = 1 := by
    have := i.isLt
    omega
  have hqi : (((i : ℕ) % 2 : ℕ) : ℤ) = 0 ∨ (((i : ℕ) % 2 : ℕ) : ℤ) = 1 := by
    have := i.isLt
    omega
  have hcls : classFin4 h P₁ P₂ Q₁ Q₂ i = gridClassCells h Jx Jy := rfl
  -- the exterior set
  have hK0 : IsPreconnected (gridK0 h Jx Jy A₁ A₂ B₁ B₂) :=
    isPreconnected_gridK0_class hh hpi hqi hP₁ hQ₁ hA₁ hA₂ hB₁ hB₂ hPsz hQsz hAsz hBsz
  obtain ⟨x0, hx0⟩ := gridK0_class_nonempty hh hpi hqi hP₁ hQ₁ hA₁ hA₂ hB₁ hB₂ hPsz hQsz hAsz hBsz
  have hconn : IsConnected (gridK1 h Jx Jy A₁ A₂ B₁ B₂) :=
    isConnected_gridK1 hh (by omega) (by omega) hK0 hx0
  obtain ⟨n, B, hBm, hBP, hBsub⟩ :=
    exists_measurable_exterior_bound hSupM hFin hγ hγ₂ hα P hC hcirc D hGFF hD
      (gridK1_finite_rect_union hh Jx Jy A₁ A₂ B₁ B₂) hconn (ENNReal.ofReal_pos.2 hδ)
  -- the shift
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (n : ℝ) + ε + 1 := ⟨_, rfl⟩
  have ha0 : 0 < a := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  obtain ⟨a', ha'⟩ : ∃ a' : ℝ, a' = -Real.log (3 * a / ε) / ξ := ⟨_, rfl⟩
  have h31 : 1 ≤ 3 * a / ε := by
    rw [le_div_iff₀ hε]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hlog : 0 ≤ Real.log (3 * a / ε) := Real.log_nonneg h31
  have ha'0 : a' ≤ 0 := by
    rw [ha']
    exact div_nonpos_iff.2 (Or.inr ⟨neg_nonpos.2 hlog, hξ.le⟩)
  have hKc : IsCompact (gridK1 h Jx Jy A₁ A₂ B₁ B₂) := isCompact_gridK1 hh Jx Jy A₁ A₂ B₁ B₂
  have hKsub : gridK1 h Jx Jy A₁ A₂ B₁ B₂ ⊆ S₂ := by
    rw [hS2eq]
    exact gridK1_subset_gridBox hh Jx Jy A₁ A₂ B₁ B₂
  have hFc : IsClosed (classFin4 h P₁ P₂ Q₁ Q₂ i ∪ sphere (0 : ℂ) 1) :=
    isClosed_classFin4_union_sphere (h := h) P₁ P₂ Q₁ Q₂ i
  have hKF : Disjoint (gridK1 h Jx Jy A₁ A₂ B₁ B₂) (classFin4 h P₁ P₂ Q₁ Q₂ i ∪ sphere (0 : ℂ) 1) :=
    disjoint_gridK1_classFin4_union_sphere hh i hKsub hdisj
  obtain ⟨f, hf1, hf2, hfF, hfK, hfr⟩ := exists_shift_const_on_zero hKc hFc hKF ha'0
  have hf0 : ∀ z ∈ classFin4 h P₁ P₂ Q₁ Q₂ i, f z = 0 := fun z hz => hfF z (Set.mem_union_left _ hz)
  have hf3 : ∀ z : ℂ, ‖z‖ = 1 → f z = 0 := fun z hz =>
    hfF z (Set.mem_union_right _ (mem_sphere_zero_iff_norm.2 hz))
  have hfP : ∀ z ∈ gridBox h A₁ A₂ B₁ B₂, ξ * f z ≤ 0 := fun z _ => by
    nlinarith [(hfr z).2, hξ]
  have e1' : ξ * a' = -Real.log (3 * a / ε) := by
    rw [ha']
    field_simp
  have e2' : Real.log (ε / (3 * a)) = -Real.log (3 * a / ε) := by
    rw [← Real.log_inv]
    congr 1
    field_simp
  have hfK' : ∀ z ∈ gridK1 h Jx Jy A₁ A₂ B₁ B₂, ξ * f z ≤ Real.log (ε / (3 * a)) := by
    intro z hz
    rw [hfK z hz, e1', e2']
  -- the good set of full measure
  have hDlAE := ae_isEuclideanLengthMetric_of_field haxioms hGFF hγ hγ₂ hα hD
  have hElAE := ae_isEuclideanLengthMetric_weylShift hFactI haxioms hGFF hγ hγ₂ hα hD hf1.continuous
  have hscaleAE := (ae_weylScaling_bddAbove_finite P γ ξ α₀ hC hcirc D haxioms hGFF hγ hγ₂ hα hD).mono
    (fun ω h => h f ⟨0, fun z => (hfr z).2⟩)
  have hGae : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω) ∧
      IsEuclideanLengthMetric (fun u v => (weylScaling (D ω) ξ f u v).toReal) ∧
      (∀ u v, ENNReal.ofReal ((weylScaling (D ω) ξ f u v).toReal) = weylScaling (D ω) ξ f u v) := by
    filter_upwards [hDlAE, hElAE, hscaleAE] with ω h1 h2 h3
    exact ⟨h1, h2, fun u v => (h3 u v).2⟩
  set G : Set Ω := {ω | IsEuclideanLengthMetric (D ω) ∧
      IsEuclideanLengthMetric (fun u v => (weylScaling (D ω) ξ f u v).toReal) ∧
      (∀ u v, ENNReal.ofReal ((weylScaling (D ω) ξ f u v).toReal) = weylScaling (D ω) ξ f u v)} with hGdef
  have hGc : P Gᶜ = 0 := ae_iff.1 hGae
  -- the pieces and the exterior bound
  have hcell : ∀ p ∈ (Jx ×ˢ Jy : Set (ℤ × ℤ)), closedDyadicSquare (N : ℤ) p.1 p.2 ⊆ S₂ := by
    rintro ⟨j, k⟩ ⟨hj, hk⟩
    rw [hJx] at hj
    rw [hJy] at hk
    obtain ⟨-, hj1, hj2⟩ := hj
    obtain ⟨-, hk1, hk2⟩ := hk
    rw [closedDyadicSquare_eq_gridBox_pow3, hS2eq]
    exact (gridBox_subset_gridBox_of_le hh (by norm_num; omega) (by norm_num; omega)
      (by norm_num; omega) (by norm_num; omega)).trans (gridBox_subset_gridBox_of_le hh hA₁ hA₂ hB₁ hB₂)
  have hDPω : ∀ ω ∈ Apc, ∀ p : (Jx ×ˢ Jy : Set (ℤ × ℤ)), ∀ u ∈ gridBlock h p.1.1 p.1.2 ∩ gridBox h A₁ A₂ B₁ B₂,
      ∀ v ∈ gridBlock h p.1.1 p.1.2 ∩ gridBox h A₁ A₂ B₁ B₂,
        internalMetric (D ω) (gridBlock h p.1.1 p.1.2 ∩ gridBox h A₁ A₂ B₁ B₂) u v ≤
          ENNReal.ofReal (ε / 3) := fun ω hω =>
    hDP_of_enlarged_pieces (N := (N : ℤ)) (h := h) (S₂ := S₂) (W := gridBox h A₁ A₂ B₁ B₂)
      hhdef hS2eq.symm hcell (hApc_sub hω)
  -- probabilities of the complements
  have hAc : P Apcᶜ ≤ ENNReal.ofReal δ :=
    prob_compl_le_ofReal_of_le P hApc_m hδ.le hδ1 hApc_P
  have hBc : P Bᶜ ≤ ENNReal.ofReal δ :=
    prob_compl_le_ofReal_of_le P hBm hδ.le hδ1
      (ofReal_one_sub_le_of_one_sub_lt hδ.le (hBP))
  have hsum : P Gᶜ + P Apcᶜ + P Bᶜ < P {ω | 2 * c < μ ω (classFin4 h P₁ P₂ Q₁ Q₂ i)} := by
    have h1 : P Gᶜ + P Apcᶜ + P Bᶜ ≤ ENNReal.ofReal δ + ENNReal.ofReal δ := by
      rw [hGc, zero_add]
      exact add_le_add hAc hBc
    have hq' : ENNReal.ofReal δ + ENNReal.ofReal δ < P {ω | 2 * c < μ ω (classFin4 h P₁ P₂ Q₁ Q₂ i)} := by
      exact hq
    exact lt_of_le_of_lt h1 hq'
  -- the shifted event
  have hTm : MeasurableSet (classFin4 h P₁ P₂ Q₁ Q₂ i) := by
    unfold classFin4
    exact (isClosed_gridClassCells_index _ _ _ _ _ _).measurableSet
  have hTS : classFin4 h P₁ P₂ Q₁ Q₂ i ⊆ S₁ := by
    rw [hS1eq]
    unfold classFin4
    exact gridClassCells_index_subset_square hh _ _ _ _ _ _
  have hsub : {ω | 2 * c < μ ω (classFin4 h P₁ P₂ Q₁ Q₂ i)} ∩ G ∩ Apc ∩ B ⊆
      {ω | (⨆ u ∈ S₂, ⨆ v ∈ S₂, internalMetric (weylShiftPair γ ξ f (μ ω, D ω)).2 S₂ u v) ≤
        ENNReal.ofReal ε ∧ ENNReal.ofReal C ≤ (weylShiftPair γ ξ f (μ ω, D ω)).1 S₁} := by
    intro ω hω
    have hωG : IsEuclideanLengthMetric (D ω) ∧
        IsEuclideanLengthMetric (fun u v => (weylScaling (D ω) ξ f u v).toReal) ∧
        (∀ u v, ENNReal.ofReal ((weylScaling (D ω) ξ f u v).toReal) = weylScaling (D ω) ξ f u v) :=
      hω.1.1.2
    -- the sup of the shifted metric on the box
    have hdet := shifted_sup_le_of_good hW hh hε ha0 hωG.1 hωG.2.1 (fun x y => ENNReal.toReal_nonneg)
      (fun x y => (hωG.2.2 x y)) hAsz hBsz
      (fun j hj j' hj' => by
        rw [hJx] at hj hj'
        exact hj'.1.trans hj.1.symm)
      (fun j hj => by
        rw [hJx] at hj
        obtain ⟨-, hj1, hj2⟩ := hj
        constructor <;> omega)
      (fun k hk => by
        rw [hJy] at hk
        obtain ⟨-, hk1, hk2⟩ := hk
        constructor <;> omega)
      hfP hfK' (fun p u hu v hv => hDPω ω hω.1.2 p u hu v hv)
      (fun u hu v hv => le_trans (hBsub hω.2 u hu v hv)
        (ENNReal.ofReal_le_ofReal (by rw [ha]; linarith)))
    have hsup : (⨆ u ∈ S₂, ⨆ v ∈ S₂, internalMetric (weylShiftPair γ ξ f (μ ω, D ω)).2 S₂ u v) ≤
        ENNReal.ofReal ε := by
      rw [hS2eq]
      exact iSup₂_internalMetric_le_iff.2 (fun u hu v hv => hdet u hu v hv)
    have hmass1 := mass_le_shifted_mass_of_zero_on (γ := γ) (ξ := ξ) (f := f) hTm hTS hf0 (μ ω) (D ω)
    have hmass : ENNReal.ofReal C ≤ (weylShiftPair γ ξ f (μ ω, D ω)).1 S₁ :=
      calc ENNReal.ofReal C = 2 * c := hC2.symm
        _ ≤ μ ω (classFin4 h P₁ P₂ Q₁ Q₂ i) := hω.1.1.1.le
        _ ≤ (weylShiftPair γ ξ f (μ ω, D ω)).1 S₁ := hmass1
    exact ⟨hsup, hmass⟩
  have hshiftpos : 0 < P {ω | (⨆ u ∈ S₂, ⨆ v ∈ S₂, internalMetric (weylShiftPair γ ξ f (μ ω, D ω)).2 S₂ u v) ≤
      ENNReal.ofReal ε ∧ ENNReal.ofReal C ≤ (weylShiftPair γ ξ f (μ ω, D ω)).1 S₁} :=
    pos_of_superset_good_inter P hsum hsub
  have hNM : NullMeasurableSet {ω | (⨆ u ∈ S₂, ⨆ v ∈ S₂,
      internalMetric (weylShiftPair γ ξ f (μ ω, D ω)).2 S₂ u v) ≤ ENNReal.ofReal ε ∧
      ENNReal.ofReal C ≤ (weylShiftPair γ ξ f (μ ω, D ω)).1 S₁} P :=
    (nullMeasurableSet_le (hM1 f hf1.continuous hf2 (fun z => (hfr z).2)) aemeasurable_const).inter
      (nullMeasurableSet_le aemeasurable_const (hM2 f hf1.continuous hf2 (fun z => (hfr z).2)))
  exact exists_measurable_of_cameronMartin_transfer hCM hγ hγ₂ hα f hf1 hf2 hf3 P hC hcirc μ D
    (ENNReal.ofReal ε) (ENNReal.ofReal C) hGFF hμ hD hS₁ hS₂ hsupAE hmassAE hNM hshiftpos

end HarmonicBalls
