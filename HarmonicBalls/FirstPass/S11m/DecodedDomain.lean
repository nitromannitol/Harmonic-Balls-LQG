import HarmonicBalls.FirstPass.S11m.DecodedRoot
import HarmonicBalls.FirstPass.S11m.DecodedClearance
import HarmonicBalls.FirstPass.S11m.DecodedRule
import HarmonicBalls.FirstPass.S11m.Finiteness
import HarmonicBalls.FirstPass.S11m.RootMin

/-!
# Decoded internal data on fixed domains (fp-S11m, owner z4)

Route `notes/fp-gaps/CHATGPT-z4-11-12-local-certificate.md` section 4.4 (root values, eqs (14)-(17)) and section 5.
For a fixed open set `V` (the punctured ball `X = B_R \ {0}`) and a decoded raw metric `Dh : ℂ → ℂ → ℝ`, this file defines

* `decPunct V Dh O x y`: the localized clearance infimum over the fixed countable sets `decChain O` (dense in `O`) and
  `decClear V O` (dense in `V \ O`); it is measurable in the pairing (`measurable_decPunct`);
* `decRoot V Dh ε O x`: the root value `D(0, x; O)` recovered from `O \ {0}` along the fixed circles of radius
  `ε/(n+2)` (`decCircle ε n`).

Identities (deterministic, for a Euclidean length metric `D` with `Dh = c · internalCost D V` on `V × V`):
`decPunct V Dh O x y = ofReal c * internalMetric D O x y` (`decPunct_eq_const_mul_internalMetric`) and the root identity
`decRoot V Dh ε O x = ofReal c * internalMetric D O 0 x` (`decRoot_eq_const_mul_internalMetric`). The chosen sets do not
depend on the metric, so the definitions are fixed before the true metric is known.
-/

namespace HarmonicBalls.S11m

open Set Metric Filter Topology MeasureTheory
open scoped ENNReal

/-- Chain vertices for the domain `O`: a fixed countable subset of `O`, dense in `O`. -/
noncomputable def decChain (O : Set ℂ) : Set ℂ :=
  Classical.choose (exists_countable_dense_subset_of_secondCountable O)

theorem decChain_spec (O : Set ℂ) : decChain O ⊆ O ∧ (decChain O).Countable ∧ O ⊆ closure (decChain O) :=
  Classical.choose_spec (exists_countable_dense_subset_of_secondCountable O)

/-- Clearance set for the pair `(V, O)`: a fixed countable subset of `V \ O`, dense in `V \ O`. -/
noncomputable def decClear (V O : Set ℂ) : Set ℂ :=
  Classical.choose (exists_countable_dense_subset_of_secondCountable (V \ O))

theorem decClear_spec (V O : Set ℂ) :
    decClear V O ⊆ V \ O ∧ (decClear V O).Countable ∧ V \ O ⊆ closure (decClear V O) :=
  Classical.choose_spec (exists_countable_dense_subset_of_secondCountable (V \ O))

/-- Circle sets of radius `ε/(n+2)`: a fixed countable subset of the circle, dense in it. -/
noncomputable def decCircle (ε : ℝ) (n : ℕ) : Set ℂ :=
  Classical.choose (exists_countable_dense_subset_of_secondCountable (sphere (0 : ℂ) (ε / ((n : ℝ) + 2))))

theorem decCircle_spec (ε : ℝ) (n : ℕ) :
    decCircle ε n ⊆ sphere (0 : ℂ) (ε / ((n : ℝ) + 2)) ∧ (decCircle ε n).Countable ∧
      sphere (0 : ℂ) (ε / ((n : ℝ) + 2)) ⊆ closure (decCircle ε n) :=
  Classical.choose_spec (exists_countable_dense_subset_of_secondCountable (sphere (0 : ℂ) (ε / ((n : ℝ) + 2))))

/-- Decoded localized clearance infimum on the domain `O` (with ambient domain `V`), from the decoded raw metric `Dh`. -/
noncomputable def decPunct (V : Set ℂ) (Dh : ℂ → ℂ → ℝ) (O : Set ℂ) (x y : ℂ) : ℝ≥0∞ :=
  localClearanceInf (decChain O) (decClear V O) Dh x y

/-- Decoded root value `D(0, x; O)` along the circles of radius `ε/(n+2)`, computed from `O \ {0}`. -/
noncomputable def decRoot (V : Set ℂ) (Dh : ℂ → ℂ → ℝ) (ε : ℝ) (O : Set ℂ) (x : ℂ) : ℝ≥0∞ :=
  limsup (fun n => ⨅ y ∈ decCircle ε n, decPunct V Dh (O \ {0}) y x) atTop

section Measurable

variable {Pair : Type*} [MeasurableSpace Pair]

/-- The decoded localized clearance infimum is measurable in the pairing. -/
theorem measurable_decPunct {Dh : Pair → ℂ → ℂ → ℝ} (hDh : ∀ a b, Measurable fun ℓ => Dh ℓ a b) (V O : Set ℂ)
    (x y : ℂ) : Measurable fun ℓ => decPunct V (Dh ℓ) O x y :=
  measurable_decClearanceInf hDh (decChain_spec O).2.1 (decClear_spec V O).2.1 x y

/-- The decoded root value is measurable in the pairing. -/
theorem measurable_decRoot' {Dh : Pair → ℂ → ℂ → ℝ} (hDh : ∀ a b, Measurable fun ℓ => Dh ℓ a b) (V : Set ℂ)
    (ε : ℝ) (O : Set ℂ) (x : ℂ) : Measurable fun ℓ => decRoot V (Dh ℓ) ε O x :=
  measurable_decRoot hDh (decChain_spec (O \ {0})).2.1 (Qn := fun _ => decClear V (O \ {0}))
    (fun _ => (decClear_spec V (O \ {0})).2.1) (fun n => (decCircle_spec ε n).2.1) x

end Measurable

/-- **Decoded punctured identity** (deterministic). If `Dh = c · internalCost D V` on `V × V` for a Euclidean length
metric `D` on the connected open set `V`, then the decoded clearance infimum on an open `O ⊆ V` is `c · D(·,·; O)`. -/
theorem decPunct_eq_const_mul_internalMetric {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {V O : Set ℂ}
    (hVo : IsOpen V) (hconnV : IsConnected V) (hO : IsOpen O) (hOV : O ⊆ V) {Dh : ℂ → ℂ → ℝ} {c : ℝ} (hc : 0 < c)
    (hDh : ∀ v ∈ V, ∀ w ∈ V, Dh v w = c * internalCost D V v w) {x y : ℂ} (hx : x ∈ O) (hy : y ∈ O) :
    decPunct V Dh O x y = ENNReal.ofReal c * internalMetric D O x y := by
  unfold decPunct
  refine localClearanceInf_eq_const_mul_internalMetric hD hO hVo hOV
    (fun v hv => hOV ((decChain_spec O).1 hv)) (decChain_spec O).2.2 (decClear_spec V O).1
    (decClear_spec V O).2.2 (fun v hv w hw => internalMetric_ne_top_of_isConnected hD hVo hconnV hv hw) hc hDh hx hy

/-- **Decoded root identity** (deterministic). Under the hypotheses of `decPunct_eq_const_mul_internalMetric`, with
`B_ε(0) ⊆ O` and `D(0, x; O) < ∞` for `x ∈ O \ {0}`, the decoded root value is `c · D(0, x; O)`. -/
theorem decRoot_eq_const_mul_internalMetric {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {V O : Set ℂ} (hVo : IsOpen V) (hconnV : IsConnected V) (hO : IsOpen O)
    (hOV : O ⊆ V) {Dh : ℂ → ℂ → ℝ} {c : ℝ} (hc : 0 < c)
    (hDh : ∀ v ∈ V, ∀ w ∈ V, Dh v w = c * internalCost D V v w) {ε : ℝ} (hε : 0 < ε)
    (hball : ball (0 : ℂ) ε ⊆ O) (h0 : (0 : ℂ) ∈ O) {x : ℂ} (hx : x ∈ O) (hx0 : x ≠ 0)
    (hfin : internalMetric D O 0 x ≠ ⊤) :
    decRoot V Dh ε O x = ENNReal.ofReal c * internalMetric D O 0 x := by
  have hOm : IsOpen (O \ {0}) := hO.sdiff isClosed_singleton
  have hOmV : O \ {0} ⊆ V := fun v hv => hOV hv.1
  have hxm : x ∈ O \ {0} := ⟨hx, hx0⟩
  have hcirc : ∀ n, ∀ y ∈ decCircle ε n, y ∈ O \ {0} := by
    intro n y hy
    have hy' := (decCircle_spec ε n).1 hy
    have hn : ‖y‖ = ε / ((n : ℝ) + 2) := mem_sphere_zero_iff_norm.mp hy'
    have hlt : ε / ((n : ℝ) + 2) < ε :=
      div_lt_self hε (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    have hyb : y ∈ ball (0 : ℂ) ε := mem_ball_zero_iff.mpr (by rw [hn]; exact hlt)
    refine ⟨hball hyb, fun h => ?_⟩
    have hy0 : y = 0 := h
    have hpos : 0 < ε / ((n : ℝ) + 2) := by positivity
    rw [hy0, norm_zero] at hn
    linarith
  have hpt : ∀ n, (⨅ y ∈ decCircle ε n, decPunct V Dh (O \ {0}) y x) =
      ENNReal.ofReal c * ⨅ y ∈ decCircle ε n, internalMetric D (O \ {0}) y x := by
    intro n
    have hfun : ∀ y ∈ decCircle ε n, decPunct V Dh (O \ {0}) y x = ENNReal.ofReal c * internalMetric D (O \ {0}) y x :=
      fun y hy => decPunct_eq_const_mul_internalMetric hD hVo hconnV hOm hOmV hc hDh (hcirc n y hy) hxm
    have hcongr : (⨅ y ∈ decCircle ε n, decPunct V Dh (O \ {0}) y x) =
        ⨅ y ∈ decCircle ε n, ENNReal.ofReal c * internalMetric D (O \ {0}) y x := by
      refine iInf_congr fun y => ?_
      by_cases hy : y ∈ decCircle ε n
      · rw [iInf_pos hy, iInf_pos hy, hfun y hy]
      · rw [iInf_neg hy, iInf_neg hy]
    rw [hcongr]
    simp only [ENNReal.mul_iInf_of_ne (ENNReal.ofReal_pos.mpr hc).ne' ENNReal.ofReal_ne_top]
  have hs : Tendsto (fun n : ℕ => ε / ((n : ℝ) + 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  unfold decRoot
  rw [show (fun n => ⨅ y ∈ decCircle ε n, decPunct V Dh (O \ {0}) y x) =
      fun n => ENNReal.ofReal c * ⨅ y ∈ decCircle ε n, internalMetric D (O \ {0}) y x from funext hpt,
    ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top]
  congr 1
  exact (internalMetric_root_eq_limsup_of_dense hD hnonneg hO h0 hball hx hx0 hfin
    (fun n : ℕ => ε / ((n : ℝ) + 2)) hs (fun n => by positivity)
    (fun n => div_lt_self hε (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])) (decCircle ε)
    (fun n => decCircle_spec ε n)).symm

open Classical in
/-- **Decoded internal distance on a fixed domain** `O` (route eq (16)): if `0 ∉ O` it is the punctured clearance
infimum; if `0 ∈ O` it is the minimum of the punctured value on `O \ {0}` and the sum of the two decoded root values,
with the root values at the endpoint `0` read off directly. `εOf O` is the radius of the root circles on `O`. -/
noncomputable def decInt (V : Set ℂ) (Dh : ℂ → ℂ → ℝ) (εOf : Set ℂ → ℝ) (O : Set ℂ) (x y : ℂ) : ℝ≥0∞ :=
  if (0 : ℂ) ∈ O then
    if x = 0 then (if y = 0 then 0 else decRoot V Dh (εOf O) O y)
    else if y = 0 then decRoot V Dh (εOf O) O x
    else min (decPunct V Dh (O \ {0}) x y) (decRoot V Dh (εOf O) O x + decRoot V Dh (εOf O) O y)
  else decPunct V Dh O x y

section MeasurableInt

variable {Pair : Type*} [MeasurableSpace Pair]

/-- The decoded internal distance is measurable in the pairing. -/
theorem measurable_decInt {Dh : Pair → ℂ → ℂ → ℝ} (hDh : ∀ a b, Measurable fun ℓ => Dh ℓ a b) (V : Set ℂ)
    (εOf : Set ℂ → ℝ) (O : Set ℂ) (x y : ℂ) : Measurable fun ℓ => decInt V (Dh ℓ) εOf O x y := by
  unfold decInt
  split_ifs
  · exact measurable_const
  · exact measurable_decRoot' hDh V (εOf O) O y
  · exact measurable_decRoot' hDh V (εOf O) O x
  · exact (measurable_decPunct hDh V (O \ {0}) x y).min
      ((measurable_decRoot' hDh V (εOf O) O x).add (measurable_decRoot' hDh V (εOf O) O y))
  · exact measurable_decPunct hDh V O x y

end MeasurableInt

/-- **Decoded internal identity** (deterministic). For a Euclidean length metric `D` on `V`, a connected open `O ⊆ V`
and `Dh = c · internalCost D V` on `V × V`, the decoded internal distance equals `c · D(·,·; O)` on `O × O`.
The hypotheses `hε`, `hball` concern the radius `εOf O` of the root circles. -/
theorem decInt_eq_const_mul_internalMetric {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {V O : Set ℂ} (hVo : IsOpen V) (hconnV : IsConnected V) (hO : IsOpen O)
    (hconnO : IsConnected O) (hOV : O ⊆ V) {Dh : ℂ → ℂ → ℝ} {c : ℝ} (hc : 0 < c)
    (hDh : ∀ v ∈ V, ∀ w ∈ V, Dh v w = c * internalCost D V v w) {εOf : Set ℂ → ℝ}
    (hε : 0 < εOf O) (hball : ball (0 : ℂ) (εOf O) ⊆ O) {x y : ℂ} (hx : x ∈ O) (hy : y ∈ O) :
    decInt V Dh εOf O x y = ENNReal.ofReal c * internalMetric D O x y := by
  unfold decInt
  by_cases h0 : (0 : ℂ) ∈ O
  · simp only [h0, ↓reduceIte]
    have hsym : ∀ z, internalMetric D O z 0 = internalMetric D O 0 z := fun z => hD.internalMetric_symm O z 0
    by_cases hx0 : x = 0
    · subst hx0
      by_cases hy0 : y = 0
      · subst hy0
        simp only [↓reduceIte]
        rw [hD.internalMetric_self_of_mem_open hnonneg hO h0, mul_zero]
      · simp only [hy0, ↓reduceIte]
        exact decRoot_eq_const_mul_internalMetric hD hnonneg hVo hconnV hO hOV hc hDh hε hball h0 hy hy0
          (internalMetric_ne_top_of_isConnected hD hO hconnO h0 hy)
    · by_cases hy0 : y = 0
      · subst hy0
        simp only [hx0, ↓reduceIte]
        rw [decRoot_eq_const_mul_internalMetric hD hnonneg hVo hconnV hO hOV hc hDh hε hball h0 hx hx0
          (internalMetric_ne_top_of_isConnected hD hO hconnO h0 hx), hsym x]
      · simp only [hx0, hy0, ↓reduceIte]
        have hOm : IsOpen (O \ {0}) := hO.sdiff isClosed_singleton
        have hOmV : O \ {0} ⊆ V := fun v hv => hOV hv.1
        have hxm : x ∈ O \ {0} := ⟨hx, hx0⟩
        have hym : y ∈ O \ {0} := ⟨hy, hy0⟩
        rw [decPunct_eq_const_mul_internalMetric hD hVo hconnV hOm hOmV hc hDh hxm hym,
          decRoot_eq_const_mul_internalMetric hD hnonneg hVo hconnV hO hOV hc hDh hε hball h0 hx hx0
            (internalMetric_ne_top_of_isConnected hD hO hconnO h0 hx),
          decRoot_eq_const_mul_internalMetric hD hnonneg hVo hconnV hO hOV hc hDh hε hball h0 hy hy0
            (internalMetric_ne_top_of_isConnected hD hO hconnO h0 hy),
          internalMetric_eq_min_punctured hD O (x := x) (y := y), hsym x, ← mul_add]
        have hmono : Monotone (fun t : ℝ≥0∞ => ENNReal.ofReal c * t) := fun a b hab => by dsimp only; gcongr
        exact (Monotone.map_min hmono).symm
  · simp only [h0, ↓reduceIte]
    exact decPunct_eq_const_mul_internalMetric hD hVo hconnV hO hOV hc hDh hx hy

end HarmonicBalls.S11m
