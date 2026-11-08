import HarmonicBalls.Proofs.Metric.SummablePathWeightedLength
import HarmonicBalls.Steps.Sec11.MetricArcLength
import HarmonicBalls.Steps.Sec11.WeylPathReverse
import HarmonicBalls.Steps.Sec11.PathCrossings
import HarmonicBalls.Steps.Sec11.CurveLengthReparam
import HarmonicBalls.Steps.Sec11.LocalPathLength

/-!
# Small weighted paths

The deterministic path construction associated with the logarithmic weight.
We acknowledge Leonardo Bonanno's contributions through the pinned
Lattice-Probability development.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

/-- Every positive radius below the initial scale lies in a later annular band. -/
theorem exists_radius_band {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0))
    {i : ℕ} {u : ℝ} (hu : 0 < u) (hi : u ≤ r i) :
    ∃ j, i ≤ j ∧ r (j + 1) < u ∧ u ≤ r j := by
  have hev : ∀ᶠ n : ℕ in atTop, r n < u :=
    hr.eventually (eventually_lt_nhds hu)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  have hex : ∃ n : ℕ, r (i + n + 1) < u := by
    refine ⟨N, hN _ ?_⟩
    omega
  let n := Nat.find hex
  have hn : r (i + n + 1) < u := Nat.find_spec hex
  refine ⟨i + n, by omega, hn, ?_⟩
  cases hnval : n with
  | zero => simpa only [hnval, add_zero] using hi
  | succ k =>
    have hmin := Nat.find_min hex (show k < Nat.find hex by
      change k < n
      rw [hnval]
      omega)
    have hle : u ≤ r (i + k + 1) := le_of_not_gt hmin
    simpa only [Nat.add_succ] using hle

/-- The cost assigned to the annular piece between consecutive radii. -/
noncomputable def smallPathCost (r L : ℕ → ℝ) (β : ℝ) (i : ℕ) : ℝ :=
  2 * L i * (if 0 ≤ β then (r (i + 1)) ^ (-β) else (2 * r i) ^ (-β))

/-- Exact target of the deterministic small-path construction. -/
def SmallWeightedPathExistence (D : ℂ → ℂ → ℝ) (r L : ℕ → ℝ) (β : ℝ) : Prop :=
  IsEuclideanLengthMetric D →
  (∀ i, 0 < r i) → StrictAnti r → Tendsto r atTop (𝓝 0) →
  (∀ i, 0 < L i) → Summable L → Summable (smallPathCost r L β) →
  (∀ i y z, y ∈ closedBall (0 : ℂ) (r i) → z ∈ closedBall (0 : ℂ) (r i) →
    internalMetric D (ball 0 (2 * r i)) y z ≤ ENNReal.ofReal (L i)) →
  ∀ i x, ‖x‖ ≤ r i → ∃ T : ℝ, ∃ p : ℝ → ℂ,
    IsLengthParametrized D p T ∧ p 0 = 0 ∧ p T = x ∧
    (∀ t ∈ Icc 0 T, p t ∈ ball (0 : ℂ) (2 * r i)) ∧
    (∀ t ∈ Ioc 0 T, p t ≠ 0) ∧
    T ≤ 2 * (∑' n, L (i + n)) ∧
    (∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (-β * Real.log ‖p t‖))) ≤
      ENNReal.ofReal (∑' n, smallPathCost r L β (i + n))

/-- The tails of a summable real sequence tend to zero. -/
theorem tendsto_smallPath_tail (a : ℕ → ℝ) :
    Tendsto (fun i => ∑' n, a (i + n)) atTop (𝓝 0) := by
  simpa only [Nat.add_comm] using (tendsto_sum_nat_add a)

/-- A path connecting a point outside a sphere to a point inside it has a
first visit to the sphere, and stays outside the smaller ball until that visit. -/
theorem path_first_sphere {x y : ℂ} (P : Path x y) {ρ : ℝ}
    (hx : ρ ≤ ‖x‖) (hy : ‖y‖ ≤ ρ) :
    ∃ s ∈ Icc (0 : ℝ) 1, ‖P.extend s‖ = ρ ∧
      ∀ t ∈ Icc (0 : ℝ) s, ρ ≤ ‖P.extend t‖ := by
  let f : ℝ → ℝ := fun t => ‖P.extend t‖
  let A : Set ℝ := Icc 0 1 ∩ {t | f t = ρ}
  have hf : Continuous f := P.continuous_extend.norm
  have hclosed : IsClosed A := isClosed_Icc.inter (isClosed_eq hf continuous_const)
  have hne : A.Nonempty := by
    obtain ⟨t, ht, heq⟩ := path_meets_sphere_between P (z := 0)
      (by simpa only [dist_zero_right] using hx)
      (by simpa only [dist_zero_right] using hy)
    refine ⟨t, ht, ?_⟩
    change f t = ρ
    simpa only [mem_sphere, dist_zero_right, f] using heq
  have hbdd : BddBelow A := ⟨0, fun t ht => ht.1.1⟩
  let s := sInf A
  have hs : s ∈ A := hclosed.csInf_mem hne hbdd
  have hs2 : f s = ρ := hs.2
  refine ⟨s, hs.1, hs2, ?_⟩
  intro t ht
  by_contra hnot
  have hft : f t < ρ := lt_of_not_ge hnot
  have hstart : ρ ≤ f 0 := by simpa only [f, P.extend_zero] using hx
  obtain ⟨u, hu, hfu⟩ := intermediate_value_Icc' ht.1 hf.continuousOn ⟨hft.le, hstart⟩
  have huA : u ∈ A := ⟨⟨hu.1, hu.2.trans (ht.2.trans hs.1.2)⟩, hfu⟩
  have hsu : s ≤ u := csInf_le hbdd huA
  have hut : u ≤ t := hu.2
  have hst : s ≤ t := hsu.trans hut
  have hts : t = s := le_antisymm ht.2 hst
  have : f t = ρ := by simpa only [hts] using hs2
  linarith

/-- A finite upper bound for internal distance gives a path with the
specified strict length bound. -/
theorem exists_path_of_internalMetric_le {D : ℂ → ℂ → ℝ} {U : Set ℂ}
    {x y : ℂ} {L : ℝ} (hL : 0 < L)
    (hbound : internalMetric D U x y ≤ ENNReal.ofReal L) :
    ∃ P : Path x y, (∀ t, P t ∈ U) ∧ pathLength D P < ENNReal.ofReal (2 * L) := by
  have hlt : internalMetric D U x y < ENNReal.ofReal (2 * L) :=
    hbound.trans_lt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hL.le).2 (by linarith))
  simpa only [internalMetric, iInf_lt_iff, exists_prop] using hlt

/-- Stop a path at its first visit to a smaller sphere, without increasing
its length or leaving its original range. -/
theorem exists_first_sphere_subpath {D : ℂ → ℂ → ℝ} {x : ℂ}
    (P : Path x 0) {ρ : ℝ} (hρ : 0 ≤ ρ) (hx : ρ ≤ ‖x‖) :
    ∃ z : ℂ, ‖z‖ = ρ ∧ ∃ Q : Path x z,
      (∀ t, ρ ≤ ‖Q t‖) ∧ Set.range Q ⊆ Set.range P ∧
      pathLength D Q ≤ pathLength D P := by
  obtain ⟨s, hs, hnorm, hbefore⟩ := path_first_sphere P hx (by simpa using hρ)
  let u : unitInterval := ⟨s, hs⟩
  let Q := P.subpath 0 u
  have hu0 : (0 : unitInterval) ≤ u := u.property.1
  have hrange : Set.range Q = P '' Icc (0 : unitInterval) u :=
    P.range_subpath_of_le 0 u hu0
  have hQ : ∀ t, ρ ≤ ‖Q t‖ := by
    intro t
    have hm : Q t ∈ P '' Icc (0 : unitInterval) u := hrange ▸ mem_range_self t
    obtain ⟨v, hv, heq⟩ := hm
    rw [← heq, ← Path.extend_apply P v.property]
    exact hbefore v ⟨v.property.1, hv.2⟩
  have hsubset : Set.range Q ⊆ Set.range P := by
    rw [hrange]
    exact Set.image_subset_range _ _
  have hlen := pathLength_subpath_le D P 0 u hu0
  refine ⟨P u, ?_, Q.cast P.source.symm rfl, ?_, ?_, ?_⟩
  · simpa only [u, ← Path.extend_apply P hs] using hnorm
  · simpa only [Path.cast_coe] using hQ
  · simpa only [Path.cast_coe] using hsubset
  · simpa only [pathLength, Path.extend_cast] using hlen

/-- Arc-length parametrization preserves the image of a finite-length curve. -/
theorem IsEuclideanLengthMetric.exists_lengthParametrized_with_image
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {p : ℝ → ℂ} {T : ℝ} (hT : 0 ≤ T) (hp : ContinuousOn p (Icc 0 T))
    (hfinite : curveLength D p 0 T < ∞) :
    ∃ q : ℝ → ℂ, IsLengthParametrized D q (curveLength D p 0 T).toReal ∧
      q 0 = p 0 ∧ q (curveLength D p 0 T).toReal = p T ∧
      q '' Icc 0 (curveLength D p 0 T).toReal = p '' Icc 0 T := by
  obtain ⟨q, hq, hq0, hqT, htrack⟩ :=
    hD.exists_lengthParametrized_with_tracking hT hp hfinite
  have himage := (hD.cumulative_curveLength_properties hT hp hfinite).2.2.2
  refine ⟨q, hq, hq0, hqT, ?_⟩
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨u, hu, heu⟩ := (show t ∈ (fun v => (curveLength D p 0 v).toReal) '' Icc 0 T from
      himage.symm ▸ ht)
    change (curveLength D p 0 u).toReal = t at heu
    exact ⟨u, hu, by rw [← htrack u hu, heu]⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨(curveLength D p 0 t).toReal, ?_, htrack t ht⟩
    rw [← himage]
    exact ⟨t, ht, rfl⟩

/-- A bounded internal distance supplies one arc-length-parametrized annular
piece, stopped on its first visit to the inner sphere. -/
theorem IsEuclideanLengthMetric.exists_short_annular_piece
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {x : ℂ} {ρ R L : ℝ} (hρ : 0 ≤ ρ) (hx : ρ ≤ ‖x‖) (hL : 0 < L)
    (hbound : internalMetric D (ball 0 R) x 0 ≤ ENNReal.ofReal L) :
    ∃ z : ℂ, ∃ T : ℝ, ∃ p : ℝ → ℂ,
      ‖z‖ = ρ ∧ IsLengthParametrized D p T ∧ p 0 = x ∧ p T = z ∧
      T < 2 * L ∧ ∀ t ∈ Icc 0 T, ρ ≤ ‖p t‖ ∧ p t ∈ ball (0 : ℂ) R := by
  obtain ⟨P, hPU, hPlen⟩ := exists_path_of_internalMetric_le hL hbound
  obtain ⟨z, hz, Q, hQnorm, hQrange, hQlen⟩ :=
    exists_first_sphere_subpath P hρ hx
  have hlt : pathLength D Q < ENNReal.ofReal (2 * L) := hQlen.trans_lt hPlen
  have hfinite : curveLength D Q.extend 0 1 < ∞ :=
    hlt.trans_le le_top
  obtain ⟨p, hp, hp0, hpT, himage⟩ :=
    hD.exists_lengthParametrized_with_image (by norm_num) Q.continuous_extend.continuousOn hfinite
  have hT : (curveLength D Q.extend 0 1).toReal < 2 * L := by
    have h := (ENNReal.toReal_lt_toReal hfinite.ne ENNReal.ofReal_ne_top).2 hlt
    simpa only [ENNReal.toReal_ofReal (by linarith : 0 ≤ 2 * L)] using h
  refine ⟨z, _, p, hz, hp, ?_, ?_, hT, ?_⟩
  · simpa only [Path.extend_zero] using hp0
  · simpa only [Path.extend_one] using hpT
  · intro t ht
    have hm : p t ∈ Q.extend '' Icc (0 : ℝ) 1 := himage ▸ ⟨t, ht, rfl⟩
    obtain ⟨v, hv, hvp⟩ := hm
    let u : unitInterval := ⟨v, hv⟩
    have heq : Q u = p t := by simpa only [u, Path.extend_apply Q hv] using hvp
    have hpRange : p t ∈ Set.range P := hQrange ⟨u, heq⟩
    obtain ⟨w, hw⟩ := hpRange
    constructor
    · rw [← heq]
      exact hQnorm u
    · rw [← hw]
      exact hPU w

/-- The logarithmic weight is bounded on an annulus by the appropriate
endpoint power, for either sign of the exponent. -/
theorem exp_neg_mul_log_le_annulus {β a b u : ℝ} (ha : 0 < a)
    (hau : a ≤ u) (hub : u ≤ b) :
    Real.exp (-β * Real.log u) ≤
      (if 0 ≤ β then a ^ (-β) else b ^ (-β)) := by
  have hu : 0 < u := ha.trans_le hau
  have hb : 0 < b := hu.trans_le hub
  by_cases hβ : 0 ≤ β
  · rw [ite_eq_left hβ, Real.rpow_def_of_pos ha]
    apply Real.exp_le_exp.mpr
    have hlog := Real.log_le_log ha hau
    nlinarith
  · rw [ite_eq_right hβ, Real.rpow_def_of_pos hb]
    apply Real.exp_le_exp.mpr
    have hlog := Real.log_le_log hu hub
    have hβ' : β < 0 := lt_of_not_ge hβ
    nlinarith

/-- The cost of a path staying in an annulus is bounded by its duration
times the endpoint power bound. -/
theorem annular_path_cost_le {β a b T : ℝ} {p : ℝ → ℂ}
    (ha : 0 < a) (hT : 0 ≤ T)
    (hp : ∀ t ∈ Icc 0 T, a ≤ ‖p t‖ ∧ ‖p t‖ ≤ b) :
    (∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (-β * Real.log ‖p t‖))) ≤
      ENNReal.ofReal (T * (if 0 ≤ β then a ^ (-β) else b ^ (-β))) := by
  let K : ℝ := if 0 ≤ β then a ^ (-β) else b ^ (-β)
  have hb : 0 < b := ha.trans_le ((hp 0 ⟨le_rfl, hT⟩).1.trans (hp 0 ⟨le_rfl, hT⟩).2)
  have hK : 0 ≤ K := by
    dsimp only [K]
    split <;> positivity
  calc
    _ ≤ ∫⁻ _ in Icc (0 : ℝ) T, ENNReal.ofReal K := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact ENNReal.ofReal_le_ofReal (exp_neg_mul_log_le_annulus ha (hp t ht).1 (hp t ht).2)
    _ = ENNReal.ofReal (T * K) := by
      simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero,
        ← ENNReal.ofReal_mul hK, mul_comm]

/-- A bounded internal distance supplies an annular piece with its explicit
logarithmic weighted-length bound. -/
theorem IsEuclideanLengthMetric.exists_short_weighted_annular_piece
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {x : ℂ} {ρ R L β : ℝ} (hρ : 0 < ρ) (hx : ρ ≤ ‖x‖) (hL : 0 < L)
    (hbound : internalMetric D (ball 0 R) x 0 ≤ ENNReal.ofReal L) :
    ∃ z : ℂ, ∃ T : ℝ, ∃ p : ℝ → ℂ,
      ‖z‖ = ρ ∧ IsLengthParametrized D p T ∧ p 0 = x ∧ p T = z ∧
      T ≤ 2 * L ∧ (∀ t ∈ Icc 0 T, ρ ≤ ‖p t‖ ∧ p t ∈ ball (0 : ℂ) R) ∧
      (∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (-β * Real.log ‖p t‖))) ≤
        ENNReal.ofReal (2 * L * (if 0 ≤ β then ρ ^ (-β) else R ^ (-β))) := by
  obtain ⟨z, T, p, hz, hp, hp0, hpT, hT, hann⟩ :=
    hD.exists_short_annular_piece hρ.le hx hL hbound
  have hann' : ∀ t ∈ Icc 0 T, ρ ≤ ‖p t‖ ∧ ‖p t‖ ≤ R := by
    intro t ht
    exact ⟨(hann t ht).1, (show ‖p t‖ < R by
      simpa only [mem_ball, dist_zero_right] using (hann t ht).2).le⟩
  have hR : 0 < R := hρ.trans_le ((hann' 0 ⟨le_rfl, hp.1⟩).1.trans
    (hann' 0 ⟨le_rfl, hp.1⟩).2)
  have hK : 0 ≤ (if 0 ≤ β then ρ ^ (-β) else R ^ (-β)) := by
    split <;> positivity
  refine ⟨z, T, p, hz, hp, hp0, hpT, hT.le, hann, ?_⟩
  exact (annular_path_cost_le hρ hp.1 hann').trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hT.le hK))

/-- The constructed path, once available, bounds the corresponding Weyl distance. -/
theorem weylScaling_le_of_smallWeightedPath {D : ℂ → ℂ → ℝ} {β B T : ℝ}
    {p : ℝ → ℂ} {x : ℂ} (hp : IsLengthParametrized D p T)
    (hp0 : p 0 = 0) (hpT : p T = x)
    (hcost : (∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (-β * Real.log ‖p t‖))) ≤
      ENNReal.ofReal B) :
    weylScaling D 1 (fun z => -β * Real.log ‖z‖) 0 x ≤ ENNReal.ofReal B := by
  calc
    _ ≤ ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (1 * (-β * Real.log ‖p t‖))) :=
      (iInf₂_le T p).trans ((iInf₂_le hp hp0).trans (iInf_le _ hpT))
    _ ≤ ENNReal.ofReal B := by simpa only [one_mul] using hcost

#print axioms IsEuclideanLengthMetric.exists_short_weighted_annular_piece
#print axioms IsEuclideanLengthMetric.exists_short_annular_piece
#print axioms IsEuclideanLengthMetric.exists_lengthParametrized_with_image
#print axioms exists_radius_band
#print axioms annular_path_cost_le
#print axioms exp_neg_mul_log_le_annulus
#print axioms exists_first_sphere_subpath
#print axioms path_first_sphere
#print axioms exists_path_of_internalMetric_le
#print axioms tendsto_smallPath_tail
#print axioms weylScaling_le_of_smallWeightedPath

end HarmonicBalls
