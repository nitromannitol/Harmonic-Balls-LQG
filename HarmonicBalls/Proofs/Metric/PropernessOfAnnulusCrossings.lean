import HarmonicBalls.Steps.Sec11.PuncturedPathLength

/-! # Annulus crossing lengths

Deterministic estimates for Euclidean-continuous paths in a Euclidean length metric.
We acknowledge Leonardo Bonanno's contributions to this formalization.
-/

namespace HarmonicBalls

open Set Metric
open scoped ENNReal

/-- The infimum of lengths of paths in the closed annulus joining its two
boundary circles. The infimum is `∞` if there is no such path. -/
noncomputable def radialAnnulusCrossingLength (D : ℂ → ℂ → ℝ)
    (center : ℂ) (r R : ℝ) : ℝ≥0∞ :=
  ⨅ (x : ℂ) (_ : x ∈ sphere center r) (y : ℂ) (_ : y ∈ sphere center R),
    internalMetric D {z | r ≤ dist z center ∧ dist z center ≤ R} x y

/-- Every admissible crossing path has length at least the crossing length. -/
theorem radialAnnulusCrossingLength_le_pathLength
    {D : ℂ → ℂ → ℝ} {center x y : ℂ} {r R : ℝ}
    (hx : x ∈ sphere center r) (hy : y ∈ sphere center R) (p : Path x y)
    (hp : ∀ t, r ≤ dist (p t) center ∧ dist (p t) center ≤ R) :
    radialAnnulusCrossingLength D center r R ≤ pathLength D p := by
  unfold radialAnnulusCrossingLength internalMetric
  exact iInf_le_of_le x (iInf_le_of_le hx (iInf_le_of_le y (iInf_le_of_le hy
    (iInf_le_of_le p (iInf_le _ hp)))))

private structure CrossingLengthPoint where
  val : ℂ

/-- The lengths of finitely many ordered disjoint subpaths are bounded by the
length of the original path. The intervening subpaths may have arbitrary length. -/
theorem IsEuclideanLengthMetric.sum_pathLength_subpaths_le
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {x y : ℂ} (p : Path x y) (τ : ℕ → unitInterval) (hτ : Monotone τ) (n : ℕ) :
    (∑ i ∈ Finset.range n, pathLength D (p.subpath (τ (2 * i)) (τ (2 * i + 1)))) ≤
      pathLength D p := by
  let : MetricSpace CrossingLengthPoint := {
    dist := fun a b => D a.val b.val
    dist_self := fun a => hD.self_eq_zero a.val
    dist_comm := fun a b => hD.symm a.val b.val
    dist_triangle := fun a b c => hD.triangle a.val b.val c.val
    eq_of_dist_eq_zero := by
      intro ⟨a⟩ ⟨b⟩ h
      exact congrArg CrossingLengthPoint.mk (hD.eq_of_eq_zero a b h) }
  have hcurve (g : ℝ → ℂ) (a b : ℝ) :
      curveLength D g a b = eVariationOn (fun u => (⟨g u⟩ : CrossingLengthPoint)) (Icc a b) := by
    simp only [curveLength, eVariationOn, edist_dist]
    rfl
  let f : ℝ → CrossingLengthPoint := fun u => ⟨p.extend u⟩
  have hseg (a b : unitInterval) (hab : a ≤ b) :
      pathLength D (p.subpath a b) ≤ eVariationOn f (Icc (a : ℝ) (b : ℝ)) := by
    let φ : ℝ → ℝ := fun u => (1 - u) * (a : ℝ) + u * (b : ℝ)
    have hφ : MonotoneOn φ (Icc (0 : ℝ) 1) := by
      intro u hu v hv huv
      dsimp [φ]
      have hab' : (a : ℝ) ≤ b := hab
      nlinarith
    have hφmem : MapsTo φ (Icc (0 : ℝ) 1) (Icc (a : ℝ) (b : ℝ)) := by
      intro u hu
      dsimp [φ]
      have hab' : (a : ℝ) ≤ b := hab
      constructor <;> nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr hab'),
        mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr hab')]
    have hφunit : MapsTo φ (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := by
      intro u hu
      have h := hφmem hu
      exact ⟨a.property.1.trans h.1, h.2.trans b.property.2⟩
    have heq : EqOn (fun u => (⟨(p.subpath a b).extend u⟩ : CrossingLengthPoint))
        (f ∘ φ) (Icc (0 : ℝ) 1) := by
      intro u hu
      dsimp only [Function.comp_apply, f]
      apply congrArg CrossingLengthPoint.mk
      rw [Path.extend_apply _ hu, Path.extend_apply _ (hφunit hu)]
      rfl
    calc
      pathLength D (p.subpath a b) = eVariationOn
          (fun u => (⟨(p.subpath a b).extend u⟩ : CrossingLengthPoint)) (Icc (0 : ℝ) 1) :=
        hcurve _ _ _
      _ = eVariationOn (f ∘ φ) (Icc (0 : ℝ) 1) := eVariationOn.eq_of_eqOn heq
      _ ≤ eVariationOn f (Icc (a : ℝ) (b : ℝ)) :=
        eVariationOn.comp_le_of_monotoneOn f φ hφ hφmem
  have hsum (m : ℕ) :
      (∑ i ∈ Finset.range m, pathLength D (p.subpath (τ (2 * i)) (τ (2 * i + 1)))) ≤
        eVariationOn f (Icc (0 : ℝ) (τ (2 * m) : ℝ)) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have h1 : (τ (2 * m) : ℝ) ≤ τ (2 * m + 1) := hτ (by omega)
      have h2 : (τ (2 * m + 1) : ℝ) ≤ τ (2 * (m + 1)) := hτ (by omega)
      have hsplit : eVariationOn f (Icc (0 : ℝ) (τ (2 * m) : ℝ)) +
          eVariationOn f (Icc (τ (2 * m) : ℝ) (τ (2 * (m + 1)) : ℝ)) =
          eVariationOn f (Icc (0 : ℝ) (τ (2 * (m + 1)) : ℝ)) := by
        simpa only [univ_inter] using eVariationOn.Icc_add_Icc f (s := univ)
          (τ (2 * m)).property.1 (h1.trans h2) (mem_univ _)
      calc
        _ ≤ eVariationOn f (Icc (0 : ℝ) (τ (2 * m) : ℝ)) +
            eVariationOn f (Icc (τ (2 * m) : ℝ) (τ (2 * m + 1) : ℝ)) :=
          add_le_add ih (hseg _ _ h1)
        _ ≤ _ := by
          rw [← hsplit]
          exact add_le_add le_rfl (eVariationOn.mono f (Icc_subset_Icc le_rfl h2))
  calc
    _ ≤ eVariationOn f (Icc (0 : ℝ) (τ (2 * n) : ℝ)) := hsum n
    _ ≤ eVariationOn f (Icc (0 : ℝ) 1) :=
      eVariationOn.mono f (Icc_subset_Icc le_rfl (τ (2 * n)).property.2)
    _ = pathLength D p := (hcurve _ _ _).symm

/-- A continuous real function that starts below `r` and ends above `R`
has a subinterval crossing `[r, R]` while staying inside it. -/
theorem exists_interval_crossing {f : ℝ → ℝ} (hf : Continuous f) {r R : ℝ}
    (hrR : r ≤ R) (hstart : f 0 ≤ r) (hend : R ≤ f 1) :
    ∃ u v : ℝ, 0 ≤ u ∧ u ≤ v ∧ v ≤ 1 ∧ f u = r ∧ f v = R ∧
      (∀ t ∈ Icc u v, r ≤ f t ∧ f t ≤ R) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, R ≤ f t → v ≤ t := by
  let S : Set ℝ := Icc 0 1 ∩ f ⁻¹' {R}
  have hSc : IsCompact S := isCompact_Icc.of_isClosed_subset
    (isClosed_Icc.inter (isClosed_singleton.preimage hf)) inter_subset_left
  have hS : S.Nonempty := by
    obtain ⟨v, hv, hvR⟩ := intermediate_value_Icc zero_le_one hf.continuousOn
      (show R ∈ Icc (f 0) (f 1) from ⟨hstart.trans hrR, hend⟩)
    exact ⟨v, hv, hvR⟩
  obtain ⟨v, hvS, hvleast⟩ := hSc.exists_isLeast hS
  have hv : v ∈ Icc (0 : ℝ) 1 := hvS.1
  have hvR : f v = R := hvS.2
  let T : Set ℝ := Icc 0 v ∩ f ⁻¹' {r}
  have hTc : IsCompact T := isCompact_Icc.of_isClosed_subset
    (isClosed_Icc.inter (isClosed_singleton.preimage hf)) inter_subset_left
  have hT : T.Nonempty := by
    obtain ⟨u, hu, hur⟩ := intermediate_value_Icc hv.1 hf.continuousOn
      (show r ∈ Icc (f 0) (f v) from ⟨hstart, by rw [hvR]; exact hrR⟩)
    exact ⟨u, hu, hur⟩
  obtain ⟨u, huT, hugreatest⟩ := hTc.exists_isGreatest hT
  have hu : u ∈ Icc (0 : ℝ) v := huT.1
  have hur : f u = r := huT.2
  refine ⟨u, v, hu.1, hu.2, hv.2, hur, hvR, ?_, ?_⟩
  · intro t ht
    constructor
    · by_contra h
      have hlt : f t < r := lt_of_not_ge h
      obtain ⟨w, hw, hwr⟩ := intermediate_value_Icc ht.2 hf.continuousOn
        (show r ∈ Icc (f t) (f v) from ⟨hlt.le, by rw [hvR]; exact hrR⟩)
      have hwT : w ∈ T := ⟨⟨hu.1.trans (ht.1.trans hw.1), hw.2⟩, hwr⟩
      have huw := hugreatest hwT
      have hwt : w ≠ t := by intro h; subst w; linarith
      linarith [ht.1, lt_of_le_of_ne hw.1 (Ne.symm hwt)]
    · by_contra h
      have hlt : R < f t := lt_of_not_ge h
      obtain ⟨w, hw, hwR⟩ := intermediate_value_Icc (hu.1.trans ht.1) hf.continuousOn
        (show R ∈ Icc (f 0) (f t) from ⟨hstart.trans hrR, hlt.le⟩)
      have hwS : w ∈ S := ⟨⟨hw.1, hw.2.trans (ht.2.trans hv.2)⟩, hwR⟩
      have hvw := hvleast hwS
      have hwt : w ≠ t := by intro h; subst w; linarith
      linarith [ht.2, lt_of_le_of_ne hw.2 hwt]

  · intro t ht htR
    obtain ⟨w, hw, hwR⟩ := intermediate_value_Icc ht.1 hf.continuousOn
      (show R ∈ Icc (f 0) (f t) from ⟨hstart.trans hrR, htR⟩)
    exact (hvleast ⟨⟨hw.1, hw.2.trans ht.2⟩, hwR⟩).trans hw.2

/-- A finite family of disjoint ordered radial bands has ordered crossing
intervals. Each interval stays inside its own band. -/
theorem exists_ordered_interval_crossings {f : ℝ → ℝ} (hf : Continuous f)
    (r R : ℕ → ℝ) (n : ℕ)
    (hstart : ∀ i < n, f 0 ≤ r i) (hband : ∀ i < n, r i ≤ R i)
    (hend : ∀ i < n, R i ≤ f 1)
    (hordered : ∀ i j, i < j → j < n → R i ≤ r j) :
    ∃ u v : ℕ → ℝ,
      (∀ i < n, 0 ≤ u i ∧ u i ≤ v i ∧ v i ≤ 1 ∧ f (u i) = r i ∧
        f (v i) = R i ∧ ∀ t ∈ Icc (u i) (v i), r i ≤ f t ∧ f t ≤ R i) ∧
      ∀ i j, i < j → j < n → v i ≤ u j := by
  have hex : ∀ i : ℕ, ∃ a b : ℝ, i < n →
      0 ≤ a ∧ a ≤ b ∧ b ≤ 1 ∧ f a = r i ∧ f b = R i ∧
      (∀ t ∈ Icc a b, r i ≤ f t ∧ f t ≤ R i) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, R i ≤ f t → b ≤ t := by
    intro i
    by_cases hi : i < n
    · obtain ⟨a, b, ha, hab, hb, hfa, hfb, hinside, hfirst⟩ :=
        exists_interval_crossing hf (hband i hi) (hstart i hi) (hend i hi)
      exact ⟨a, b, fun _ => ⟨ha, hab, hb, hfa, hfb, hinside, hfirst⟩⟩
    · exact ⟨0, 0, fun h => (hi h).elim⟩
  choose u v huv using hex
  refine ⟨u, v, ?_, ?_⟩
  · intro i hi
    obtain ⟨ha, hab, hb, hfa, hfb, hinside, _⟩ := huv i hi
    exact ⟨ha, hab, hb, hfa, hfb, hinside⟩
  · intro i j hij hj
    have hi : i < n := hij.trans hj
    obtain ⟨_, _, _, _, _, _, hfirst⟩ := huv i hi
    obtain ⟨huj, huvj, hvj, hfj, _, _, _⟩ := huv j hj
    apply hfirst (u j) ⟨huj, huvj.trans hvj⟩
    rw [hfj]
    exact hordered i j hij hj

/-- Interleave finitely many ordered pairs of unit-interval times into a
monotone sequence, padding after the last pair by the endpoint. -/
theorem exists_monotone_interleaving (a b : ℕ → unitInterval) (n : ℕ)
    (hab : ∀ i < n, a i ≤ b i)
    (hba : ∀ i, i + 1 < n → b i ≤ a (i + 1)) :
    ∃ τ : ℕ → unitInterval, Monotone τ ∧
      ∀ i < n, τ (2 * i) = a i ∧ τ (2 * i + 1) = b i := by
  let A : ℕ → unitInterval := fun i => if i < n then a i else 1
  let B : ℕ → unitInterval := fun i => if i < n then b i else 1
  have hAB (i : ℕ) : A i ≤ B i := by
    by_cases hi : i < n
    · simpa [A, B, hi] using hab i hi
    · simp [A, B, hi]
  have hBA (i : ℕ) : B i ≤ A (i + 1) := by
    by_cases hi : i + 1 < n
    · have hi' : i < n := by omega
      simpa [A, B, hi, hi'] using hba i hi
    · change B i ≤ (if i + 1 < n then a (i + 1) else 1)
      simp [hi]
      exact (B i).property.2
  let τ : ℕ → unitInterval := fun k => if k % 2 = 0 then A (k / 2) else B (k / 2)
  refine ⟨τ, ?_, ?_⟩
  · apply monotone_nat_of_le_succ
    intro k
    by_cases hk : k % 2 = 0
    · have he : (k + 1) % 2 ≠ 0 := by omega
      have hd : (k + 1) / 2 = k / 2 := by omega
      simpa [τ, hk, he, hd] using hAB (k / 2)
    · have he : (k + 1) % 2 = 0 := by omega
      have hd : (k + 1) / 2 = k / 2 + 1 := by omega
      simpa [τ, hk, he, hd] using hBA (k / 2)
  · intro i hi
    have hd : (2 * i + 1) / 2 = i := by omega
    simp [τ, A, B, hi, hd]

/-- A path spanning finitely many ordered radial bands has ordered crossing
subpaths inside their respective closed annuli. -/
theorem exists_path_ordered_radial_crossings {x y center : ℂ} (p : Path x y)
    (r R : ℕ → ℝ) (n : ℕ)
    (hstart : ∀ i < n, dist x center ≤ r i)
    (hband : ∀ i < n, r i ≤ R i) (hend : ∀ i < n, R i ≤ dist y center)
    (hordered : ∀ i j, i < j → j < n → R i ≤ r j) :
    ∃ τ : ℕ → unitInterval, Monotone τ ∧
      ∀ i < n, p (τ (2 * i)) ∈ sphere center (r i) ∧
        p (τ (2 * i + 1)) ∈ sphere center (R i) ∧
        ∀ t, r i ≤ dist ((p.subpath (τ (2 * i)) (τ (2 * i + 1))) t) center ∧
          dist ((p.subpath (τ (2 * i)) (τ (2 * i + 1))) t) center ≤ R i := by
  let f : ℝ → ℝ := fun t => dist (p.extend t) center
  have hf : Continuous f := p.continuous_extend.dist continuous_const
  obtain ⟨u, v, huv, horder⟩ := exists_ordered_interval_crossings hf r R n
    (by simpa [f] using hstart) hband (by simpa [f] using hend) hordered
  let a : ℕ → unitInterval := fun i =>
    if hi : i < n then ⟨u i, ⟨(huv i hi).1, (huv i hi).2.1.trans (huv i hi).2.2.1⟩⟩ else 0
  let b : ℕ → unitInterval := fun i =>
    if hi : i < n then ⟨v i, ⟨(huv i hi).1.trans (huv i hi).2.1, (huv i hi).2.2.1⟩⟩ else 0
  have ha (i : ℕ) (hi : i < n) : (a i : ℝ) = u i := by simp [a, hi]
  have hb (i : ℕ) (hi : i < n) : (b i : ℝ) = v i := by simp [b, hi]
  have hab (i : ℕ) (hi : i < n) : a i ≤ b i := by
    change (a i : ℝ) ≤ (b i : ℝ)
    rw [ha i hi, hb i hi]
    exact (huv i hi).2.1
  have hba (i : ℕ) (hi : i + 1 < n) : b i ≤ a (i + 1) := by
    have hi' : i < n := by omega
    change (b i : ℝ) ≤ (a (i + 1) : ℝ)
    rw [hb i hi', ha (i + 1) hi]
    exact horder i (i + 1) (by omega) hi
  obtain ⟨τ, hτ, hτeq⟩ := exists_monotone_interleaving a b n hab hba
  refine ⟨τ, hτ, ?_⟩
  intro i hi
  obtain ⟨ht1, ht2⟩ := hτeq i hi
  rw [ht1, ht2]
  have hfa : f (u i) = r i := (huv i hi).2.2.2.1
  have hfb : f (v i) = R i := (huv i hi).2.2.2.2.1
  have hext (t : unitInterval) : p.extend t = p t := Path.extend_apply _ t.property
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_sphere, ← hext, ha i hi]
    exact hfa
  · rw [mem_sphere, ← hext, hb i hi]
    exact hfb
  · intro t
    have hmem : (p.subpath (a i) (b i)) t ∈ p '' Icc (a i) (b i) := by
      rw [← Path.range_subpath_of_le p (a i) (b i) (hab i hi)]
      exact mem_range_self t
    obtain ⟨z, hz, hzval⟩ := hmem
    have hz' : (z : ℝ) ∈ Icc (u i) (v i) := by
      change (a i : ℝ) ≤ z ∧ (z : ℝ) ≤ b i at hz
      simpa [ha i hi, hb i hi] using hz
    have hinside := (huv i hi).2.2.2.2.2 _ hz'
    dsimp only [f] at hinside
    rw [hext z, hzval] at hinside
    exact hinside

/-- If a path has ordered subpaths crossing the listed closed annuli, the
sum of their crossing lengths is bounded by its length. -/
theorem IsEuclideanLengthMetric.sum_radialAnnulusCrossingLength_le_pathLength
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {x y center : ℂ} (p : Path x y) (r R : ℕ → ℝ)
    (τ : ℕ → unitInterval) (hτ : Monotone τ) (n : ℕ)
    (hcross : ∀ i < n,
      p (τ (2 * i)) ∈ sphere center (r i) ∧
      p (τ (2 * i + 1)) ∈ sphere center (R i) ∧
      ∀ t, r i ≤ dist ((p.subpath (τ (2 * i)) (τ (2 * i + 1))) t) center ∧
        dist ((p.subpath (τ (2 * i)) (τ (2 * i + 1))) t) center ≤ R i) :
    (∑ i ∈ Finset.range n, radialAnnulusCrossingLength D center (r i) (R i)) ≤
      pathLength D p := by
  calc
    _ ≤ ∑ i ∈ Finset.range n, pathLength D (p.subpath (τ (2 * i)) (τ (2 * i + 1))) := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨ha, hb, hp⟩ := hcross i (Finset.mem_range.mp hi)
      exact radialAnnulusCrossingLength_le_pathLength ha hb _ hp
    _ ≤ pathLength D p := hD.sum_pathLength_subpaths_le p τ hτ n

/-- An ordered crossing decomposition for every path gives a lower bound for
metric distance, without using compactness or geodesics. -/
theorem IsEuclideanLengthMetric.sum_radialAnnulusCrossingLength_le_of_crossings
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {x y center : ℂ} (r R : ℕ → ℝ) (n : ℕ)
    (hcross : ∀ p : Path x y, ∃ τ : ℕ → unitInterval, Monotone τ ∧
      ∀ i < n, p (τ (2 * i)) ∈ sphere center (r i) ∧
        p (τ (2 * i + 1)) ∈ sphere center (R i) ∧
        ∀ t, r i ≤ dist ((p.subpath (τ (2 * i)) (τ (2 * i + 1))) t) center ∧
          dist ((p.subpath (τ (2 * i)) (τ (2 * i + 1))) t) center ≤ R i) :
    (∑ i ∈ Finset.range n, radialAnnulusCrossingLength D center (r i) (R i)) ≤
      ENNReal.ofReal (D x y) := by
  rw [hD.ofReal_eq_internalMetric]
  unfold internalMetric
  refine le_iInf fun p => le_iInf fun _ => ?_
  obtain ⟨τ, hτ, hp⟩ := hcross p
  exact hD.sum_radialAnnulusCrossingLength_le_pathLength p r R τ hτ n hp

/-- A path spanning ordered bands has length at least the sum of their
internal crossing lengths. -/
theorem IsEuclideanLengthMetric.sum_radialAnnulusCrossingLength_le_of_spans
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {x y center : ℂ} (r R : ℕ → ℝ) (n : ℕ)
    (hstart : ∀ i < n, dist x center ≤ r i)
    (hband : ∀ i < n, r i ≤ R i) (hend : ∀ i < n, R i ≤ dist y center)
    (hordered : ∀ i j, i < j → j < n → R i ≤ r j) :
    (∑ i ∈ Finset.range n, radialAnnulusCrossingLength D center (r i) (R i)) ≤
      ENNReal.ofReal (D x y) := by
  apply hD.sum_radialAnnulusCrossingLength_le_of_crossings r R n
  intro p
  exact exists_path_ordered_radial_crossings p r R n hstart hband hend hordered

/-- Divergent lower crossing sums for ordered expanding annuli centered at
`center` force every set bounded in `D` to be Euclidean bounded. The hypothesis
is deterministic and does not assert such lower bounds for an LQG metric. -/
theorem IsEuclideanLengthMetric.isBounded_of_divergent_radialCrossings
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (center : ℂ) (r R : ℕ → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hband : ∀ i, r i ≤ R i)
    (hordered : ∀ i j, i < j → R i ≤ r j)
    (hdiv : ∀ C : ℝ, ∃ n : ℕ, ENNReal.ofReal C <
      ∑ i ∈ Finset.range n, radialAnnulusCrossingLength D center (r i) (R i))
    (S : Set ℂ) (hS : ∃ x C, ∀ z ∈ S, D x z ≤ C) : Bornology.IsBounded S := by
  obtain ⟨x, C, hS⟩ := hS
  obtain ⟨n, hn⟩ := hdiv (D center x + C)
  apply (Metric.isBounded_closedBall : Bornology.IsBounded (closedBall center (R n))).subset
  intro z hz
  rw [mem_closedBall]
  by_contra h
  have hzR : R n ≤ dist z center := (lt_of_not_ge h).le
  have hsum := hD.sum_radialAnnulusCrossingLength_le_of_spans r R n
    (center := center) (x := center) (y := z)
    (by intro i hi; simpa using hr i)
    (by intro i hi; exact hband i)
    (by intro i hi; exact (hordered i n hi).trans ((hband n).trans hzR))
    (by intro i j hij hj; exact hordered i j hij)
  have hbound : D center z ≤ D center x + C :=
    (hD.triangle center x z).trans (add_le_add le_rfl (hS z hz))
  exact (not_lt_of_ge (hsum.trans (ENNReal.ofReal_le_ofReal hbound))) hn

/-- Divergent sums of lower bounds for radial crossing lengths imply that
`D`-bounded sets are Euclidean bounded. -/
theorem IsEuclideanLengthMetric.isBounded_of_radialCrossing_lowerBounds
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (center : ℂ) (r R : ℕ → ℝ) (a : ℕ → ℝ≥0∞)
    (hr : ∀ i, 0 ≤ r i) (hband : ∀ i, r i ≤ R i)
    (hordered : ∀ i j, i < j → R i ≤ r j)
    (ha : ∀ i, a i ≤ radialAnnulusCrossingLength D center (r i) (R i))
    (hdiv : ∀ C : ℝ, ∃ n : ℕ, ENNReal.ofReal C < ∑ i ∈ Finset.range n, a i)
    (S : Set ℂ) (hS : ∃ x C, ∀ z ∈ S, D x z ≤ C) : Bornology.IsBounded S := by
  apply hD.isBounded_of_divergent_radialCrossings center r R hr hband hordered ?_ S hS
  intro C
  obtain ⟨n, hn⟩ := hdiv C
  refine ⟨n, hn.trans_le ?_⟩
  exact Finset.sum_le_sum fun i _ => ha i


end HarmonicBalls
