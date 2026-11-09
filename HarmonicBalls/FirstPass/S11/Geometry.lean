import HarmonicBalls.Defs.Geometry

/-!
# Section 11 geometry: Lipschitz domains satisfy the cone condition

NEW helper for Proposition 11.2 (`prop:not-balls`, paper line 2816). The printed proof (line 3010) says
"one easily gets from Definition 11.1 that every Lipschitz domain satisfies the cone condition at each of its
boundary points". This module proves that statement (`isLipschitzDomain_satisfiesConeCondition`) and the cone
facts it uses. It is deterministic plane geometry; no probability and no external input.

Cones: `openSector v w` and `IsCone` are those of `Defs/Geometry.lean` (Definition 11.3). The cones used here are
`{x : Im x < -c |Re x|}` and `{x : Im x > c |Re x|}` (`c = K + 1` for a Lipschitz constant `K`), transported by
the linear isometry `e` of Definition 11.1.
-/

open Metric Set Filter Topology

namespace HarmonicBalls

namespace FirstPassS11

/-- The downward sector `{x : Im x < -c |Re x|}` for `c > 0`. -/
def downSector (c : ℝ) : Set ℂ :=
  {x | x.im < -c * |x.re|}

/-- The upward sector `{x : Im x > c |Re x|}` for `c > 0`. -/
def upSector (c : ℝ) : Set ℂ :=
  {x | c * |x.re| < x.im}

lemma downSector_eq_openSector {c : ℝ} (hc : 0 < c) :
    downSector c = openSector (1 - (c : ℂ) * Complex.I) (-1 - (c : ℂ) * Complex.I) := by
  ext x
  simp only [downSector, openSector, mem_ofPred_eq]
  constructor
  · intro hx
    have hs : |x.re| < -x.im / c := by
      rw [lt_div_iff₀ hc]; linarith
    have h1 := le_abs_self x.re
    have h2 := neg_abs_le x.re
    refine ⟨(-x.im / c + x.re) / 2, (-x.im / c - x.re) / 2, by linarith, by linarith, ?_⟩
    apply Complex.ext <;> simp <;> field_simp <;> ring
  · rintro ⟨a, b, ha, hb, rfl⟩
    have hab : |a - b| < a + b := abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
    have key : c * |a - b| < c * (a + b) := mul_lt_mul_of_pos_left hab hc
    have him : (a • (1 - (c : ℂ) * Complex.I) + b • (-1 - (c : ℂ) * Complex.I)).im = -c * (a + b) := by
      simp; ring
    have hre : (a • (1 - (c : ℂ) * Complex.I) + b • (-1 - (c : ℂ) * Complex.I)).re = a - b := by
      simp; ring
    rw [him, hre]
    linarith [key]

lemma upSector_eq_openSector {c : ℝ} (hc : 0 < c) :
    upSector c = openSector (-1 + (c : ℂ) * Complex.I) (1 + (c : ℂ) * Complex.I) := by
  ext x
  simp only [upSector, openSector, mem_ofPred_eq]
  constructor
  · intro hx
    have hs : |x.re| < x.im / c := by
      rw [lt_div_iff₀ hc]; linarith
    have h1 := le_abs_self x.re
    have h2 := neg_abs_le x.re
    refine ⟨(x.im / c - x.re) / 2, (x.im / c + x.re) / 2, by linarith, by linarith, ?_⟩
    apply Complex.ext <;> simp <;> field_simp <;> ring
  · rintro ⟨a, b, ha, hb, rfl⟩
    have hab : |b - a| < a + b := abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
    have key : c * |b - a| < c * (a + b) := mul_lt_mul_of_pos_left hab hc
    have him : (a • (-1 + (c : ℂ) * Complex.I) + b • (1 + (c : ℂ) * Complex.I)).im = c * (a + b) := by
      simp; ring
    have hre : (a • (-1 + (c : ℂ) * Complex.I) + b • (1 + (c : ℂ) * Complex.I)).re = b - a := by
      simp; ring
    rw [him, hre]
    linarith [key]

/-- Transport of a sector to the preimage under a linear isometry `e` is again a cone (Definition 11.3). -/
lemma isCone_preimage_of_openSector (e : ℂ ≃ₗᵢ[ℝ] ℂ) {S : Set ℂ} {v w : ℂ} (hv : v ≠ 0) (hw : w ≠ 0)
    (hS : S = openSector v w) (hSo : IsOpen S) (hS0 : (0 : ℂ) ∉ S) (hSne : S.Nonempty) :
    IsCone (e ⁻¹' S) := by
  have hpre : e ⁻¹' S = openSector (e.symm v) (e.symm w) := by
    ext x
    simp only [hS, mem_preimage, openSector, mem_ofPred_eq]
    constructor
    · rintro ⟨c', d', hc', hd', h⟩
      refine ⟨c', d', hc', hd', ?_⟩
      apply e.injective
      rw [map_add, map_smul, map_smul, e.apply_symm_apply, e.apply_symm_apply]
      exact h
    · rintro ⟨c', d', hc', hd', h⟩
      refine ⟨c', d', hc', hd', ?_⟩
      have := congrArg e h
      rw [map_add, map_smul, map_smul, e.apply_symm_apply, e.apply_symm_apply] at this
      exact this
  left
  refine ⟨?_, hSo.preimage e.continuous, ?_, e.symm v, e.symm w, ?_, ?_, hpre⟩
  · obtain ⟨p, hp⟩ := hSne
    exact ⟨e.symm p, by simpa using hp⟩
  · intro h
    apply hS0
    have h0 : (0 : ℂ) ∈ e ⁻¹' S := h ▸ mem_univ _
    simpa using h0
  · intro h
    apply hv
    have := congrArg e h
    simpa using this
  · intro h
    apply hw
    have := congrArg e h
    simpa using this

/-- The interior and exterior cone sectors of Lemma 11.5 and Proposition 11.2 are given by the two lemmas below. -/
lemma isOpen_downSector (c : ℝ) : IsOpen (downSector c) :=
  isOpen_lt Complex.continuous_im (by fun_prop)

lemma isOpen_upSector (c : ℝ) : IsOpen (upSector c) :=
  isOpen_lt (by fun_prop) Complex.continuous_im

lemma zero_not_mem_downSector (c : ℝ) : (0 : ℂ) ∉ downSector c := by
  simp [downSector]

lemma zero_not_mem_upSector (c : ℝ) : (0 : ℂ) ∉ upSector c := by
  simp [upSector]

lemma neg_I_mem_downSector (c : ℝ) : (-Complex.I) ∈ downSector c := by
  simp [downSector]

lemma I_mem_upSector (c : ℝ) : Complex.I ∈ upSector c := by
  simp [upSector]

/-- Lipschitz domains satisfy the cone condition at each of their boundary points (the printed remark after
Definition 11.1, used in the proof of Proposition 11.2, line 3010). In the coordinates `e` of Definition 11.1 the
graph `f` passes through `x₀` (`f (e x₀).re = (e x₀).im`, from `x₀ ∈ ∂A` and `A` open); the cones
`e⁻¹' {Im < -c|Re|}` (exterior) and `e⁻¹' {Im > c|Re|}` (interior), `c = K + 1`, lie below resp. above the
epigraph of the `K`-Lipschitz `f`. -/
theorem isLipschitzDomain_satisfiesConeCondition {A : Set ℂ} (hA : IsLipschitzDomain A) {x₀ : ℂ}
    (hx₀ : x₀ ∈ frontier A) : SatisfiesConeCondition A x₀ := by
  obtain ⟨r, hr, e, K, f, hf, hloc⟩ := hA.2.2 x₀ hx₀
  have hnA : x₀ ∉ A := by
    have h2 : x₀ ∉ interior A := hx₀.2
    rwa [hA.1.interior_eq] at h2
  have hcl : x₀ ∈ closure A := hx₀.1
  have hx0ball : x₀ ∈ ball x₀ r := mem_ball_self hr
  have key : ∀ x ∈ ball x₀ r, (x ∈ A ↔ f (e x).re < (e x).im) := by
    intro x hx
    have h := Set.ext_iff.mp hloc x
    constructor
    · intro hxA
      exact (h.mp ⟨hxA, hx⟩).2
    · intro hlt
      exact (h.mpr ⟨hx, hlt⟩).1
  have hLip : ∀ s t : ℝ, |f s - f t| ≤ (K : ℝ) * |s - t| := by
    intro s t
    have := hf.dist_le_mul s t
    rwa [Real.dist_eq, Real.dist_eq] at this
  have hcont : Continuous fun x : ℂ => (e x).im - f (e x).re :=
    (Complex.continuous_im.comp e.continuous).sub
      (hf.continuous.comp (Complex.continuous_re.comp e.continuous))
  have hb_le : (e x₀).im ≤ f (e x₀).re := by
    by_contra hlt
    have hlt := not_le.mp hlt
    exact hnA ((key x₀ hx0ball).mpr hlt)
  have hf_le : f (e x₀).re ≤ (e x₀).im := by
    by_contra hlt
    have hlt := not_le.mp hlt
    have hopen : IsOpen ({x : ℂ | (e x).im - f (e x).re < 0} ∩ ball x₀ r) :=
      (isOpen_lt hcont continuous_const).inter isOpen_ball
    have hmem : x₀ ∈ ({x : ℂ | (e x).im - f (e x).re < 0} ∩ ball x₀ r) := by
      refine ⟨?_, hx0ball⟩
      show (e x₀).im - f (e x₀).re < 0
      linarith
    obtain ⟨y, ⟨hy1, hy2⟩, hyA⟩ := mem_closure_iff.mp hcl _ hopen hmem
    have h3 := (key y hy2).mp hyA
    have hy1' : (e y).im - f (e y).re < 0 := hy1
    linarith
  have hfeq : f (e x₀).re = (e x₀).im := le_antisymm hf_le hb_le
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (K : ℝ) + 1 := ⟨_, rfl⟩
  have hcpos : 0 < c := by rw [hc]; positivity
  have hcK : K ≤ c := by rw [hc]; linarith
  have hne1 : (1 - (c : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have h' := congrArg Complex.im h
    simp at h'
    linarith
  have hne2 : (-1 - (c : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have h' := congrArg Complex.im h
    simp at h'
    linarith
  have hne3 : (-1 + (c : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have h' := congrArg Complex.im h
    simp at h'
    linarith
  have hne4 : (1 + (c : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have h' := congrArg Complex.im h
    simp at h'
    linarith
  have hext : SatisfiesExteriorConeCondition A x₀ := by
    refine ⟨r, hr, e ⁻¹' downSector c, ?_, ?_⟩
    · exact isCone_preimage_of_openSector e hne1 hne2 (downSector_eq_openSector hcpos)
        (isOpen_downSector c) (zero_not_mem_downSector c) ⟨-Complex.I, neg_I_mem_downSector c⟩
    · rintro y ⟨⟨x, hxQ, rfl⟩, hyb⟩ hyA
      have hy := (key _ hyb).mp hyA
      rw [map_add, Complex.add_re, Complex.add_im] at hy
      have hxQ' : (e x).im < -c * |(e x).re| := hxQ
      have h1 := hLip ((e x).re + (e x₀).re) (e x₀).re
      have h2 : (e x).re + (e x₀).re - (e x₀).re = (e x).re := by ring
      rw [h2, hfeq] at h1
      have h3 := (abs_le.mp h1).1
      have h4 := abs_nonneg (e x).re
      have h5 : c * |(e x).re| = (K : ℝ) * |(e x).re| + |(e x).re| := by rw [hc]; ring
      linarith
  have hint : SatisfiesInteriorConeCondition A x₀ := by
    refine ⟨r, hr, e ⁻¹' upSector c, ?_, ?_⟩
    · exact isCone_preimage_of_openSector e hne3 hne4 (upSector_eq_openSector hcpos)
        (isOpen_upSector c) (zero_not_mem_upSector c) ⟨Complex.I, I_mem_upSector c⟩
    · rintro y ⟨⟨x, hxQ, rfl⟩, hyb⟩
      refine (key _ hyb).mpr ?_
      rw [map_add, Complex.add_re, Complex.add_im]
      have hxQ' : c * |(e x).re| < (e x).im := hxQ
      have h1 := hLip ((e x).re + (e x₀).re) (e x₀).re
      have h2 : (e x).re + (e x₀).re - (e x₀).re = (e x).re := by ring
      rw [h2, hfeq] at h1
      have h3 := (abs_le.mp h1).2
      have h4 := abs_nonneg (e x).re
      have h5 : (K : ℝ) * |(e x).re| ≤ c * |(e x).re| := mul_le_mul_of_nonneg_right hcK h4
      linarith
  exact ⟨hint, hext⟩

end FirstPassS11

#print axioms HarmonicBalls.FirstPassS11.isLipschitzDomain_satisfiesConeCondition

end HarmonicBalls
