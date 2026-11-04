import HarmonicBalls.Steps.Sec11.ConeCoordinates

/-! # A countable cofinal family of cones -/

namespace HarmonicBalls

open Set Filter Topology

/-- Every neighbourhood of a nonzero vector contains a second direction with
strictly positive orientation. -/
theorem exists_mem_open_pos_planarCross {U : Set ℂ} (hU : IsOpen U)
    {v : ℂ} (hv : v ∈ U) (hv0 : v ≠ 0) :
    ∃ w ∈ U, 0 < planarCross v w := by
  let f : ℝ → ℂ := fun t => v + (t : ℂ) * Complex.I * v
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hnear : ∀ᶠ t in 𝓝[>] (0 : ℝ), f t ∈ U :=
    nhdsWithin_le_nhds (hf.continuousAt.eventually (by simpa [f] using hU.mem_nhds hv))
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht, hft⟩ := (hpos.and hnear).exists
  refine ⟨f t, hft, ?_⟩
  have hvnorm : 0 < v.re * v.re + v.im * v.im := by
    simpa [Complex.normSq_apply, pow_two] using Complex.normSq_pos.mpr hv0
  have hp := mul_pos ht hvnorm
  dsimp [planarCross, f]
  simp only [Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  nlinarith

/-- Every open cone contains two points of a dense set whose oriented area is
positive. -/
theorem IsOpenCone.exists_pos_pair_in_dense {Q D : Set ℂ} (hQ : IsOpenCone Q)
    (hD : Dense D) : ∃ v ∈ D, ∃ w ∈ D, v ∈ Q ∧ w ∈ Q ∧ 0 < planarCross v w := by
  obtain ⟨v, hvQ, hvD⟩ := hD.inter_open_nonempty Q hQ.2.1 hQ.1
  have hv0 : v ≠ 0 := fun he => hQ.zero_not_mem (he ▸ hvQ)
  obtain ⟨w, hwQ, hcross⟩ := exists_mem_open_pos_planarCross hQ.2.1 hvQ hv0
  have hcont : Continuous (fun w : ℂ => planarCross v w) := by unfold planarCross; fun_prop
  let V : Set ℂ := Q ∩ {w | 0 < planarCross v w}
  have hV : IsOpen V := hQ.2.1.inter (isOpen_lt continuous_const hcont)
  obtain ⟨w', hw'V, hw'D⟩ := hD.inter_open_nonempty V hV ⟨w, hwQ, hcross⟩
  exact ⟨v, hvD, w', hw'D, hvQ, hw'V.1, hw'V.2⟩

/-- There is a countable family of open cones with a member contained in
every cone of Definition 11.3. -/
theorem exists_countable_cofinal_open_cones :
    ∃ cones : ℕ → Set ℂ, (∀ i, IsOpenCone (cones i)) ∧
      ∀ Q : Set ℂ, IsCone Q → ∃ i, cones i ⊆ Q := by
  classical
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℂ
  let F : Set (Set ℂ) := {Q | ∃ v ∈ D, ∃ w ∈ D,
    0 < planarCross v w ∧ Q = openSector v w}
  have hFc : F.Countable := by
    apply ((hDc.prod hDc).image (fun p : ℂ × ℂ => openSector p.1 p.2)).mono
    rintro Q ⟨v, hv, w, hw, hcross, rfl⟩
    exact ⟨(v, w), ⟨hv, hw⟩, rfl⟩
  have hsub : ∀ Q : Set ℂ, IsOpenCone Q → ∃ V ∈ F, V ⊆ Q := by
    intro Q hQ
    obtain ⟨v, hvD, w, hwD, hvQ, hwQ, hcross⟩ := hQ.exists_pos_pair_in_dense hDd
    exact ⟨openSector v w, ⟨v, hvD, w, hwD, hcross, rfl⟩, hQ.openSector_subset hvQ hwQ⟩
  have hne : F.Nonempty := by
    obtain ⟨V, hV, _⟩ := hsub _ isOpenCone_firstQuadrant
    exact ⟨V, hV⟩
  obtain ⟨cones, hcones⟩ := hFc.exists_eq_range hne
  refine ⟨cones, ?_, ?_⟩
  · intro i
    have hi : cones i ∈ F := hcones ▸ mem_range_self i
    obtain ⟨v, _, w, _, hcross, heq⟩ := hi
    rw [heq]
    exact isOpenCone_openSector_of_planarCross_pos hcross
  · intro Q hQ
    obtain ⟨V, hV, hVQ⟩ := hQ.exists_open_subcone
    obtain ⟨W, hW, hWV⟩ := hsub V hV
    have hWrange : W ∈ range cones := hcones ▸ hW
    obtain ⟨i, hi⟩ := hWrange
    exact ⟨i, hi ▸ hWV.trans hVQ⟩

end HarmonicBalls
