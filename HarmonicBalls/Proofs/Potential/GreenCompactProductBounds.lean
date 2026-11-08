import HarmonicBalls.Proofs.Potential.GreenComponentPositivity

/-! # Green bounds on disjoint compact sets

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/

namespace HarmonicBalls

open Set MeasureTheory

/-- On two nonempty disjoint compact subsets of one component, the Green
kernel has strictly positive finite uniform lower and upper bounds. -/
theorem exists_pos_bounds_greenFunction_compact_product
    {U K L : Set ℂ} {w : ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hK : IsCompact K) (hL : IsCompact L) (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKC : K ⊆ connectedComponentIn U w) (hLC : L ⊆ connectedComponentIn U w)
    (hKL : Disjoint K L) :
    ∃ c C : ℝ, 0 < c ∧ ∀ z ∈ K, ∀ x ∈ L,
      c ≤ greenFunction U z x ∧ greenFunction U z x ≤ C := by
  have hKU : K ⊆ U := hKC.trans (connectedComponentIn_subset U w)
  have hLU : L ⊆ U := hLC.trans (connectedComponentIn_subset U w)
  have hne : ∀ z ∈ K, ∀ x ∈ L, z ≠ x := by
    intro z hz x hx heq
    exact disjoint_left.mp hKL hz (heq ▸ hx)
  have hc : ContinuousOn (fun p : ℂ × ℂ => greenFunction U p.1 p.2) (K ×ˢ L) := by
    intro p hp
    exact (continuousAt_greenFunction_uncurry hU hUb (hKU hp.1) (hLU hp.2)
      (hne p.1 hp.1 p.2 hp.2)).continuousWithinAt
  have hp : ∀ p ∈ K ×ˢ L, 0 < greenFunction U p.1 p.2 := by
    intro p hp
    apply greenFunction_pos_of_mem_connectedComponentIn hU hUb (hKU hp.1)
    · rw [← connectedComponentIn_eq (hKC hp.1)]
      exact hLC hp.2
    · exact Ne.symm (hne p.1 hp.1 p.2 hp.2)
  have hprod : (K ×ˢ L).Nonempty := hKne.prod hLne
  obtain ⟨p, hpK, hpmin⟩ := (hK.prod hL).exists_isMinOn hprod hc
  obtain ⟨q, hqK, hqmax⟩ := (hK.prod hL).exists_isMaxOn hprod hc
  refine ⟨greenFunction U p.1 p.2, greenFunction U q.1 q.2, hp p hpK, ?_⟩
  intro z hz x hx
  exact ⟨hpmin (show (z, x) ∈ K ×ˢ L from ⟨hz, hx⟩),
    hqmax (show (z, x) ∈ K ×ˢ L from ⟨hz, hx⟩)⟩

/-- A finite measure charging the source compact gives a uniformly positive
restricted Green potential on the observation compact. The bound is the
kernel's uniform lower bound multiplied by the measure of the source set. -/
theorem exists_pos_lower_bound_integral_greenFunction_compact
    {U K L : Set ℂ} {w : ℂ} {μ : Measure ℂ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hK : IsCompact K) (hL : IsCompact L) (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKC : K ⊆ connectedComponentIn U w) (hLC : L ⊆ connectedComponentIn U w)
    (hKL : Disjoint K L) (hfinite : μ L < ⊤) (hμ : μ L ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ 0 < c * μ.real L ∧ ∀ z ∈ K,
      c * μ.real L ≤ ∫ x in L, greenFunction U z x ∂μ := by
  obtain ⟨c, C, hc, hb⟩ :=
    exists_pos_bounds_greenFunction_compact_product hU hUb hK hL hKne hLne hKC hLC hKL
  have hmass : 0 < μ.real L :=
    lt_of_le_of_ne measureReal_nonneg (Ne.symm ((measureReal_ne_zero_iff hfinite.ne).mpr hμ))
  refine ⟨c, hc, mul_pos hc hmass, ?_⟩
  intro z hz
  have hzU : z ∈ U := connectedComponentIn_subset U w (hKC hz)
  have hcont : ContinuousOn (greenFunction U z) L := by
    intro x hx
    have hxU : x ∈ U := connectedComponentIn_subset U w (hLC hx)
    have hzx : z ≠ x := fun heq => disjoint_left.mp hKL hz (heq ▸ hx)
    have hpair := continuousAt_greenFunction_uncurry hU hUb hzU hxU hzx
    exact (hpair.comp (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  have hi : IntegrableOn (greenFunction U z) L μ :=
    hcont.integrableOn_of_subset_isCompact hL hL.isClosed.measurableSet Subset.rfl hfinite.ne
  let _ : IsFiniteMeasure (μ.restrict L) := isFiniteMeasure_restrict.mpr hfinite.ne
  have hh : (∫ _ in L, c ∂μ) ≤ ∫ x in L, greenFunction U z x ∂μ := by
    apply integral_mono_ae (integrable_const c) hi
    filter_upwards [ae_restrict_mem hL.isClosed.measurableSet] with x hx
    exact (hb z hz x hx).1
  simpa only [setIntegral_const, smul_eq_mul, mul_comm] using hh

/-- The same positive lower bound applies to the full Green potential when
the finite measure is concentrated on the source compact. -/
theorem exists_pos_lower_bound_greenPotential_of_ae_mem_compact
    {U K L : Set ℂ} {w : ℂ} {μ : Measure ℂ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hK : IsCompact K) (hL : IsCompact L) (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKC : K ⊆ connectedComponentIn U w) (hLC : L ⊆ connectedComponentIn U w)
    (hKL : Disjoint K L) (hfinite : μ L < ⊤) (hμ : μ L ≠ 0)
    (hsupport : ∀ᵐ x ∂μ, x ∈ L) :
    ∃ c : ℝ, 0 < c ∧ 0 < c * μ.real L ∧ ∀ z ∈ K,
      c * μ.real L ≤ ∫ x, greenFunction U z x ∂μ := by
  obtain ⟨c, hc, hmass, hbound⟩ :=
    exists_pos_lower_bound_integral_greenFunction_compact hU hUb hK hL hKne hLne
      hKC hLC hKL hfinite hμ
  refine ⟨c, hc, hmass, ?_⟩
  intro z hz
  simpa only [Measure.restrict_eq_self_of_ae_mem hsupport] using hbound z hz

#print axioms exists_pos_bounds_greenFunction_compact_product
#print axioms exists_pos_lower_bound_integral_greenFunction_compact
#print axioms exists_pos_lower_bound_greenPotential_of_ae_mem_compact

end HarmonicBalls
