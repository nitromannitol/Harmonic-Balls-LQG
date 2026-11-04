import HarmonicBalls.Proofs.Sec5.NestedDomainLocality

/-! # First-contact horizons along open-domain exhaustions -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

universe u

/-- A compact set covered by an increasing sequence of open sets is contained
in one member of the sequence. -/
theorem IsCompact.subset_monotone_open_iUnion {K : Set ℂ} (hK : IsCompact K)
    {U : ℕ → Set ℂ} (hopen : ∀ n, IsOpen (U n)) (hmono : Monotone U)
    (hsub : K ⊆ ⋃ n, U n) : ∃ n, K ⊆ U n := by
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover U hopen hsub
  refine ⟨s.sup id, ?_⟩
  intro x hx
  obtain ⟨n, hn, hxn⟩ := mem_iUnion₂.mp (hs hx)
  exact hmono (Finset.le_sup (f := id) hn) hxn

/-- The exact compact-containment horizon in an increasing union of open sets
is the supremum of the horizons in the exhausting domains. -/
theorem exact_containment_horizon_iSup
    {A : ℝ → Set ℂ} {U : ℕ → Set ℂ} (hopen : ∀ n, IsOpen (U n))
    (hmono : Monotone U) (hcompact : ∀ t : ℝ, 0 < t → IsCompact (closure (A t)))
    {H : ℕ → ℝ≥0∞} {K : ℝ≥0∞}
    (hH : ∀ (n : ℕ) (t : ℝ), 0 < t → (ENNReal.ofReal t < H n ↔ closure (A t) ⊆ U n))
    (hK : ∀ t : ℝ, 0 < t → (ENNReal.ofReal t < K ↔ closure (A t) ⊆ ⋃ n, U n)) :
    Monotone H ∧ (⨆ n, H n) = K := by
  have hle : ∀ n m : ℕ, n ≤ m → H n ≤ H m := by
    intro n m hnm
    exact exact_containment_horizon_mono (hmono hnm) (hH n) (hH m)
  have hleK : ∀ n, H n ≤ K := fun n =>
    exact_containment_horizon_mono (subset_iUnion U n) (hH n) hK
  refine ⟨hle, le_antisymm (iSup_le hleK) ?_⟩
  by_contra hn
  obtain ⟨q, hqlo, hqhi⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp (lt_of_not_ge hn)
  have hqpos : 0 < (q : ℝ) := by
    have hqpos' : 0 < (q : ℝ≥0∞) := lt_of_le_of_lt bot_le hqlo
    exact_mod_cast hqpos'
  have hqK : ENNReal.ofReal (q : ℝ) < K := by simpa using hqhi
  have hqU := (hK q hqpos).mp hqK
  obtain ⟨n, hn⟩ := IsCompact.subset_monotone_open_iUnion (hcompact q hqpos) hopen hmono hqU
  have hqn := (hH n q hqpos).mpr hn
  have hsup : ENNReal.ofReal (q : ℝ) < ⨆ n, H n := lt_of_lt_of_le hqn (le_iSup H n)
  have hlo : (⨆ n, H n) < ENNReal.ofReal (q : ℝ) := by simpa using hqlo
  exact (not_lt_of_ge hsup.le) hlo

/-- For an increasing open exhaustion, one can choose a horizon measurable
in each exhausting domain, extended by zero outside it, whose values increase
to the field-local horizon in the union. The assertion holds simultaneously
for all centres. The locality input is proposed and awaits source review. -/
theorem exists_fieldLocal_horizons_of_open_exhaustion
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc)
    (U : ℕ → Set ℂ) (hopen : ∀ n, IsOpen (U n)) (hmono : Monotone U)
    {Λ : Ω → ℂ → ℝ → Set ℂ}
    (hΛ : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (μ ω) (Λ ω z) z) :
    ∃ H : ℕ → Ω → ((⋃ n, U n) → ℝ≥0∞),
      ∃ K : Ω → ((⋃ n, U n) → ℝ≥0∞),
      (∀ n, Measurable[fieldSigmaAlgebra α₀ hC (U n)] (H n)) ∧
      Measurable[fieldSigmaAlgebra α₀ hC (⋃ n, U n)] K ∧
      ∀ᵐ ω ∂P, ∀ z : (⋃ n, U n),
        (∀ n, (z : ℂ) ∉ U n → H n ω z = 0) ∧
        (∀ (n : ℕ) (t : ℝ), 0 < t →
          (ENNReal.ofReal t < H n ω z ↔ closure (Λ ω z t) ⊆ U n)) ∧
        (∀ t : ℝ, 0 < t →
          (ENNReal.ofReal t < K ω z ↔ closure (Λ ω z t) ⊆ ⋃ n, U n)) ∧
        Monotone (fun n => H n ω z) ∧ (⨆ n, H n ω z) = K ω z ∧
        Tendsto (fun n => H n ω z) atTop (𝓝 (K ω z)) := by
  classical
  choose H hH hHchar using fun n : ℕ => exists_fieldLocal_open_exact_containment_horizons
    hI2 hγ hγ2 hα hGFF hμ hloc (hopen n) hΛ
  obtain ⟨K, hK, hKchar⟩ := exists_fieldLocal_open_exact_containment_horizons
    hI2 hγ hγ2 hα hGFF hμ hloc (isOpen_iUnion hopen) hΛ
  let S := ⋃ n, U n
  let H' : ℕ → Ω → S → ℝ≥0∞ := fun n ω z =>
    if hz : (z : ℂ) ∈ U n then H n ω ⟨z, hz⟩ else 0
  have hH' (n : ℕ) : Measurable[fieldSigmaAlgebra α₀ hC (U n)] (H' n) := by
    let : MeasurableSpace Ω := fieldSigmaAlgebra α₀ hC (U n)
    apply Measurable.of_eval
    intro z
    by_cases hz : (z : ℂ) ∈ U n
    · simpa only [H', dite_eq_left hz, Function.comp_def] using
        (measurable_pi_apply (⟨(z : ℂ), hz⟩ : U n)).comp (hH n)
    · simpa only [H', dite_eq_right hz] using (measurable_const : Measurable (fun _ : Ω => (0 : ℝ≥0∞)))
  refine ⟨H', K, hH', hK, ?_⟩
  filter_upwards [ae_all_iff.mpr hHchar, hKchar, hΛ] with ω hHω hKω hΛω
  intro z
  have hchar : ∀ (n : ℕ) (t : ℝ), 0 < t →
      (ENNReal.ofReal t < H' n ω z ↔ closure (Λ ω z t) ⊆ U n) := by
    intro n t ht
    by_cases hz : (z : ℂ) ∈ U n
    · simpa only [H', dite_eq_left hz] using hHω n ⟨z, hz⟩ t ht
    · simp only [H', dite_eq_right hz, not_lt_zero, false_iff]
      intro hsub
      exact hz (hsub (subset_closure ((hΛω z).1.mem t ht)))
  have hcompact : ∀ t : ℝ, 0 < t → IsCompact (closure (Λ ω z t)) := by
    intro t ht
    exact Metric.isCompact_of_isClosed_isBounded isClosed_closure ((hΛω z).1.isBounded t ht).closure
  have hlim := exact_containment_horizon_iSup hopen hmono hcompact hchar (hKω z)
  refine ⟨?_, hchar, hKω z, hlim.1, hlim.2, ?_⟩
  · intro n hz
    simp only [H', dite_eq_right hz]
  · simpa only [hlim.2] using tendsto_atTop_iSup hlim.1

/-- The exact containment horizon of the whole plane is infinite. -/
theorem exact_containment_horizon_univ {A : ℝ → Set ℂ} {K : ℝ≥0∞}
    (hK : ∀ t : ℝ, 0 < t → (ENNReal.ofReal t < K ↔ closure (A t) ⊆ univ)) :
    K = ⊤ := by
  by_contra hn
  have hk : K < ⊤ := lt_top_iff_ne_top.mpr hn
  obtain ⟨q, hqlo, _⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hk
  have hqpos : 0 < (q : ℝ) := by
    have hqpos' : 0 < (q : ℝ≥0∞) := lt_of_le_of_lt bot_le hqlo
    exact_mod_cast hqpos'
  have hqK : ENNReal.ofReal (q : ℝ) < K := (hK q hqpos).mpr (subset_univ _)
  have hqlo' : K < ENNReal.ofReal (q : ℝ) := by simpa using hqlo
  exact (not_lt_of_ge hqK.le) hqlo'

/-- Along any increasing open exhaustion of the plane, the field-local exact
horizons tend to infinity simultaneously for all centres. The locality input
is proposed and awaits source review. -/
theorem exists_fieldLocal_horizons_diverging_of_open_exhaustion
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc)
    (U : ℕ → Set ℂ) (hopen : ∀ n, IsOpen (U n)) (hmono : Monotone U)
    (hcover : (⋃ n, U n) = univ)
    {Λ : Ω → ℂ → ℝ → Set ℂ}
    (hΛ : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (μ ω) (Λ ω z) z) :
    ∃ H : ℕ → Ω → ((⋃ n, U n) → ℝ≥0∞),
      (∀ n, Measurable[fieldSigmaAlgebra α₀ hC (U n)] (H n)) ∧
      ∀ᵐ ω ∂P, ∀ z : (⋃ n, U n),
        (∀ n, (z : ℂ) ∉ U n → H n ω z = 0) ∧
        (∀ (n : ℕ) (t : ℝ), 0 < t →
          (ENNReal.ofReal t < H n ω z ↔ closure (Λ ω z t) ⊆ U n)) ∧
        Monotone (fun n => H n ω z) ∧ (⨆ n, H n ω z) = ⊤ ∧
        Tendsto (fun n => H n ω z) atTop (𝓝 ⊤) := by
  obtain ⟨H, K, hH, _, hK⟩ := exists_fieldLocal_horizons_of_open_exhaustion
    hI2 hγ hγ2 hα hGFF hμ hloc U hopen hmono hΛ
  refine ⟨H, hH, ?_⟩
  filter_upwards [hK] with ω hKω
  intro z
  have htop : K ω z = ⊤ := exact_containment_horizon_univ (by
    simpa only [hcover] using (hKω z).2.2.1)
  exact ⟨(hKω z).1, (hKω z).2.1, (hKω z).2.2.2.1,
    (hKω z).2.2.2.2.1.trans htop, by simpa only [htop] using (hKω z).2.2.2.2.2⟩

#print axioms IsCompact.subset_monotone_open_iUnion
#print axioms exact_containment_horizon_iSup
#print axioms exists_fieldLocal_horizons_of_open_exhaustion
#print axioms exact_containment_horizon_univ
#print axioms exists_fieldLocal_horizons_diverging_of_open_exhaustion

end HarmonicBalls
