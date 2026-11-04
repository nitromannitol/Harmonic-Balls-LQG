import HarmonicBalls.Proofs.Sec10.PoleAvoidingHarmonicCorrection
import HarmonicBalls.Proofs.Sec6.HarnackChain

/-! # Harnack chains for pole-avoiding components

The zero extension has a Green correction even across the pole. Harnack
chains therefore compare it with the annular Green-potential supremum from
any point outside the selected union of components.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Section6
open scoped ENNReal

/-- A Harnack chain starting outside a union of components bounds its
truncated odometer by the annular Green potential. The annulus may contain
the pole. -/
theorem truncated_odometer_le_greenPotentialSup_of_harnack_chain
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {R βminus βplus : ℝ} (hR : 0 < R) (hV : VolumeGrowth μ R βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) {t : ℝ} (ht : 0 < t)
    {c : ℂ} {a b : ℝ} (hab : a < b) (hb : 0 < b)
    (hA : annulus c a b ⊆ ball (0 : ℂ) R)
    {Λ : Set ℂ} (hΛsub : Λ ⊆ annulus c a b ∩ cluster μ R z t)
    (hcomp : ∀ x ∈ Λ, connectedComponentIn (annulus c a b ∩ cluster μ R z t) x ⊆ Λ)
    (hzΛ : z ∉ Λ) {r : ℝ} (hr : 0 < r) (p : ℕ → ℂ) (n : ℕ)
    (hp0 : p 0 ∈ annulus c a b) (hzero : p 0 ∉ Λ)
    (hdisc : ∀ i < n, closedBall (p i) r ⊆ annulus c a b)
    (hstep : ∀ i < n, p (i + 1) ∈ closedBall (p i) (r / 2)) :
    ENNReal.ofReal (Λ.indicator (odometer μ R z t) (p n)) ≤
      ENNReal.ofReal ((4 : ℝ) ^ n) * annulusGreenPotentialSup μ c a b := by
  classical
  obtain ⟨q, _, hq0, hqbound, hsum0, hharm⟩ :=
    exists_pole_avoiding_annulus_classical_harmonic_correction
      hμ hR hV hz ht hab hb hA hΛsub hcomp hzΛ
  have hchain := harmonic_le_of_harnack_chain hharm hsum0 hr p n hdisc hstep
  have hle : Λ.indicator (odometer μ R z t) (p n) ≤ (4 : ℝ) ^ n * q (p 0) := by
    simp only [indicator_of_notMem hzero, zero_add] at hchain
    have hq := hq0 (p n)
    linarith
  calc
    ENNReal.ofReal (Λ.indicator (odometer μ R z t) (p n)) ≤
        ENNReal.ofReal ((4 : ℝ) ^ n * q (p 0)) := ENNReal.ofReal_le_ofReal hle
    _ = ENNReal.ofReal ((4 : ℝ) ^ n) * ENNReal.ofReal (q (p 0)) :=
      ENNReal.ofReal_mul (by positivity)
    _ ≤ ENNReal.ofReal ((4 : ℝ) ^ n) * annulusGreenPotentialSup μ c a b :=
      by simpa only [mul_comm] using
        (mul_le_mul_left (hqbound (p 0) hp0) (ENNReal.ofReal ((4 : ℝ) ^ n)))

/-- Uniformly bounded Harnack chains from a point outside the selected
component union control the odometer on that union. -/
theorem truncated_odometer_iSup_le_greenPotentialSup_of_harnack_chains
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {βminus βplus : ℝ} (hV : VolumeGrowth μ 1 βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) {t : ℝ} (ht : 0 < t)
    {c : ℂ} {a b : ℝ} (hab : a < b) (hb : 0 < b)
    (hA : annulus c a b ⊆ ball (0 : ℂ) 1)
    {Λ : Set ℂ} (hΛsub : Λ ⊆ annulus c a b ∩ cluster μ 1 z t)
    (hcomp : ∀ x ∈ Λ, connectedComponentIn (annulus c a b ∩ cluster μ 1 z t) x ⊆ Λ)
    (hzΛ : z ∉ Λ) {y : ℂ} (hy : y ∈ annulus c a b) (hyΛ : y ∉ Λ)
    {K : Set ℂ} {r : ℝ} (hr : 0 < r) (N : ℕ)
    (hchains : ∀ x ∈ K ∩ Λ, ∃ p : ℕ → ℂ,
      p 0 = y ∧ p N = x ∧
      (∀ i < N, closedBall (p i) r ⊆ annulus c a b) ∧
      (∀ i < N, p (i + 1) ∈ closedBall (p i) (r / 2))) :
    ⨆ x ∈ K ∩ Λ, odometerExt μ z t x ≤
      ENNReal.ofReal ((4 : ℝ) ^ N) * annulusGreenPotentialSup μ c a b := by
  classical
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  obtain ⟨p, hp0, hpN, hdisc, hstep⟩ := hchains x hx
  have hbound := truncated_odometer_le_greenPotentialSup_of_harnack_chain
    hμ (by norm_num) hV hz ht hab hb hA hΛsub hcomp hzΛ hr p N
    (by simpa only [hp0] using hy) (by simpa only [hp0] using hyΛ) hdisc hstep
  have hxz : x ≠ z := fun h => hzΛ (h ▸ hx.2)
  simpa only [hpN, indicator_of_mem hx.2, odometerExt, hxz, ↓reduceIte] using hbound

/-- A local component inherits the chain bound on each annulus contained in
its ambient open set, even when that annulus contains the pole. -/
theorem component_odometer_iSup_le_greenPotentialSup_of_harnack_chains
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {βminus βplus : ℝ} (hV : VolumeGrowth μ 1 βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) {t : ℝ} (ht : 0 < t)
    {U D : Set ℂ} (hUsub : U ⊆ ball (0 : ℂ) 1)
    (hD : D ∈ connectedComponentsIn (U ∩ cluster μ 1 z t)) (hzD : z ∉ D)
    {c : ℂ} {a b : ℝ} (hab : a < b) (hb : 0 < b)
    (hA : annulus c a b ⊆ U) {y : ℂ} (hy : y ∈ annulus c a b) (hyD : y ∉ D)
    {K : Set ℂ} (hKA : K ⊆ annulus c a b) {r : ℝ} (hr : 0 < r) (N : ℕ)
    (hchains : ∀ x ∈ K ∩ D, ∃ p : ℕ → ℂ,
      p 0 = y ∧ p N = x ∧
      (∀ i < N, closedBall (p i) r ⊆ annulus c a b) ∧
      (∀ i < N, p (i + 1) ∈ closedBall (p i) (r / 2))) :
    ⨆ x ∈ K ∩ D, odometerExt μ z t x ≤
      ENNReal.ofReal ((4 : ℝ) ^ N) * annulusGreenPotentialSup μ c a b := by
  obtain ⟨a₀, ha₀, hDa⟩ := hD
  have hDsub : D ⊆ U ∩ cluster μ 1 z t := by
    rw [← hDa]
    exact connectedComponentIn_subset _ _
  have hcomp : ∀ x ∈ D, connectedComponentIn (U ∩ cluster μ 1 z t) x ⊆ D := by
    intro x hx
    rw [← hDa] at hx ⊢
    exact (connectedComponentIn_eq hx).symm.subset
  obtain ⟨hLsub, hLcomp⟩ := inter_union_components_of_subset hA hDsub hcomp
  have hK : K ∩ (annulus c a b ∩ D) = K ∩ D := by
    ext x
    exact ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, hKA hx.1, hx.2⟩⟩
  have hbnd := truncated_odometer_iSup_le_greenPotentialSup_of_harnack_chains
    hμ hV hz ht hab hb (hA.trans hUsub) hLsub hLcomp (fun h => hzD h.2)
    hy (fun h => hyD h.2) (K := K) hr N (by simpa only [hK] using hchains)
  rwa [hK] at hbnd

/-- A strict mass deficit produces a point outside the selected set. -/
theorem exists_mem_sdiff_of_measure_inter_lt {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {K D : Set X} (hsmall : μ (K ∩ D) < μ K) :
    (K \ D).Nonempty := by
  by_contra h
  have hsub : K ⊆ D := by
    intro x hx
    by_contra hxD
    exact h ⟨x, hx, hxD⟩
  have heq : K ∩ D = K := inter_eq_left.mpr hsub
  rw [heq] at hsmall
  exact (lt_irrefl _ hsmall)

/-- Relative mass below one yields an anchor outside the selected set. -/
theorem exists_mem_sdiff_of_relative_mass_lt_one {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {K D : Set X} (hK0 : μ K ≠ 0) (hKtop : μ K ≠ ∞)
    {α : ℝ} (hα : α < 1)
    (hmass : μ (K ∩ D) ≤ ENNReal.ofReal α * μ K) : (K \ D).Nonempty := by
  apply exists_mem_sdiff_of_measure_inter_lt μ
  apply hmass.trans_lt
  calc ENNReal.ofReal α * μ K < 1 * μ K :=
      ENNReal.mul_lt_mul_left hK0 hKtop (ENNReal.ofReal_lt_one.2 hα)
    _ = μ K := one_mul _

/-- If the selected component has relative mass below one in the target set,
its missing point supplies the initial zero for a uniform Harnack chain. -/
theorem component_odometer_iSup_le_greenPotentialSup_of_small_mass
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {βminus βplus : ℝ} (hV : VolumeGrowth μ 1 βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) {t : ℝ} (ht : 0 < t)
    {U D : Set ℂ} (hUsub : U ⊆ ball (0 : ℂ) 1)
    (hD : D ∈ connectedComponentsIn (U ∩ cluster μ 1 z t)) (hzD : z ∉ D)
    {c : ℂ} {a b : ℝ} (hab : a < b) (hb : 0 < b)
    (hA : annulus c a b ⊆ U) {K : Set ℂ} (hKA : K ⊆ annulus c a b)
    (hK0 : μ K ≠ 0) (hKtop : μ K ≠ ∞) {α : ℝ} (hα : α < 1)
    (hmass : μ (K ∩ D) ≤ ENNReal.ofReal α * μ K) {r : ℝ} (hr : 0 < r) (N : ℕ)
    (hchains : ∀ y ∈ K, ∀ x ∈ K ∩ D, ∃ p : ℕ → ℂ,
      p 0 = y ∧ p N = x ∧
      (∀ i < N, closedBall (p i) r ⊆ annulus c a b) ∧
      (∀ i < N, p (i + 1) ∈ closedBall (p i) (r / 2))) :
    ⨆ x ∈ K ∩ D, odometerExt μ z t x ≤
      ENNReal.ofReal ((4 : ℝ) ^ N) * annulusGreenPotentialSup μ c a b := by
  obtain ⟨y, hyK, hyD⟩ := exists_mem_sdiff_of_relative_mass_lt_one μ hK0 hKtop hα hmass
  exact component_odometer_iSup_le_greenPotentialSup_of_harnack_chains
    hμ hV hz ht hUsub hD hzD hab hb hA (hKA hyK) hyD hKA hr N (hchains y hyK)

/-- If the pole belongs to the target set, it is itself a zero of the
component truncation and can start the chain. -/
theorem component_odometer_iSup_le_greenPotentialSup_of_pole_mem
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {βminus βplus : ℝ} (hV : VolumeGrowth μ 1 βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) {t : ℝ} (ht : 0 < t)
    {U D : Set ℂ} (hUsub : U ⊆ ball (0 : ℂ) 1)
    (hD : D ∈ connectedComponentsIn (U ∩ cluster μ 1 z t)) (hzD : z ∉ D)
    {c : ℂ} {a b : ℝ} (hab : a < b) (hb : 0 < b)
    (hA : annulus c a b ⊆ U) {K : Set ℂ} (hKA : K ⊆ annulus c a b)
    (hzK : z ∈ K) {r : ℝ} (hr : 0 < r) (N : ℕ)
    (hchains : ∀ x ∈ K ∩ D, ∃ p : ℕ → ℂ,
      p 0 = z ∧ p N = x ∧
      (∀ i < N, closedBall (p i) r ⊆ annulus c a b) ∧
      (∀ i < N, p (i + 1) ∈ closedBall (p i) (r / 2))) :
    ⨆ x ∈ K ∩ D, odometerExt μ z t x ≤
      ENNReal.ofReal ((4 : ℝ) ^ N) * annulusGreenPotentialSup μ c a b :=
  component_odometer_iSup_le_greenPotentialSup_of_harnack_chains
    hμ hV hz ht hUsub hD hzD hab hb hA (hKA hzK) hzD hKA hr N hchains

/-- If the mass allowed in a larger set is smaller than the mass of the
nested target, the target contains a point outside the selected component. -/
theorem exists_mem_sdiff_of_outer_mass_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {K A D : Set X} (hKA : K ⊆ A) {m : ℝ≥0∞}
    (hmass : μ (D ∩ A) ≤ m) (hlower : m < μ K) : (K \ D).Nonempty := by
  apply exists_mem_sdiff_of_measure_inter_lt μ
  calc
    μ (K ∩ D) ≤ μ (D ∩ A) := measure_mono (fun x hx => ⟨hx.2, hKA hx.1⟩)
    _ ≤ m := hmass
    _ < μ K := hlower

/-- An outer-annulus mass bound and a lower bound on the middle-annulus mass
provide the zero needed for the component Harnack estimate. -/
theorem component_odometer_iSup_le_greenPotentialSup_of_outer_mass_bound
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {βminus βplus : ℝ} (hV : VolumeGrowth μ 1 βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) {t : ℝ} (ht : 0 < t)
    {U D : Set ℂ} (hUsub : U ⊆ ball (0 : ℂ) 1)
    (hD : D ∈ connectedComponentsIn (U ∩ cluster μ 1 z t)) (hzD : z ∉ D)
    {c : ℂ} {a b : ℝ} (hab : a < b) (hb : 0 < b)
    (hA : annulus c a b ⊆ U) {K T : Set ℂ} (hKA : K ⊆ annulus c a b)
    (hKT : K ⊆ T) {m : ℝ≥0∞} (hmass : μ (D ∩ T) ≤ m) (hlower : m < μ K)
    {r : ℝ} (hr : 0 < r) (N : ℕ)
    (hchains : ∀ y ∈ K, ∀ x ∈ K ∩ D, ∃ p : ℕ → ℂ,
      p 0 = y ∧ p N = x ∧
      (∀ i < N, closedBall (p i) r ⊆ annulus c a b) ∧
      (∀ i < N, p (i + 1) ∈ closedBall (p i) (r / 2))) :
    ⨆ x ∈ K ∩ D, odometerExt μ z t x ≤
      ENNReal.ofReal ((4 : ℝ) ^ N) * annulusGreenPotentialSup μ c a b := by
  obtain ⟨y, hyK, hyD⟩ := exists_mem_sdiff_of_outer_mass_bound μ hKT hmass hlower
  exact component_odometer_iSup_le_greenPotentialSup_of_harnack_chains
    hμ hV hz ht hUsub hD hzD hab hb hA (hKA hyK) hyD hKA hr N (hchains y hyK)

end HarmonicBalls
