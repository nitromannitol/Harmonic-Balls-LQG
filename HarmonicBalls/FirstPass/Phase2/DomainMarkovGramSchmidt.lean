import HarmonicBalls.Steps.Sec11.PairingCovarianceLinearity
import HarmonicBalls.Proofs.Sec8.LaplacianCovarianceEnergy
import HarmonicBalls.Proofs.Sec3.ConservationOfMassStep2

/-!
# Orthogonal outer coordinates of the whole-plane GFF

Gram-Schmidt orthogonalisation of a sequence of test functions `ρ n` for the covariance form
`G(φ, ψ) = wholePlaneGFFCov (.pairing φ) (.pairing ψ)` of the whole-plane GFF:
`ρ' k = ρ k - ∑_{j<k} G(ρ' j, ρ' j)⁻¹ G(ρ k, ρ' j) ρ' j` (the coefficient is `0` when `G(ρ' j, ρ' j) = 0`).
The `ρ' k` are finite linear combinations of the `ρ j`, hence again (mean-zero) test functions on the same set, and
they are pairwise `G`-orthogonal. Since the pairings are almost surely linear, an event of the pairings `(h, ρ n)`
is almost surely equal to an event of the orthogonal pairings `(h, ρ' k)`.

We also record that the deterministic logarithmic shift `-α₀ log |·|` of the field only translates each pairing by
a constant, so events of the pairings `fieldPairing α₀ (hC ω) ψ` are events of the pairings `hC ω ψ`.
-/

namespace HarmonicBalls

open MeasureTheory Set ProbabilityTheory Filter

/-! ### Finite linear combinations of test functions -/

theorem isTestFunction_fun_zero (U : Set ℂ) : IsTestFunction U (fun _ => (0 : ℝ)) :=
  ⟨contDiff_const, HasCompactSupport.zero, by
    rw [show (fun _ : ℂ => (0 : ℝ)) = 0 from rfl, tsupport_zero]; exact empty_subset _⟩

theorem isTestFunction_finset_sum {ι : Type*} {U : Set ℂ} (s : Finset ι) (c : ι → ℝ) {g : ι → ℂ → ℝ}
    (hg : ∀ j ∈ s, IsTestFunction U (g j)) : IsTestFunction U (fun x => ∑ j ∈ s, c j * g j x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isTestFunction_fun_zero U
  | insert i s hi ih =>
    have h := (hg i (Finset.mem_insert_self i s)).const_mul_add_const_mul
      (ih fun j hj => hg j (Finset.mem_insert_of_mem hj)) (c i) 1
    simpa [Finset.sum_insert hi] using h

theorem integral_finset_sum_mul {ι : Type*} {U : Set ℂ} (s : Finset ι) (c : ι → ℝ) {g : ι → ℂ → ℝ}
    (hg : ∀ j ∈ s, IsTestFunction U (g j)) :
    ∫ x, ∑ j ∈ s, c j * g j x = ∑ j ∈ s, c j * ∫ x, g j x := by
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  · intro j hj
    exact ((hg j hj).1.continuous.integrable_of_hasCompactSupport (hg j hj).2.1).const_mul _

/-- The covariance form is linear in finite linear combinations in its first test function. -/
theorem wholePlaneGFFCov_pairing_finset_sum_left {ι : Type*} (s : Finset ι) (c : ι → ℝ) {g : ι → ℂ → ℝ}
    {χ : ℂ → ℝ} (hg : ∀ j ∈ s, IsTestFunction univ (g j)) (hχ : IsTestFunction univ χ) :
    wholePlaneGFFCov (.pairing (fun x => ∑ j ∈ s, c j * g j x)) (.pairing χ) =
      ∑ j ∈ s, c j * wholePlaneGFFCov (.pairing (g j)) (.pairing χ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := wholePlaneGFFCov_pairing_linear_left (isTestFunction_fun_zero univ)
      (isTestFunction_fun_zero univ) hχ 0 0
    simpa using h
  | insert i s hi ih =>
    have hs : ∀ j ∈ s, IsTestFunction univ (g j) := fun j hj => hg j (Finset.mem_insert_of_mem hj)
    have h := wholePlaneGFFCov_pairing_linear_left (hg i (Finset.mem_insert_self i s))
      (isTestFunction_finset_sum s c hs) hχ (c i) 1
    have hfun : (fun x => ∑ j ∈ insert i s, c j * g j x) =
        fun x => c i * g i x + 1 * ∑ j ∈ s, c j * g j x := by
      funext x; rw [Finset.sum_insert hi, one_mul]
    rw [hfun, h, ih hs, Finset.sum_insert hi, one_mul]

/-- Almost sure linearity of the pairings for finite linear combinations. -/
theorem IsWholePlaneGFF.ae_pairing_finset_sum {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc) {ι : Type*}
    (s : Finset ι) (c : ι → ℝ) {g : ι → ℂ → ℝ} (hg : ∀ j ∈ s, IsTestFunction univ (g j)) :
    ∀ᵐ ω ∂P, hC ω (fun x => ∑ j ∈ s, c j * g j x) = ∑ j ∈ s, c j * hC ω (g j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [h.ae_pairing_linear_combination (isTestFunction_fun_zero univ)
      (isTestFunction_fun_zero univ) 0 0] with ω hω
    simpa using hω
  | insert i s hi ih =>
    have hs : ∀ j ∈ s, IsTestFunction univ (g j) := fun j hj => hg j (Finset.mem_insert_of_mem hj)
    have hfun : (fun x => ∑ j ∈ insert i s, c j * g j x) =
        fun x => c i * g i x + 1 * ∑ j ∈ s, c j * g j x := by
      funext x; rw [Finset.sum_insert hi, one_mul]
    filter_upwards [ih hs, h.ae_pairing_linear_combination (hg i (Finset.mem_insert_self i s))
      (isTestFunction_finset_sum s c hs) (c i) 1] with ω h1 h2
    rw [hfun, h2, h1, Finset.sum_insert hi, one_mul]

/-- Nonnegativity of the covariance form on the diagonal. -/
theorem IsWholePlaneGFF.wholePlaneGFFCov_pairing_self_nonneg {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) : 0 ≤ wholePlaneGFFCov (.pairing φ) (.pairing φ) := by
  have h1 := h.covariance_eq (.pairing φ) (.pairing φ) hφ hφ
  simp only [GFFObservable.eval] at h1
  rw [← h1, covariance_self (h.measurable_pairing φ hφ).aemeasurable]
  exact variance_nonneg _ _

/-- Cauchy-Schwarz in the degenerate case: a test function of zero variance is `G`-orthogonal to every
test function. -/
theorem IsWholePlaneGFF.wholePlaneGFFCov_pairing_eq_zero_of_self_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    {φ ψ : ℂ → ℝ} (hφ : IsTestFunction univ φ) (hψ : IsTestFunction univ ψ)
    (h0 : wholePlaneGFFCov (.pairing ψ) (.pairing ψ) = 0) :
    wholePlaneGFFCov (.pairing φ) (.pairing ψ) = 0 := by
  have key : ∀ t : ℝ, 0 ≤ wholePlaneGFFCov (.pairing φ) (.pairing φ) +
      2 * t * wholePlaneGFFCov (.pairing φ) (.pairing ψ) := by
    intro t
    have hθ : IsTestFunction univ (fun x => 1 * φ x + t * ψ x) := hφ.const_mul_add_const_mul hψ 1 t
    have hpos := h.wholePlaneGFFCov_pairing_self_nonneg hθ
    rw [wholePlaneGFFCov_pairing_linear_left hφ hψ hθ, wholePlaneGFFCov_pairing_linear_right hφ hψ hφ,
      wholePlaneGFFCov_pairing_linear_right hφ hψ hψ, h0, h.wholePlaneGFFCov_pairing_comm hψ hφ] at hpos
    linarith
  generalize wholePlaneGFFCov (.pairing φ) (.pairing φ) = A at key
  generalize wholePlaneGFFCov (.pairing φ) (.pairing ψ) = B at key ⊢
  by_contra hb
  have ht : 2 * (-(A + 1) / (2 * B)) * B = -(A + 1) := by field_simp
  have := key (-(A + 1) / (2 * B))
  linarith

/-! ### Gram-Schmidt orthogonalisation -/

/-- Gram-Schmidt orthogonalisation of the test functions `ρ n` for the covariance form of the whole-plane GFF. -/
noncomputable def gramSchmidtTest (ρ : ℕ → ℂ → ℝ) (k : ℕ) : ℂ → ℝ :=
  fun x => ρ k x - ∑ j : Fin k,
    (wholePlaneGFFCov (.pairing (gramSchmidtTest ρ j)) (.pairing (gramSchmidtTest ρ j)))⁻¹ *
      wholePlaneGFFCov (.pairing (ρ k)) (.pairing (gramSchmidtTest ρ j)) * gramSchmidtTest ρ j x
termination_by k
decreasing_by all_goals exact j.isLt

/-- The Gram-Schmidt coefficient of `ρ' j` in `ρ k`. -/
noncomputable def gramSchmidtCoeff (ρ : ℕ → ℂ → ℝ) (k j : ℕ) : ℝ :=
  (wholePlaneGFFCov (.pairing (gramSchmidtTest ρ j)) (.pairing (gramSchmidtTest ρ j)))⁻¹ *
    wholePlaneGFFCov (.pairing (ρ k)) (.pairing (gramSchmidtTest ρ j))

theorem gramSchmidtTest_apply (ρ : ℕ → ℂ → ℝ) (k : ℕ) (x : ℂ) :
    gramSchmidtTest ρ k x = ρ k x - ∑ j : Fin k, gramSchmidtCoeff ρ k j * gramSchmidtTest ρ j x := by
  rw [gramSchmidtTest]; rfl

/-- `ρ k = ρ' k + ∑_{j<k} c_{kj} ρ' j`. -/
theorem eq_gramSchmidtTest_add (ρ : ℕ → ℂ → ℝ) (k : ℕ) :
    ρ k = fun x => 1 * gramSchmidtTest ρ k x +
      1 * ∑ j : Fin k, gramSchmidtCoeff ρ k j * gramSchmidtTest ρ j x := by
  funext x; rw [gramSchmidtTest_apply]; ring

theorem isTestFunction_gramSchmidtTest {U : Set ℂ} {ρ : ℕ → ℂ → ℝ}
    (hρ : ∀ n, IsTestFunction U (ρ n) ∧ ∫ x, ρ n x = 0) (k : ℕ) :
    IsTestFunction U (gramSchmidtTest ρ k) ∧ ∫ x, gramSchmidtTest ρ k x = 0 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have hs : ∀ j ∈ (Finset.univ : Finset (Fin k)), IsTestFunction U (gramSchmidtTest ρ j) :=
      fun j _ => (ih j j.isLt).1
    have hsum := isTestFunction_finset_sum Finset.univ (fun j : Fin k => gramSchmidtCoeff ρ k j) hs
    have hfun : gramSchmidtTest ρ k = fun x => 1 * ρ k x +
        (-1) * ∑ j : Fin k, gramSchmidtCoeff ρ k j * gramSchmidtTest ρ j x := by
      funext x; rw [gramSchmidtTest_apply]; ring
    refine ⟨by rw [hfun]; exact (hρ k).1.const_mul_add_const_mul hsum 1 (-1), ?_⟩
    rw [hfun, integral_add, integral_const_mul, integral_const_mul, integral_finset_sum_mul _ _ hs, (hρ k).2]
    · simp [fun j : Fin k => (ih j j.isLt).2]
    · exact ((hρ k).1.1.continuous.integrable_of_hasCompactSupport (hρ k).1.2.1).const_mul _
    · exact (hsum.1.continuous.integrable_of_hasCompactSupport hsum.2.1).const_mul _

theorem IsWholePlaneGFF.wholePlaneGFFCov_gramSchmidtTest_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    {U : Set ℂ} {ρ : ℕ → ℂ → ℝ} (hρ : ∀ n, IsTestFunction U (ρ n) ∧ ∫ x, ρ n x = 0) :
    ∀ k l, l < k →
      wholePlaneGFFCov (.pairing (gramSchmidtTest ρ k)) (.pairing (gramSchmidtTest ρ l)) = 0 := by
  have hT : ∀ n, IsTestFunction univ (gramSchmidtTest ρ n) :=
    fun n => (isTestFunction_gramSchmidtTest hρ n).1.mono_set (subset_univ U)
  have hρu : ∀ n, IsTestFunction univ (ρ n) := fun n => (hρ n).1.mono_set (subset_univ U)
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro l hl
    have hs : ∀ j ∈ (Finset.univ : Finset (Fin k)), IsTestFunction univ (gramSchmidtTest ρ j) :=
      fun j _ => hT j
    have hsum := isTestFunction_finset_sum Finset.univ (fun j : Fin k => gramSchmidtCoeff ρ k j) hs
    have hfun : gramSchmidtTest ρ k = fun x => 1 * ρ k x +
        (-1) * ∑ j : Fin k, gramSchmidtCoeff ρ k j * gramSchmidtTest ρ j x := by
      funext x; rw [gramSchmidtTest_apply]; ring
    rw [hfun, wholePlaneGFFCov_pairing_linear_left (hρu k) hsum (hT l),
      wholePlaneGFFCov_pairing_finset_sum_left _ _ hs (hT l)]
    have hsingle : ∑ j : Fin k, gramSchmidtCoeff ρ k j *
        wholePlaneGFFCov (.pairing (gramSchmidtTest ρ j)) (.pairing (gramSchmidtTest ρ l)) =
        gramSchmidtCoeff ρ k l *
          wholePlaneGFFCov (.pairing (gramSchmidtTest ρ l)) (.pairing (gramSchmidtTest ρ l)) := by
      rw [Finset.sum_eq_single (⟨l, hl⟩ : Fin k)]
      · intro j _ hj
        have hjl : (j : ℕ) ≠ l := fun e => hj (Fin.ext e)
        rcases lt_or_gt_of_ne hjl with hlt | hlt
        · rw [h.wholePlaneGFFCov_pairing_comm (hT j) (hT l), ih l hl j hlt, mul_zero]
        · rw [ih j j.isLt l hlt, mul_zero]
      · intro hmem; exact absurd (Finset.mem_univ _) hmem
    rw [hsingle, gramSchmidtCoeff]
    by_cases h0 : wholePlaneGFFCov (.pairing (gramSchmidtTest ρ l)) (.pairing (gramSchmidtTest ρ l)) = 0
    · rw [h.wholePlaneGFFCov_pairing_eq_zero_of_self_eq_zero (hρu k) (hT l) h0, h0]; ring
    · have hc : (wholePlaneGFFCov (.pairing (gramSchmidtTest ρ l)) (.pairing (gramSchmidtTest ρ l)))⁻¹ *
          wholePlaneGFFCov (.pairing (ρ k)) (.pairing (gramSchmidtTest ρ l)) *
          wholePlaneGFFCov (.pairing (gramSchmidtTest ρ l)) (.pairing (gramSchmidtTest ρ l)) =
          wholePlaneGFFCov (.pairing (ρ k)) (.pairing (gramSchmidtTest ρ l)) := by field_simp
      rw [hc]; ring

/-- **Orthogonal outer coordinates.** For mean-zero test functions `ρ n` on `U` and a measurable set `S` of
sequences, there are pairwise `G`-orthogonal mean-zero test functions `ρ' k` on `U` (finite linear combinations of
the `ρ n`) and a measurable set `T` such that the event `{((h, ρ n))_n ∈ S}` is almost surely equal to the event
`{((h, ρ' k))_k ∈ T}`. -/
theorem IsWholePlaneGFF.exists_orthogonal_pairing_coordinates {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    {U : Set ℂ} {ρ : ℕ → ℂ → ℝ} (hρ : ∀ n, IsTestFunction U (ρ n) ∧ ∫ x, ρ n x = 0)
    {S : Set (ℕ → ℝ)} (hS : MeasurableSet S) :
    ∃ (ρ' : ℕ → ℂ → ℝ) (T : Set (ℕ → ℝ)), (∀ k, IsTestFunction U (ρ' k) ∧ ∫ x, ρ' k x = 0) ∧
      (∀ k l, k ≠ l → wholePlaneGFFCov (.pairing (ρ' k)) (.pairing (ρ' l)) = 0) ∧ MeasurableSet T ∧
      {ω | (fun n => hC ω (ρ n)) ∈ S} =ᵐ[P] {ω | (fun k => hC ω (ρ' k)) ∈ T} := by
  have hT : ∀ n, IsTestFunction univ (gramSchmidtTest ρ n) :=
    fun n => (isTestFunction_gramSchmidtTest hρ n).1.mono_set (subset_univ U)
  let L : (ℕ → ℝ) → (ℕ → ℝ) := fun y k => y k + ∑ j : Fin k, gramSchmidtCoeff ρ k j * y j
  have hL : Measurable L := by
    refine measurable_pi_iff.mpr fun k => (measurable_pi_apply k).add ?_
    exact Finset.measurable_sum _ fun j _ => (measurable_pi_apply (j : ℕ)).const_mul _
  refine ⟨gramSchmidtTest ρ, L ⁻¹' S, isTestFunction_gramSchmidtTest hρ, ?_, hL hS, ?_⟩
  · intro k l hkl
    rcases lt_or_gt_of_ne hkl with hlt | hlt
    · rw [h.wholePlaneGFFCov_pairing_comm (hT k) (hT l)]
      exact h.wholePlaneGFFCov_gramSchmidtTest_eq_zero hρ l k hlt
    · exact h.wholePlaneGFFCov_gramSchmidtTest_eq_zero hρ k l hlt
  · have hae : ∀ᵐ ω ∂P, ∀ k, hC ω (ρ k) =
        hC ω (gramSchmidtTest ρ k) + ∑ j : Fin k, gramSchmidtCoeff ρ k j * hC ω (gramSchmidtTest ρ j) := by
      rw [ae_all_iff]
      intro k
      have hs : ∀ j ∈ (Finset.univ : Finset (Fin k)), IsTestFunction univ (gramSchmidtTest ρ j) :=
        fun j _ => hT j
      filter_upwards [h.ae_pairing_linear_combination (hT k)
        (isTestFunction_finset_sum Finset.univ (fun j : Fin k => gramSchmidtCoeff ρ k j) hs) 1 1,
        h.ae_pairing_finset_sum Finset.univ (fun j : Fin k => gramSchmidtCoeff ρ k j) hs] with ω h1 h2
      rw [← eq_gramSchmidtTest_add ρ k] at h1
      rw [h1, h2]; ring
    filter_upwards [hae] with ω hω
    have hseq : (fun n => hC ω (ρ n)) = L (fun k => hC ω (gramSchmidtTest ρ k)) := funext hω
    change ((fun n => hC ω (ρ n)) ∈ S) = (L (fun k => hC ω (gramSchmidtTest ρ k)) ∈ S)
    rw [hseq]

/-! ### Removing the logarithmic shift -/

/-- Events of the pairings `(h, ψ n) = (h^ℂ, ψ n) - α₀ ∫ ψ n log |·|` are events of the pairings `(h^ℂ, ψ n)`. -/
theorem exists_setOf_fieldPairing_seq_eq {Ω : Type*} (α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (ψ : ℕ → ℂ → ℝ)
    {S : Set (ℕ → ℝ)} (hS : MeasurableSet S) :
    ∃ S₁ : Set (ℕ → ℝ), MeasurableSet S₁ ∧
      {ω | (fun n => fieldPairing α₀ (hC ω) (ψ n)) ∈ S} = {ω | (fun n => hC ω (ψ n)) ∈ S₁} := by
  let M : (ℕ → ℝ) → (ℕ → ℝ) := fun y n => y n - α₀ * ∫ x, ψ n x * Real.log ‖x‖
  have hM : Measurable M := measurable_pi_iff.mpr fun n => (measurable_pi_apply n).sub_const _
  exact ⟨M ⁻¹' S, hM hS, rfl⟩

end HarmonicBalls
