import HarmonicBalls.FirstPass.S11c.BadSetMeasurable11_7
import HarmonicBalls.FirstPass.S11c.LocalScale11_7

/-!
# First pass, Lemma 11.7: identification of the local bad set (task fp-S11c-11-7-redo-11-10, owner n1; B2 route,
CHATGPT-11-7-B2.md eq. (4.8); referee §2.2)

On the event where the local decoder identity `K x = c • μ|_D` holds with `c ∈ (0,∞)`, and for a root `z ∈ U` such that
the closed balls `B̄_{6·2^{-n}}(z)` lie in `D` for `n ≥ n_D`, the local bad set (4.6) at `(z, x)` is the complement of the
event that the window sums of the global cone-mass events `C_M(μ, 2^{-n}, z)` are eventually at least `a N`.
Only the scales `n ≥ n_D` enter, and for `N ≥ n_D` the whole window `[N+1, 2N]` consists of such scales.
-/

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

namespace HarmonicBalls.S11c

variable {X : Type*} [MeasurableSpace X]

/-- The global window sum of the cone-mass events `C_M(ν, 2^{-n}, z)` over `n ∈ [N+1, 2N]` (B2 window sums, no local
restriction). -/
noncomputable def globalWindowSum (Q : Set ℂ) (M : ℝ) (z : ℂ) (ν : Measure ℂ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc (N + 1) (2 * N),
    ({ν' : Measure ℂ | coneMassEvent ν' Q M ((2 : ℝ)⁻¹ ^ n) z}).indicator (fun _ => (1 : ℝ)) ν

/-- For `N ≥ n_D` and a decoded local measure `c • ν|_D` (with `B̄_{6·2^{-n}}(z) ⊆ D` for `n ≥ n_D`), the local window
sum of `localConeSet` equals the global window sum of `ν`. -/
theorem localWindow_eq_global {K : Kernel X ℂ} {Q : Set ℂ} {M : ℝ} {D : Set ℂ} (hDm : MeasurableSet D)
    {nD : ℕ} {z : ℂ} {x : X} {c : ℝ≥0∞} (hc0 : c ≠ 0) (hcT : c ≠ ⊤) {ν : Measure ℂ}
    (hK : K x = c • ν.restrict D) (hD : ∀ n : ℕ, nD ≤ n → closedBall z (6 * (2 : ℝ)⁻¹ ^ n) ⊆ D)
    {N : ℕ} (hN : nD ≤ N) :
    ∑ n ∈ Finset.Icc (N + 1) (2 * N), (localConeSet K Q M nD n).indicator (fun _ => (1 : ℝ)) (z, x)
      = globalWindowSum Q M z ν N := by
  unfold globalWindowSum
  refine Finset.sum_congr rfl fun n hn => ?_
  have hnD : nD ≤ n := by
    have := (Finset.mem_Icc.mp hn).1
    omega
  have hr : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ n := by positivity
  have hiff : coneMassEvent (K x) Q M ((2 : ℝ)⁻¹ ^ n) z ↔ coneMassEvent ν Q M ((2 : ℝ)⁻¹ ^ n) z := by
    rw [hK]
    exact coneMassEvent_smul_restrict_iff ν hDm hc0 hcT Q M _ hr z (hD n hnD)
  by_cases h : coneMassEvent ν Q M ((2 : ℝ)⁻¹ ^ n) z
  · have hmem : (z, x) ∈ localConeSet K Q M nD n := ⟨hnD, hiff.mpr h⟩
    rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (show ν ∈ {ν' : Measure ℂ |
      coneMassEvent ν' Q M ((2 : ℝ)⁻¹ ^ n) z} from h)]
  · have hmem : (z, x) ∉ localConeSet K Q M nD n := fun hm => h (hiff.mp hm.2)
    rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem (show ν ∉ {ν' : Measure ℂ |
      coneMassEvent ν' Q M ((2 : ℝ)⁻¹ ^ n) z} from h)]

/-- Set-level identification (B2 (4.8), pointwise in the observation): for `z ∈ U`, the pair `(z, x)` lies in the local
bad set (4.6) iff there is no `N₀` with `a N ≤` the global window sum of `ν` for all `N ≥ N₀`. -/
theorem mem_localBadSet_iff {K : Kernel X ℂ} {Q : Set ℂ} {M a : ℝ} {D U : Set ℂ} (hDm : MeasurableSet D)
    {nD : ℕ} {z : ℂ} {x : X} {c : ℝ≥0∞} (hc0 : c ≠ 0) (hcT : c ≠ ⊤) {ν : Measure ℂ}
    (hK : K x = c • ν.restrict D) (hD : ∀ n : ℕ, nD ≤ n → closedBall z (6 * (2 : ℝ)⁻¹ ^ n) ⊆ D) (hzU : z ∈ U) :
    (z, x) ∈ localBadSet K Q M a U nD ↔
      ¬ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → a * (N : ℝ) ≤ globalWindowSum Q M z ν N := by
  constructor
  · rintro ⟨-, hbad⟩ ⟨N0, hN0⟩
    obtain ⟨N, hN, hlt⟩ := hbad (max N0 nD)
    have hnD : nD ≤ N := le_trans (le_max_right _ _) hN
    have hN0N : N0 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
    rw [localWindow_eq_global hDm hc0 hcT hK hD hnD] at hlt
    exact absurd (hN0 N hN0N) (not_le.mpr hlt)
  · intro h
    refine ⟨hzU, fun k => ?_⟩
    by_contra hcon
    simp only [not_exists, not_and, not_lt] at hcon
    refine h ⟨max k nD, fun N hN => ?_⟩
    have hnD : nD ≤ N := le_trans (le_max_right _ _) hN
    have := hcon N hN
    rw [localWindow_eq_global hDm hc0 hcT hK hD hnD] at this
    exact this

/-- A.s. identification (B2 (4.8)): if the decoder identity `K(obs ω) = c • (μ ω)|_D`, `c ∈ (0,∞)`, holds almost surely,
then almost surely, simultaneously for all `z ∈ U`, `(z, obs ω)` lies in the local bad set iff the global window sums
of `μ ω` are not eventually at least `a N`. -/
theorem ae_forall_mem_localBadSet_iff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (obs : Ω → X)
    (μ : Ω → Measure ℂ) (K : Kernel X ℂ) (Q : Set ℂ) (M a : ℝ) {D U : Set ℂ} (hDm : MeasurableSet D) (nD : ℕ)
    (hUD : ∀ z ∈ U, ∀ n : ℕ, nD ≤ n → closedBall z (6 * (2 : ℝ)⁻¹ ^ n) ⊆ D)
    (hdec : ∀ᵐ ω ∂P, ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧ K (obs ω) = c • (μ ω).restrict D) :
    ∀ᵐ ω ∂P, ∀ z ∈ U, ((z, obs ω) ∈ localBadSet K Q M a U nD ↔
      ¬ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → a * (N : ℝ) ≤ globalWindowSum Q M z (μ ω) N) := by
  filter_upwards [hdec] with ω hω
  obtain ⟨c, hc0, hcT, hK⟩ := hω
  intro z hz
  exact mem_localBadSet_iff hDm hc0.ne' hcT.ne hK (hUD z hz) hz

end HarmonicBalls.S11c
