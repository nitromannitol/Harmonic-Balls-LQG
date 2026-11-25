import HarmonicBalls.Proofs.Potential.ReflectedClockOccupation

/-!
# The occupation identity of a clock from every start

Let `A` be a clock of reflected Brownian motion in `K₀` (`IsUnitSquarePCAF A`), unbounded from
every start in `K₀`, with finite Revuz measure `ν`, and `k_s(x, y)` the Neumann heat kernel of the
square. For every start `x ∈ K₀` and every window `(a, T]` with `a > 0`,
`E_x ∫_{(a,T]} g(b_s) dA_s = ∫_a^T ∫ k_s(x, y) g(y) ν(dy) ds`
(`lintegral_clockOccupation_windowWeight_eq`). The proof partitions `(a, T]` at
`a = s_0 < ⋯ < s_N = T`: by the Markov property at `s_j` and the stationarity of Lebesgue measure,
`E_x ∫_{(s_j, s_{j+1}]} g dA = E_m[k_{s_j}(x, b_{s_j}) ∫_{(s_j, s_{j+1}]} g dA]`, where `E_m` is
reflected Brownian motion started from Lebesgue measure on `K₀`; as the mesh tends to `0` the
weights converge along every path to `k_s(x, b_s)` by continuity of the kernel, and dominated
convergence and the mean occupation measure `ds ⊗ ν` under `E_m`
(`lebesgueOccupationMeasure_eq_prod`) give the identity.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology MarkovProcess
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- **Windows after a fixed time.** Almost surely, for every measurable `g`, the occupation
integral over `(c, c + h]` along `b` is the occupation integral over `(0, h]` along `θ_c b`. -/
theorem ae_clockOccupation_windowWeight_shift {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A) {z : ℂ} (hz : z ∈ closedSquare 0 1)
    (hU : ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 z, Tendsto (fun t => A t b) atTop atTop)
    (c : ℝ≥0) (h : ℝ) :
    ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 z, ∀ g : ℂ → ℝ≥0∞, Measurable g →
      clockOccupation A (windowWeight (Ioc (c : ℝ) (c + h)) g) b =
        clockOccupation A (windowWeight (Ioc 0 h) g) (ContinuousPath.shift c b) := by
  filter_upwards [ae_clockOccupation_indicator_Ioi_eq_shift hA hz hU c] with b hb g hg
  have h1 := hb (windowWeight (Ioc (c : ℝ) (c + h)) g)
    (measurable_windowWeight measurableSet_Ioc hg)
  have e1 : (fun p : ℝ × ℂ => (Ioi (c : ℝ)).indicator (fun _ =>
      windowWeight (Ioc (c : ℝ) (c + h)) g p) p.1) = windowWeight (Ioc (c : ℝ) (c + h)) g := by
    funext p
    by_cases hp : p.1 ∈ Ioc (c : ℝ) (c + h)
    · simp [indicator, show p.1 ∈ Ioi (c : ℝ) from hp.1]
    · simp [windowWeight, indicator, hp, mem_prod]
  have e2 : (fun p : ℝ × ℂ => windowWeight (Ioc (c : ℝ) (c + h)) g ((c : ℝ) + p.1, p.2)) =
      windowWeight (Ioc 0 h) g := by
    funext p
    have : (c : ℝ) + p.1 ∈ Ioc (c : ℝ) (c + h) ↔ p.1 ∈ Ioc (0 : ℝ) h := by
      simp only [mem_Ioc]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    by_cases hp : p.1 ∈ Ioc (0 : ℝ) h
    · simp [windowWeight, indicator, mem_prod, hp, this.2 hp]
    · simp [windowWeight, indicator, mem_prod, hp, mt this.1 hp]
  rw [e1, e2] at h1
  exact h1

/-- **The Markov property at a fixed time with the Neumann kernel**:
`E_x Ψ(θ_c b) = ∫_{K₀} E_y Ψ k_c(x, y) dy` for `c > 0`. -/
theorem lintegral_shift_eq_neumannKernel {Ψ : ContinuousPath ℂ → ℝ≥0∞} (hΨ : Measurable Ψ)
    (x : ℂ) {c : ℝ≥0} (hc : c ≠ 0) :
    ∫⁻ b, Ψ (ContinuousPath.shift c b) ∂reflectedPlanarBrownianMotion 0 1 x =
      ∫⁻ y in closedSquare 0 1, (∫⁻ b, Ψ b ∂reflectedPlanarBrownianMotion 0 1 y) *
        squareNeumannKernel c x y := by
  have hφ : Measurable fun y => ∫⁻ b, Ψ b ∂reflectedPlanarBrownianMotion 0 1 y :=
    hΨ.lintegral_kernel
  have h := lintegral_reflected_eval_mul_shift (g := fun _ => 1) measurable_const hΨ c x
  simp only [one_mul] at h
  rw [h, ← lintegral_reflected_eval_eq_neumannKernel hφ x hc, lintegral_reflected_eval_eq c hφ x]
  refine lintegral_congr fun w => ?_
  rw [reflectedPlanarBrownianMotion_zero_one_squareFold]

/-- **One window from every start.** For `x ∈ K₀`, `c > 0` and `h`,
`E_x ∫_{(c, c+h]} g dA = E_m[k_c(x, b_c) ∫_{(c, c+h]} g dA]`. -/
theorem lintegral_clockOccupation_window_eq {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A)
    (hU : ∀ z ∈ closedSquare 0 1, ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 z,
      Tendsto (fun t => A t b) atTop atTop)
    {x : ℂ} (hx : x ∈ closedSquare 0 1) {c : ℝ≥0} (hc : c ≠ 0) (h : ℝ) {g : ℂ → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ b, clockOccupation A (windowWeight (Ioc (c : ℝ) (c + h)) g) b
        ∂reflectedPlanarBrownianMotion 0 1 x =
      ∫⁻ z in closedSquare 0 1, ∫⁻ b, squareNeumannKernel c x (b c) *
        clockOccupation A (windowWeight (Ioc (c : ℝ) (c + h)) g) b
          ∂reflectedPlanarBrownianMotion 0 1 z := by
  have hKm : MeasurableSet (closedSquare 0 1) :=
    (isCompact_closedSquare 0 1).isClosed.measurableSet
  have hΨ : Measurable (clockOccupation A (windowWeight (Ioc 0 h) g)) :=
    measurable_clockOccupation hA.measurable (measurable_windowWeight measurableSet_Ioc hg)
  have hk : Measurable fun y => squareNeumannKernel c x y :=
    (measurable_squareNeumannKernel c).comp (measurable_const.prodMk measurable_id)
  rw [lintegral_congr_ae ((ae_clockOccupation_windowWeight_shift hA hx (hU x hx) c h).mono
    fun b hb => hb g hg), lintegral_shift_eq_neumannKernel hΨ x hc]
  have h2 : ∀ z ∈ closedSquare 0 1, ∫⁻ b, squareNeumannKernel c x (b c) *
      clockOccupation A (windowWeight (Ioc (c : ℝ) (c + h)) g) b
        ∂reflectedPlanarBrownianMotion 0 1 z =
      ∫⁻ b, squareNeumannKernel c x (b c) *
        clockOccupation A (windowWeight (Ioc 0 h) g) (ContinuousPath.shift c b)
          ∂reflectedPlanarBrownianMotion 0 1 z := by
    intro z hz
    refine lintegral_congr_ae ?_
    filter_upwards [ae_clockOccupation_windowWeight_shift hA hz (hU z hz) c h] with b hb
    rw [hb g hg]
  rw [setLIntegral_congr_fun hKm h2, setLIntegral_lintegral_mul_shift_eq hk hΨ c]
  refine setLIntegral_congr_fun hKm fun y _ => ?_
  rw [mul_comm]

/-- Windows of a monotone sequence of times add up. -/
theorem windowWeight_Ioc_eq_sum {f : ℕ → ℝ} (hf : Monotone f) (g : ℂ → ℝ≥0∞) (n : ℕ) :
    windowWeight (Ioc (f 0) (f n)) g =
      ∑ j ∈ Finset.range n, windowWeight (Ioc (f j) (f (j + 1))) g := by
  induction n with
  | zero => funext p; simp [windowWeight, indicator]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    funext p
    simp only [Pi.add_apply, windowWeight, indicator, mem_prod, mem_univ, and_true]
    have hmono : f 0 ≤ f n := hf (Nat.zero_le n)
    have hmono' : f n ≤ f (n + 1) := hf (Nat.le_succ n)
    by_cases h1 : p.1 ∈ Ioc (f 0) (f n)
    · have h2 : p.1 ∉ Ioc (f n) (f (n + 1)) := fun h => absurd h.1 (not_lt.2 h1.2)
      have h3 : p.1 ∈ Ioc (f 0) (f (n + 1)) := ⟨h1.1, h1.2.trans hmono'⟩
      simp [h1, h2, h3]
    · by_cases h2 : p.1 ∈ Ioc (f n) (f (n + 1))
      · have h3 : p.1 ∈ Ioc (f 0) (f (n + 1)) := ⟨lt_of_le_of_lt hmono h2.1, h2.2⟩
        simp [h1, h2, h3]
      · have h3 : p.1 ∉ Ioc (f 0) (f (n + 1)) := by
          rintro ⟨h4, h5⟩
          by_cases h6 : p.1 ≤ f n
          · exact h1 ⟨h4, h6⟩
          · exact h2 ⟨not_le.1 h6, h5⟩
        simp [h1, h2, h3]

theorem windowWeight_apply' (I : Set ℝ) (g : ℂ → ℝ≥0∞) (q : ℝ × ℂ) :
    windowWeight I g q = I.indicator (fun _ => g q.2) q.1 := windowWeight_apply I g q.1 q.2

/-- The partition points `a + j (T - a)/N`. -/
noncomputable def partitionPoint (a T : ℝ) (N j : ℕ) : ℝ := a + j * ((T - a) / N)

theorem monotone_partitionPoint {a T : ℝ} (haT : a ≤ T) (N : ℕ) :
    Monotone (partitionPoint a T N) := by
  intro i j hij
  unfold partitionPoint
  have : 0 ≤ (T - a) / N := div_nonneg (by linarith) (Nat.cast_nonneg N)
  have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
  nlinarith

theorem partitionPoint_succ (a T : ℝ) (N j : ℕ) :
    partitionPoint a T N (j + 1) = partitionPoint a T N j + (T - a) / N := by
  unfold partitionPoint
  push_cast
  ring

/-- **The partition identity.** For `x ∈ K₀`, `0 < a ≤ T` and `N > 0`,
`E_x ∫_{(a,T]} g dA = E_m ∑_j k_{s_j}(x, b_{s_j}) ∫_{(s_j, s_{j+1}]} g dA`. -/
theorem lintegral_clockOccupation_partition {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A)
    (hU : ∀ z ∈ closedSquare 0 1, ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 z,
      Tendsto (fun t => A t b) atTop atTop)
    {x : ℂ} (hx : x ∈ closedSquare 0 1) {a T : ℝ} (ha : 0 < a) (haT : a ≤ T) {N : ℕ}
    (hN : 0 < N) {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ b, clockOccupation A (windowWeight (Ioc a T) g) b ∂reflectedPlanarBrownianMotion 0 1 x =
      ∫⁻ b, ∑ j ∈ Finset.range N,
        squareNeumannKernel (partitionPoint a T N j).toNNReal x (b (partitionPoint a T N j).toNNReal) *
          clockOccupation A (windowWeight (Ioc (partitionPoint a T N j)
            (partitionPoint a T N (j + 1))) g) b ∂unitSquareLebesguePathLaw := by
  have hf := monotone_partitionPoint haT N
  have hf0 : partitionPoint a T N 0 = a := by simp [partitionPoint]
  have hfN : partitionPoint a T N N = T := by
    unfold partitionPoint
    have : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
    ring
  have hpos : ∀ j, 0 < partitionPoint a T N j := fun j =>
    lt_of_lt_of_le ha (hf0.symm.le.trans (hf (Nat.zero_le j)))
  have hW : ∀ j, Measurable (windowWeight (Ioc (partitionPoint a T N j)
      (partitionPoint a T N (j + 1))) g) := fun j => measurable_windowWeight measurableSet_Ioc hg
  have hO : ∀ j, Measurable (clockOccupation A (windowWeight (Ioc (partitionPoint a T N j)
      (partitionPoint a T N (j + 1))) g)) := fun j => measurable_clockOccupation hA.measurable (hW j)
  -- the window is the sum of the cells
  have hsum : ∀ b, clockOccupation A (windowWeight (Ioc a T) g) b =
      ∑ j ∈ Finset.range N, clockOccupation A (windowWeight (Ioc (partitionPoint a T N j)
        (partitionPoint a T N (j + 1))) g) b := by
    intro b
    have hw := windowWeight_Ioc_eq_sum hf g N
    rw [hf0, hfN] at hw
    rw [hw]
    unfold clockOccupation
    simp only [Finset.sum_apply]
    exact lintegral_finsetSum _ fun j _ => (hW j).comp
      (((measurable_clockInverse_timeChange_uncurry hA.measurable)).comp measurable_prodMk_left)
  have hk : ∀ j, Measurable fun b : ContinuousPath ℂ =>
      squareNeumannKernel (partitionPoint a T N j).toNNReal x (b (partitionPoint a T N j).toNNReal) :=
    fun j => (measurable_squareNeumannKernel _).comp (measurable_const.prodMk
      (continuous_eval_const _).measurable)
  simp_rw [hsum]
  rw [lintegral_finsetSum _ fun j _ => hO j, lintegral_finsetSum (Finset.range N)
    (f := fun j b => squareNeumannKernel (partitionPoint a T N j).toNNReal x
      (b (partitionPoint a T N j).toNNReal) * clockOccupation A (windowWeight
        (Ioc (partitionPoint a T N j) (partitionPoint a T N (j + 1))) g) b)
    fun j _ => (hk j).mul (hO j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hc : (partitionPoint a T N j).toNNReal ≠ 0 := (Real.toNNReal_pos.2 (hpos j)).ne'
  have hcoe : ((partitionPoint a T N j).toNNReal : ℝ) = partitionPoint a T N j :=
    Real.coe_toNNReal _ (hpos j).le
  have h := lintegral_clockOccupation_window_eq hA hU hx hc ((T - a) / N) hg
  rw [hcoe, ← partitionPoint_succ] at h
  rw [h]
  exact (lintegral_unitSquareLebesguePathLaw (F := fun b => squareNeumannKernel
    (partitionPoint a T N j).toNNReal x (b (partitionPoint a T N j).toNNReal) * clockOccupation A
      (windowWeight (Ioc (partitionPoint a T N j) (partitionPoint a T N (j + 1))) g) b)
    ((hk j).mul (hO j)).aemeasurable).symm

/-- Reflected paths stay in `K₀` under the Lebesgue-started law. -/
theorem ae_forall_mem_closedSquare_unitSquareLebesguePathLaw :
    ∀ᵐ b ∂unitSquareLebesguePathLaw, ∀ t, b t ∈ closedSquare 0 1 := by
  have hclosed : IsClosed {b : ContinuousPath ℂ | ∀ t, b t ∈ closedSquare 0 1} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun t =>
      (isCompact_closedSquare 0 1).isClosed.preimage (continuous_eval_const t)
  rw [ae_iff, show {a : ContinuousPath ℂ | ¬∀ t, a t ∈ closedSquare 0 1} =
    {b : ContinuousPath ℂ | ∀ t, b t ∈ closedSquare 0 1}ᶜ from rfl,
    unitSquareLebesguePathLaw_apply hclosed.measurableSet.compl]
  refine (setLIntegral_congr_fun (isCompact_closedSquare 0 1).isClosed.measurableSet
    (g := fun _ => 0) fun z _ => ?_).trans (by simp)
  exact ae_iff.1 (OptionalTime.ae_forall_mem_closedSquare_reflected z)

/-- **The occupation identity from every start** on a window `(a, T]` with `a > 0`:
`E_x ∫_{(a,T]} 1_B(b_s) dA_s = ∫∫ k_s(x, y) 1_{(a,T]}(s) 1_B(y) ds ν(dy)`. -/
theorem lintegral_clockOccupation_windowWeight_eq {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A)
    (hU : ∀ z ∈ closedSquare 0 1, ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 z,
      Tendsto (fun t => A t b) atTop atTop) [IsFiniteMeasure (unitSquareRevuzMeasure A)]
    {x : ℂ} (hx : x ∈ closedSquare 0 1) {a T : ℝ} (ha : 0 < a) (haT : a < T) {B : Set ℂ}
    (hB : MeasurableSet B) :
    ∫⁻ b, clockOccupation A (windowWeight (Ioc a T) (B.indicator 1)) b
        ∂reflectedPlanarBrownianMotion 0 1 x =
      ∫⁻ q, squareNeumannKernel q.1.toNNReal x q.2 * windowWeight (Ioc a T) (B.indicator 1) q
        ∂((volume.restrict (Ioi (0 : ℝ))).prod (unitSquareRevuzMeasure A)) := by
  set g : ℂ → ℝ≥0∞ := B.indicator 1 with hg_def
  have hg : Measurable g := measurable_one.indicator hB
  set P := unitSquareLebesguePathLaw with hP
  set μ := P.prod (volume.restrict (Ioi (0 : ℝ))) with hμ
  set φ : ContinuousPath ℂ × ℝ → ℝ × ℂ := fun p =>
    ((pcafClockInverse (clockRationalRegularization A) p.2.toNNReal p.1 : ℝ),
      unitSquareTimeChangeRegularized A p.2.toNNReal p.1) with hφ_def
  have hφ : Measurable φ := measurable_clockInverse_timeChange_uncurry hA.measurable
  have hWm : Measurable (windowWeight (Ioc a T) g) := measurable_windowWeight measurableSet_Ioc hg
  set G : ℝ × ℂ → ℝ≥0∞ := fun q => squareNeumannKernel q.1.toNNReal x q.2 *
    windowWeight (Ioc a T) g q with hG_def
  have hGm : Measurable G :=
    (measurable_squareNeumannKernel_uncurry.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk
      (measurable_const.prodMk measurable_snd))).mul hWm
  -- integrals against `μ` are mean occupation integrals
  have hμint : ∀ H : ℝ × ℂ → ℝ≥0∞, Measurable H →
      ∫⁻ p, H (φ p) ∂μ = ∫⁻ q, H q ∂((volume.restrict (Ioi (0 : ℝ))).prod
        (unitSquareRevuzMeasure A)) := by
    intro H hH
    rw [hμ, lintegral_prod (fun p => H (φ p)) (hH.comp hφ).aemeasurable]
    have h1 : (fun b => ∫⁻ u, H (φ (b, u)) ∂volume.restrict (Ioi (0 : ℝ))) =
        clockOccupation A H := rfl
    rw [h1, hP, lintegral_unitSquareLebesguePathLaw (measurable_clockOccupation hA.measurable
      hH).aemeasurable, ← lintegral_lebesgueOccupationMeasure hA.measurable hH,
      lebesgueOccupationMeasure_eq_prod hA hU]
  -- the approximating integrands
  set s : ℕ → ℕ → ℝ := fun n j => partitionPoint a T (n + 1) j with hs_def
  set F : ℕ → ContinuousPath ℂ × ℝ → ℝ≥0∞ := fun n p => ∑ j ∈ Finset.range (n + 1),
    squareNeumannKernel (s n j).toNNReal x (p.1 (s n j).toNNReal) *
      windowWeight (Ioc (s n j) (s n (j + 1))) g (φ p) with hF_def
  have hFm : ∀ n, Measurable (F n) := by
    intro n
    refine Finset.measurable_sum _ fun j _ => ?_
    exact ((measurable_squareNeumannKernel _).comp (measurable_const.prodMk
      ((continuous_eval_const _).measurable.comp measurable_fst))).mul
      ((measurable_windowWeight measurableSet_Ioc hg).comp hφ)
  have hpart : ∀ n, ∫⁻ b, clockOccupation A (windowWeight (Ioc a T) g) b
      ∂reflectedPlanarBrownianMotion 0 1 x = ∫⁻ p, F n p ∂μ := by
    intro n
    rw [lintegral_clockOccupation_partition hA hU hx ha haT.le (Nat.succ_pos n) hg, hμ,
      lintegral_prod _ (hFm n).aemeasurable]
    refine lintegral_congr fun b => ?_
    symm
    rw [hF_def]
    simp only
    rw [lintegral_finsetSum (f := fun j u => squareNeumannKernel (s n j).toNNReal x
      (b (s n j).toNNReal) * windowWeight (Ioc (s n j) (s n (j + 1))) g (φ (b, u))) _
      fun j _ => (((measurable_windowWeight measurableSet_Ioc hg).comp hφ).comp
        measurable_prodMk_left).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [lintegral_const_mul (f := fun u => windowWeight (Ioc (s n j) (s n (j + 1))) g (φ (b, u))) _
      (((measurable_windowWeight measurableSet_Ioc hg).comp hφ).comp measurable_prodMk_left)]
    rfl
  -- endpoints and cells
  have hf := fun n => monotone_partitionPoint haT.le (n + 1)
  have hs0 : ∀ n, s n 0 = a := fun n => by simp [hs_def, partitionPoint]
  have hsN : ∀ n, s n (n + 1) = T := by
    intro n
    simp only [hs_def, partitionPoint]
    have : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  have hsmem : ∀ n j, j ≤ n + 1 → a ≤ s n j ∧ s n j ≤ T := by
    intro n j hj
    exact ⟨(hs0 n) ▸ hf n (Nat.zero_le j), (hsN n) ▸ hf n hj⟩
  have hsum1 : ∀ n (g' : ℂ → ℝ≥0∞) q, windowWeight (Ioc a T) g' q =
      ∑ j ∈ Finset.range (n + 1), windowWeight (Ioc (s n j) (s n (j + 1))) g' q := by
    intro n g' q
    have h := congrFun (windowWeight_Ioc_eq_sum (hf n) g' (n + 1)) q
    rw [Finset.sum_apply] at h
    rw [← hs0 n, ← hsN n]
    exact h
  obtain ⟨C, hC, hCle⟩ := exists_squareNeumannKernel_le ha haT.le
  have hgood := Measure.QuasiMeasurePreserving.ae (Measure.quasiMeasurePreserving_fst (μ := P)
    (ν := volume.restrict (Ioi (0 : ℝ)))) ae_forall_mem_closedSquare_unitSquareLebesguePathLaw
  -- the bound
  have hbound : ∀ n, ∀ᵐ p ∂μ, F n p ≤ C * windowWeight (Ioc a T) g (φ p) := by
    intro n
    filter_upwards [hgood] with p hp
    rw [hsum1 n g, Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => mul_le_mul' ?_ le_rfl
    have hj' := hsmem n j (Finset.mem_range.1 hj).le
    refine hCle _ ?_ ?_ x hx _ (hp _)
    · rw [Real.coe_toNNReal _ (ha.le.trans hj'.1)]
      exact hj'.1
    · rw [Real.coe_toNNReal _ (ha.le.trans hj'.1)]
      exact hj'.2
  have hfin : ∫⁻ p, C * windowWeight (Ioc a T) g (φ p) ∂μ ≠ ⊤ := by
    rw [lintegral_const_mul (f := fun p => windowWeight (Ioc a T) g (φ p)) C (hWm.comp hφ),
      hμint _ hWm]
    refine ENNReal.mul_ne_top hC (ne_top_of_le_ne_top (b := ((volume.restrict (Ioi (0 : ℝ))).prod
      (unitSquareRevuzMeasure A)) (Ioc a T ×ˢ univ)) ?_ ?_)
    · rw [Measure.prod_prod]
      exact ENNReal.mul_ne_top (by
        rw [Measure.restrict_apply measurableSet_Ioc]
        exact (measure_mono inter_subset_left).trans_lt measure_Ioc_lt_top |>.ne)
        (measure_ne_top _ _)
    · rw [← lintegral_indicator_one (measurableSet_Ioc.prod MeasurableSet.univ)]
      refine lintegral_mono fun q => ?_
      by_cases hq : q.1 ∈ Ioc a T
      · simp only [windowWeight, indicator, mem_prod, hq, mem_univ, and_self, ite_true, hg_def]
        by_cases hq2 : q.2 ∈ B <;> simp [hq2]
      · simp [windowWeight, indicator, mem_prod, hq]
  -- the limit
  have hlim : ∀ᵐ p ∂μ, Tendsto (fun n => F n p) atTop (𝓝 (G (φ p))) := by
    filter_upwards [hgood] with p hp
    set σ := (φ p).1 with hσ_def
    by_cases hσ : σ ∈ Ioc a T
    · have hσ0 : 0 < σ := ha.trans hσ.1
      -- the cell of `σ`
      have hcell : ∀ n, ∃ j ∈ Finset.range (n + 1), σ ∈ Ioc (s n j) (s n (j + 1)) := by
        intro n
        have h2 := hsum1 n (fun _ => (1 : ℝ≥0∞)) (σ, (φ p).2)
        have h1 : windowWeight (Ioc a T) (fun _ => (1 : ℝ≥0∞)) (σ, (φ p).2) = 1 := by
          rw [windowWeight_apply, indicator_of_mem hσ]
        rw [h1] at h2
        obtain ⟨j, hj, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h2 ▸ one_ne_zero)
        refine ⟨j, hj, ?_⟩
        by_contra hnot
        exact hne (by rw [windowWeight_apply, indicator_of_notMem hnot])
      choose j hj hjσ using hcell
      -- disjointness of the cells
      have hdisj : ∀ n j', j' ≠ j n → σ ∉ Ioc (s n j') (s n (j' + 1)) := by
        intro n j' hne hmem
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · have := hf n (show j' + 1 ≤ j n from hlt)
          exact absurd (hmem.2.trans this) (not_le.2 (hjσ n).1)
        · have := hf n (show j n + 1 ≤ j' from hlt)
          exact absurd ((hjσ n).2.trans this) (not_le.2 hmem.1)
      have hFn : ∀ n, F n p = squareNeumannKernel (s n (j n)).toNNReal x
          (p.1 (s n (j n)).toNNReal) * g (φ p).2 := by
        intro n
        rw [hF_def]
        simp only
        rw [Finset.sum_eq_single (j n)]
        · rw [windowWeight_apply', ← hσ_def, indicator_of_mem (hjσ n)]
        · intro j' _ hne
          rw [windowWeight_apply', ← hσ_def, indicator_of_notMem (hdisj n j' hne), mul_zero]
        · intro hnot
          exact absurd (hj n) hnot
      -- the left endpoints converge to `σ`
      have hconv : Tendsto (fun n => (s n (j n)).toNNReal) atTop (𝓝 σ.toNNReal) := by
        have hd : ∀ n, dist (s n (j n)).toNNReal σ.toNNReal ≤ (T - a) / ((n : ℝ) + 1) := by
          intro n
          have h1 := (hjσ n).1
          have h2 := (hjσ n).2
          simp only [hs_def] at h1 h2
          rw [partitionPoint_succ] at h2
          have hsn : 0 ≤ s n (j n) := ha.le.trans (hsmem n (j n)
            (Finset.mem_range.1 (hj n)).le).1
          simp only [hs_def] at hsn
          rw [NNReal.dist_eq, Real.coe_toNNReal _ hsn, Real.coe_toNNReal _ hσ0.le, abs_sub_comm,
            abs_of_nonneg (by linarith)]
          push_cast at h2
          linarith
        refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun n => dist_nonneg) hd ?_)
        have h0 := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (T - a)
        simpa [div_eq_mul_inv] using h0
      have hσ' : 0 < σ.toNNReal := Real.toNNReal_pos.2 hσ0
      have hpath : Tendsto (fun n => ((s n (j n)).toNNReal, p.1 (s n (j n)).toNNReal)) atTop
          (𝓝 (σ.toNNReal, p.1 σ.toNNReal)) :=
        hconv.prodMk_nhds ((p.1.continuous.tendsto _).comp hconv)
      have hk : Tendsto (fun n => squareNeumannKernel (s n (j n)).toNNReal x
          (p.1 (s n (j n)).toNNReal)) atTop
          (𝓝 (squareNeumannKernel σ.toNNReal x (p.1 σ.toNNReal))) :=
        (continuousAt_squareNeumannKernel hx hσ' (hp _)).tendsto.comp hpath
      have hY : (φ p).2 = p.1 σ.toNNReal := by
        simp only [hφ_def, hσ_def, unitSquareTimeChangeRegularized, Real.toNNReal_coe]
      have hGv : G (φ p) = squareNeumannKernel σ.toNNReal x (p.1 σ.toNNReal) * g (φ p).2 := by
        simp only [hG_def]
        rw [windowWeight_apply', ← hσ_def, indicator_of_mem hσ, ← hY, hσ_def]
      rw [hGv]
      simp_rw [hFn]
      by_cases hgy : (φ p).2 ∈ B
      · simpa [hg_def, hgy] using hk
      · simp [hg_def, hgy]
    · have hzero : ∀ n, F n p = 0 := by
        intro n
        refine Finset.sum_eq_zero fun j hj => ?_
        have hj' := hsmem n j (Finset.mem_range.1 hj).le
        have hj'' := hsmem n (j + 1) (Finset.mem_range.1 hj)
        have hnot : σ ∉ Ioc (s n j) (s n (j + 1)) := fun hm =>
          hσ ⟨lt_of_le_of_lt hj'.1 hm.1, hm.2.trans hj''.2⟩
        rw [windowWeight_apply', ← hσ_def, indicator_of_notMem hnot, mul_zero]
      have hG0 : G (φ p) = 0 := by
        simp only [hG_def]
        rw [windowWeight_apply', ← hσ_def, indicator_of_notMem hσ, mul_zero]
      simp only [hzero, hG0]
      exact tendsto_const_nhds
  have htend := tendsto_lintegral_of_dominated_convergence _ hFm hbound hfin hlim
  have hconst : Tendsto (fun n => ∫⁻ p, F n p ∂μ) atTop
      (𝓝 (∫⁻ b, clockOccupation A (windowWeight (Ioc a T) g) b
        ∂reflectedPlanarBrownianMotion 0 1 x)) := by
    simp_rw [← hpart]
    exact tendsto_const_nhds
  rw [tendsto_nhds_unique hconst htend, hμint _ hGm]

/-- **The occupation measure of the time change from every start** is `k_s(x, y) ds ν(dy)`
(`ν` the Revuz measure, carried by `K₀`): for `x ∈ K₀`, the mean over paths from `x` of the
occupation measures `pathOccupationMeasure A b` (in the variables `(s, b_s)`, `s` the time of the
underlying motion) is `(Leb|(0,∞) ⊗ ν).withDensity k_s(x, ·)`. -/
theorem bind_pathOccupationMeasure_eq {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A)
    (hU : ∀ z ∈ closedSquare 0 1, ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 z,
      Tendsto (fun t => A t b) atTop atTop) [IsFiniteMeasure (unitSquareRevuzMeasure A)]
    (hνK : unitSquareRevuzMeasure A (closedSquare 0 1)ᶜ = 0)
    {x : ℂ} (hx : x ∈ closedSquare 0 1) :
    (reflectedPlanarBrownianMotion 0 1 x).bind (pathOccupationMeasure A) =
      ((volume.restrict (Ioi (0 : ℝ))).prod (unitSquareRevuzMeasure A)).withDensity
        fun q => squareNeumannKernel q.1.toNNReal x q.2 := by
  set M := (reflectedPlanarBrownianMotion 0 1 x).bind (pathOccupationMeasure A) with hM
  set N := ((volume.restrict (Ioi (0 : ℝ))).prod (unitSquareRevuzMeasure A)).withDensity
    (fun q : ℝ × ℂ => squareNeumannKernel q.1.toNNReal x q.2) with hN
  have hMapp : ∀ S, MeasurableSet S → M S = ∫⁻ b, clockOccupation A (S.indicator 1) b
      ∂reflectedPlanarBrownianMotion 0 1 x := by
    intro S hS
    rw [hM, Measure.bind_apply hS (measurable_pathOccupationMeasure hA.measurable).aemeasurable]
    refine lintegral_congr fun b => ?_
    rw [← lintegral_indicator_one hS, lintegral_pathOccupationMeasure hA.measurable
      (measurable_one.indicator hS)]
  -- rectangles with time window away from `0`
  have hrect : ∀ a T : ℝ, 0 < a → a < T → ∀ B : Set ℂ, MeasurableSet B →
      M (Ioc a T ×ˢ B) = N (Ioc a T ×ˢ B) := by
    intro a T ha haT B hB
    rw [hMapp _ (measurableSet_Ioc.prod hB), indicator_prod_eq_windowWeight,
      lintegral_clockOccupation_windowWeight_eq hA hU hx ha haT hB, hN,
      withDensity_apply _ (measurableSet_Ioc.prod hB), ← lintegral_indicator
        (measurableSet_Ioc.prod hB)]
    refine lintegral_congr fun q => ?_
    rw [windowWeight_apply']
    by_cases h1 : q.1 ∈ Ioc a T <;> by_cases h2 : q.2 ∈ B <;>
      simp [indicator, mem_prod, h1, h2]
  -- no mass at nonpositive times
  have hMneg : M (Iic 0 ×ˢ univ) = 0 := by
    rw [hMapp _ (measurableSet_Iic.prod MeasurableSet.univ)]
    refine (lintegral_congr_ae (g := fun _ => 0) ?_).trans (by simp)
    filter_upwards [hA.path x hx, hU x hx] with b hp hu
    unfold clockOccupation
    refine (setLIntegral_congr_fun measurableSet_Ioi (g := fun _ => 0) fun u hu0 => ?_).trans
      (by simp)
    have hreg : ∀ s, clockRationalRegularization A s b = A s b := fun s =>
      clockRationalRegularization_eq_of_continuous_monotone hp.2.1 hp.2.2 s
    have hpos : 0 < (pcafClockInverse (clockRationalRegularization A) u.toNNReal b : ℝ) := by
      by_contra hle
      have hle' : pcafClockInverse (clockRationalRegularization A) u.toNNReal b ≤ 0 := by
        rw [← NNReal.coe_le_coe]
        exact not_lt.1 hle
      unfold pcafClockInverse at hle'
      simp only [hreg] at hle'
      have h : u.toNNReal ≤ A 0 b := le_clock_of_sInf_le (a := fun s => A s b) hp.1 hp.2.1
        hp.2.2 (hu.eventually_gt_atTop _).exists hle'
      rw [hp.1] at h
      exact absurd (Real.toNNReal_pos.2 (hu0 : (0 : ℝ) < u)) (not_lt.2 h)
    exact indicator_of_notMem (fun h => (not_le.2 hpos) h.1) _
  have hNneg : N (Iic 0 ×ˢ univ) = 0 := by
    rw [hN, withDensity_apply _ (measurableSet_Iic.prod MeasurableSet.univ)]
    refine setLIntegral_measure_zero _ _ ?_
    rw [Measure.prod_prod, Measure.restrict_apply measurableSet_Iic, Iic_inter_Ioi, Ioc_self,
      measure_empty, zero_mul]
  -- windows starting at `0`
  have h0 : ∀ T : ℝ, 0 < T → ∀ B : Set ℂ, MeasurableSet B →
      M (Ioc 0 T ×ˢ B) = N (Ioc 0 T ×ˢ B) := by
    intro T hT B hB
    have hmono : Monotone fun n : ℕ => Ioc (T / (n + 2)) T ×ˢ B := by
      intro m n hmn
      have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
      refine prod_mono (Ioc_subset_Ioc_left (div_le_div_of_nonneg_left hT.le
        (by positivity) (by linarith))) subset_rfl
    have hU' : ⋃ n : ℕ, Ioc (T / (n + 2)) T ×ˢ B = Ioc 0 T ×ˢ B := by
      ext q
      simp only [mem_iUnion, mem_prod, mem_Ioc]
      constructor
      · rintro ⟨n, ⟨h1, h2⟩, h3⟩
        exact ⟨⟨lt_trans (div_pos hT (by positivity)) h1, h2⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        obtain ⟨n, hn⟩ := exists_nat_gt (T / q.1)
        have hn' : T < n * q.1 := (div_lt_iff₀ h1).1 hn
        refine ⟨n, ⟨?_, h2⟩, h3⟩
        rw [div_lt_iff₀ (by positivity)]
        nlinarith
    rw [← hU', hmono.measure_iUnion, hmono.measure_iUnion]
    refine iSup_congr fun n => hrect _ _ (div_pos hT (by positivity)) (div_lt_self hT ?_) B hB
    have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    linarith
  -- all time windows
  have hrect' : ∀ a T : ℝ, ∀ B : Set ℂ, MeasurableSet B →
      M (Ioc a T ×ˢ B) = N (Ioc a T ×ˢ B) := by
    intro a T B hB
    have hred : ∀ μ' : Measure (ℝ × ℂ), μ' (Iic 0 ×ˢ univ) = 0 →
        μ' (Ioc a T ×ˢ B) = μ' (Ioc (max a 0) T ×ˢ B) := by
      intro μ' hz
      have hsub : Ioc a T ×ˢ B ⊆ Ioc (max a 0) T ×ˢ B ∪ Iic 0 ×ˢ univ := by
        intro q hq
        by_cases hq0 : q.1 ≤ 0
        · exact Or.inr ⟨hq0, mem_univ _⟩
        · exact Or.inl ⟨⟨max_lt hq.1.1 (not_le.1 hq0), hq.1.2⟩, hq.2⟩
      refine le_antisymm ((measure_mono hsub).trans ((measure_union_le _ _).trans
        (le_of_eq (by rw [hz, add_zero])))) (measure_mono (prod_mono (Ioc_subset_Ioc_left
          (le_max_left _ _)) subset_rfl))
    rw [hred M hMneg, hred N hNneg]
    rcases le_or_gt T (max a 0) with hT | hT
    · rw [Ioc_eq_empty (not_lt.2 hT), empty_prod, measure_empty, measure_empty]
    · rcases le_or_gt a 0 with ha | ha
      · rw [max_eq_right ha] at hT ⊢
        exact h0 T hT B hB
      · rw [max_eq_left ha.le] at hT ⊢
        exact hrect a T ha hT B hB
  -- finiteness on time windows away from `0`
  have hfin : ∀ a T : ℝ, 0 < a → a < T → M (Ioc a T ×ˢ univ) ≠ ⊤ := by
    intro a T ha haT
    rw [hrect a T ha haT univ MeasurableSet.univ, hN, withDensity_apply _
      (measurableSet_Ioc.prod MeasurableSet.univ)]
    obtain ⟨C, hC, hCle⟩ := exists_squareNeumannKernel_le ha haT.le
    have hK : ∀ᵐ q ∂(volume.restrict (Ioi (0 : ℝ))).prod (unitSquareRevuzMeasure A),
        q.2 ∈ closedSquare 0 1 := by
      rw [ae_iff, show {q : ℝ × ℂ | ¬q.2 ∈ closedSquare 0 1} = univ ×ˢ (closedSquare 0 1)ᶜ by
        ext q; simp, Measure.prod_prod, hνK, mul_zero]
    have hle : ∀ᵐ q ∂((volume.restrict (Ioi (0 : ℝ))).prod (unitSquareRevuzMeasure A)).restrict
        (Ioc a T ×ˢ univ), squareNeumannKernel q.1.toNNReal x q.2 ≤ C := by
      refine (ae_restrict_iff' (measurableSet_Ioc.prod MeasurableSet.univ)).2
        (hK.mono fun q hq hqS => ?_)
      have h1 : ((q.1.toNNReal : ℝ≥0) : ℝ) = q.1 := Real.coe_toNNReal _ (ha.trans hqS.1.1).le
      exact hCle _ (by rw [h1]; exact hqS.1.1.le) (by rw [h1]; exact hqS.1.2) x hx _ hq
    refine ne_top_of_le_ne_top ?_ (lintegral_mono_ae hle)
    rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, Measure.prod_prod,
      Measure.restrict_apply measurableSet_Ioc]
    exact ENNReal.mul_ne_top hC (ENNReal.mul_ne_top
      ((measure_mono inter_subset_left).trans_lt measure_Ioc_lt_top).ne (measure_ne_top _ _))
  -- the generating π-system of rectangles
  have hC : IsCountablySpanning {I : Set ℝ | ∃ l u, l < u ∧ Ioc l u = I} := by
    refine ⟨fun n : ℕ => Ioc (-((n : ℝ) + 1)) (n + 1), fun n => ⟨_, _, ?_, rfl⟩, ?_⟩
    · have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      linarith
    · refine eq_univ_of_forall fun r => mem_iUnion.2 ?_
      obtain ⟨n, hn⟩ := exists_nat_gt |r|
      exact ⟨n, ⟨by linarith [neg_abs_le r], by linarith [le_abs_self r]⟩⟩
  have hgen : (inferInstance : MeasurableSpace (ℝ × ℂ)) = MeasurableSpace.generateFrom
      (image2 (· ×ˢ ·) {I : Set ℝ | ∃ l u, l < u ∧ Ioc l u = I} {B : Set ℂ | MeasurableSet B}) := by
    have h1 : (inferInstance : MeasurableSpace ℝ) =
        MeasurableSpace.generateFrom {I : Set ℝ | ∃ l u, l < u ∧ Ioc l u = I} := by
      rw [← borel_eq_generateFrom_Ioc ℝ]
      exact BorelSpace.measurable_eq
    have h2 : (inferInstance : MeasurableSpace ℂ) =
        MeasurableSpace.generateFrom {B : Set ℂ | MeasurableSet B} :=
      MeasurableSpace.generateFrom_measurableSet.symm
    rw [← generateFrom_prod_eq hC isCountablySpanning_measurableSet, ← h1, ← h2]
  refine Measure.ext_of_generateFrom_of_cover_subset hgen
    ((isPiSystem_Ioc (id : ℝ → ℝ) id).prod MeasurableSpace.isPiSystem_measurableSet)
    (T := range (fun n : ℕ => Ioc (-((n : ℝ) + 1)) 0 ×ˢ (univ : Set ℂ)) ∪
      range (fun n : ℕ => Ioc (1 / ((n : ℝ) + 2)) (n + 1) ×ˢ (univ : Set ℂ))) ?_ ?_ ?_ ?_ ?_
  · rintro _ (⟨n, rfl⟩ | ⟨n, rfl⟩)
    · refine mem_image2_of_mem ⟨_, _, ?_, rfl⟩ (MeasurableSet.univ : MeasurableSet (univ : Set ℂ))
      have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      linarith
    · refine mem_image2_of_mem ⟨_, _, ?_, rfl⟩ (MeasurableSet.univ : MeasurableSet (univ : Set ℂ))
      have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      have : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
      linarith
  · exact (countable_range _).union (countable_range _)
  · rw [sUnion_union, sUnion_range, sUnion_range]
    refine eq_univ_of_forall fun q => ?_
    by_cases hq : q.1 ≤ 0
    · obtain ⟨n, hn⟩ := exists_nat_gt (-q.1)
      exact Or.inl (mem_iUnion.2 ⟨n, ⟨by linarith, hq⟩, mem_univ _⟩)
    · have hq' : 0 < q.1 := not_le.1 hq
      obtain ⟨n, hn⟩ := exists_nat_gt (max (1 / q.1) q.1)
      have hn1 : 1 / q.1 < n := lt_of_le_of_lt (le_max_left _ _) hn
      have hn2 : q.1 < n := lt_of_le_of_lt (le_max_right _ _) hn
      refine Or.inr (mem_iUnion.2 ⟨n, ⟨?_, by linarith⟩, mem_univ _⟩)
      have h3 : 1 < n * q.1 := by
        rw [div_lt_iff₀ hq'] at hn1
        exact hn1
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
  · rintro _ (⟨n, rfl⟩ | ⟨n, rfl⟩)
    · refine ne_top_of_le_ne_top (b := M (Iic 0 ×ˢ univ)) (by rw [hMneg]; exact ENNReal.zero_ne_top)
        (measure_mono (prod_mono Ioc_subset_Iic_self subset_rfl))
    · refine hfin _ _ (by positivity) ?_
      have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      have : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
      linarith
  · rintro _ ⟨I, ⟨l, u, -, rfl⟩, B, hB, rfl⟩
    exact hrect' l u B hB

end HarmonicBalls
