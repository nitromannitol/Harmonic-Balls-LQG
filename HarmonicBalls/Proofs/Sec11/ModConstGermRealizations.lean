import HarmonicBalls.Proofs.Sec11.ModConstPairingRealizations

/-! # The origin germ across field realizations

The Section 8 zero-one law uses Leonardo Bonanno's LatticeProb formalization.
Only absolute continuity of the full local joint zero-integral pairing laws
is assumed; the source and reference fields may live on different spaces.
-/

namespace HarmonicBalls

open Set Metric Filter MeasureTheory

/-- Local joint pairing-law domination transfers origin germ triviality
between different realizations. -/
theorem origin_modConst_germ_trivial_of_trivial_reference
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) (Q : Measure Ξ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hD : Ξ → (ℂ → ℝ) → ℝ}
    (α : ℝ) {r : ℝ} (hr : 0 < r)
    (hP : Measurable (localModConstPairings α hC (ball 0 r)))
    (hQmap : Measurable (localModConstPairings α hD (ball 0 r)))
    (hQtrivial : ∀ A : Set Ξ, (∀ ε : ℝ, 0 < ε →
      MeasurableSet[Section6.fieldSigmaAlgebraModConst α hD (ball 0 ε)] A) →
      Q A = 0 ∨ Q A = 1)
    (hAC : P.map (localModConstPairings α hC (ball 0 r)) ≪
      Q.map (localModConstPairings α hD (ball 0 r))) :
    ∀ A : Set Ω, (∀ ε : ℝ, 0 < ε →
      MeasurableSet[Section6.fieldSigmaAlgebraModConst α hC (ball 0 ε)] A) →
      P A = 0 ∨ P A = 1 := by
  classical
  let s : ℕ → ℝ := fun n => min r (1 / ((n : ℝ) + 1))
  have hspos (n : ℕ) : 0 < s n := by dsimp [s]; positivity
  have hsr (n : ℕ) : s n ≤ r := min_le_left _ _
  have hsanti : Antitone s := by
    intro a b hab
    dsimp [s]
    apply min_le_min_left
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hab 1
  have hscofinal : ∀ ε : ℝ, 0 < ε → ∃ n, s n ≤ ε := by
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    exact ⟨n, (min_le_right _ _).trans (le_of_lt hn)⟩
  intro A hA
  have hrepresent (n : ℕ) : ∃ B : Set (LocalZeroMeanTest (ball 0 (s n)) → ℝ),
      MeasurableSet B ∧ (localModConstPairings α hC (ball 0 (s n))) ⁻¹' B = A := by
    have hh := hA (s n) (hspos n)
    rw [fieldSigmaAlgebraModConst_eq_comap_localModConstPairings] at hh
    exact MeasurableSpace.measurableSet_comap.mp hh
  choose B hBm hBA using hrepresent
  let R (n : ℕ) : (LocalZeroMeanTest (ball 0 r) → ℝ) →
      (LocalZeroMeanTest (ball 0 (s n)) → ℝ) := fun v φ =>
    v ⟨φ.1, φ.2.1.mono_set (ball_subset_ball (hsr n)), φ.2.2⟩
  have hRm (n : ℕ) : Measurable (R n) := by
    apply measurable_pi_iff.mpr
    intro φ
    exact measurable_pi_apply (⟨φ.1, φ.2.1.mono_set (ball_subset_ball (hsr n)), φ.2.2⟩ : LocalZeroMeanTest (ball 0 r))
  let E (n : ℕ) := R n ⁻¹' B n
  let ELim := Filter.limsup E atTop
  have hEm : MeasurableSet ELim := MeasurableSet.measurableSet_limsup fun n => hRm n (hBm n)
  have hEP (n : ℕ) : (localModConstPairings α hC (ball 0 r)) ⁻¹' E n = A := hBA n
  have hEPLim : (localModConstPairings α hC (ball 0 r)) ⁻¹' ELim = A := by
    simp only [ELim, Filter.limsup_eq_iInf_iSup_of_nat, iInf_eq_iInter, iSup_eq_iUnion,
      preimage_iInter, preimage_iUnion, hEP]
    ext ω
    simp
    exact ⟨fun h => (h 0).2, fun h i => ⟨⟨i, le_rfl⟩, h⟩⟩
  let C (n : ℕ) : Set Ξ := (localModConstPairings α hD (ball 0 (s n))) ⁻¹' B n
  let CLim := Filter.limsup C atTop
  have hEC : (localModConstPairings α hD (ball 0 r)) ⁻¹' ELim = CLim := by
    simp only [ELim, CLim, Filter.limsup_eq_iInf_iSup_of_nat, iInf_eq_iInter, iSup_eq_iUnion,
      preimage_iInter, preimage_iUnion]
    rfl
  have hCgerm : ∀ ε : ℝ, 0 < ε →
      MeasurableSet[Section6.fieldSigmaAlgebraModConst α hD (ball 0 ε)] CLim := by
    intro ε hε
    obtain ⟨N, hN⟩ := hscofinal ε hε
    let C' (n : ℕ) : Set Ξ := if N ≤ n then C n else ∅
    have heq : Filter.limsup C' atTop = CLim := by
      apply Filter.limsup_congr
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      simp [C', hn]
    rw [← heq]
    let m : MeasurableSpace Ξ := Section6.fieldSigmaAlgebraModConst α hD (ball 0 ε)
    change @MeasurableSet Ξ m (Filter.limsup C' atTop)
    let : MeasurableSpace Ξ := m
    apply MeasurableSet.measurableSet_limsup
    intro n
    by_cases hn : N ≤ n
    · have hm : MeasurableSet[Section6.fieldSigmaAlgebraModConst α hD (ball 0 (s n))] (C n) := by
        rw [fieldSigmaAlgebraModConst_eq_comap_localModConstPairings]
        exact MeasurableSpace.measurableSet_comap.mpr ⟨B n, hBm n, rfl⟩
      have hm' := (fieldSigmaAlgebraModConst_mono α hD
        (ball_subset_ball ((hsanti hn).trans hN))) _ hm
      simpa [C', hn] using hm'
    · simp [C', hn]
  rcases hQtrivial CLim hCgerm with hz | ho
  · left
    have hz' : Q.map (localModConstPairings α hD (ball 0 r)) ELim = 0 := by
      rwa [Measure.map_apply hQmap hEm, hEC]
    have hp := hAC hz'
    rwa [Measure.map_apply hP hEm, hEPLim] at hp
  · right
    have hcm : MeasurableSet CLim := hQmap hEm |>.congr (by rw [hEC])
    have hz : Q CLimᶜ = 0 := by rw [measure_compl hcm (measure_ne_top Q CLim), ho]; simp
    have hz' : Q.map (localModConstPairings α hD (ball 0 r)) ELimᶜ = 0 := by
      rwa [Measure.map_apply hQmap hEm.compl, preimage_compl, hEC]
    have hp := hAC hz'
    rw [Measure.map_apply hP hEm.compl, preimage_compl, hEPLim] at hp
    simpa using measure_of_measure_compl_eq_zero hp

/-- Joint pairing-law domination by a whole-plane GFF transfers the origin
germ zero-one law across different sample spaces. -/
theorem origin_modConst_germ_trivial_of_pairing_law_realizations
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) (Q : Measure Ξ) [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hD : Ξ → (ℂ → ℝ) → ℝ}
    {hcirc : Ξ → ℝ → ℂ → ℝ}
    (hQ : IsWholePlaneGFF Q hD hcirc) (α : ℝ) {r : ℝ} (hr : 0 < r)
    (hP : Measurable (localModConstPairings α hC (ball 0 r)))
    (hAC : P.map (localModConstPairings α hC (ball 0 r)) ≪
      Q.map (localModConstPairings α hD (ball 0 r))) :
    ∀ A : Set Ω, (∀ ε : ℝ, 0 < ε →
      MeasurableSet[Section6.fieldSigmaAlgebraModConst α hC (ball 0 ε)] A) →
      P A = 0 ∨ P A = 1 := by
  let : IsProbabilityMeasure Q := hQ.isProbabilityMeasure
  have hQmap : Measurable (localModConstPairings α hD (ball 0 r)) := by
    apply measurable_iff_comap_le.mpr
    rw [← fieldSigmaAlgebraModConst_eq_comap_localModConstPairings]
    exact (Section6.fieldSigmaAlgebraModConst_le α hD _).trans (hQ.fieldSigmaAlgebra_le α _)
  exact origin_modConst_germ_trivial_of_trivial_reference P Q α hr hP hQmap
    (hQ.origin_germ_trivial α) hAC

/-- A local pairing-law comparison to a whole-plane GFF after any deterministic
pairing shift and any random additive recentering transfers its zero-one germ
law. The random constant need not be measurable. -/
theorem origin_modConst_germ_trivial_of_shifted_gff_realization
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) (Q : Measure Ξ) [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hD : Ξ → (ℂ → ℝ) → ℝ}
    {hcirc : Ξ → ℝ → ℂ → ℝ}
    (hQ : IsWholePlaneGFF Q hD hcirc) (α : ℝ) {r : ℝ} (hr : 0 < r)
    (d : (ℂ → ℝ) → ℝ) (c : Ξ → ℝ)
    (hP : Measurable (localModConstPairings α hC (ball 0 r)))
    (hAC : P.map (localModConstPairings α hC (ball 0 r)) ≪
      Q.map (localModConstPairings α (fun ω =>
        addFunPairing (fun φ => hD ω φ + d φ) (fun _ => c ω)) (ball 0 r))) :
    ∀ A : Set Ω, (∀ ε : ℝ, 0 < ε →
      MeasurableSet[Section6.fieldSigmaAlgebraModConst α hC (ball 0 ε)] A) →
      P A = 0 ∨ P A = 1 := by
  let : IsProbabilityMeasure Q := hQ.isProbabilityMeasure
  let hD' : Ξ → (ℂ → ℝ) → ℝ := fun ω =>
    addFunPairing (fun φ => hD ω φ + d φ) (fun _ => c ω)
  have heq (U : Set ℂ) : Section6.fieldSigmaAlgebraModConst α hD' U =
      Section6.fieldSigmaAlgebraModConst α hD U := by
    dsimp [hD']
    rw [fieldSigmaAlgebraModConst_add_random_constant]
    exact fieldSigmaAlgebraModConst_eq_of_deterministic_pairing_shift α hD
      (fun ω φ => hD ω φ + d φ) d (by intros; rfl) U
  have hQmap : Measurable (localModConstPairings α hD' (ball 0 r)) := by
    apply measurable_iff_comap_le.mpr
    rw [← fieldSigmaAlgebraModConst_eq_comap_localModConstPairings, heq]
    exact (Section6.fieldSigmaAlgebraModConst_le α hD _).trans (hQ.fieldSigmaAlgebra_le α _)
  have hz : ∀ A : Set Ξ, (∀ ε : ℝ, 0 < ε →
      MeasurableSet[Section6.fieldSigmaAlgebraModConst α hD' (ball 0 ε)] A) →
      Q A = 0 ∨ Q A = 1 := by
    intro A hA
    apply hQ.origin_germ_trivial α A
    intro ε hε
    rw [← heq]
    exact hA ε hε
  exact origin_modConst_germ_trivial_of_trivial_reference P Q α hr hP hQmap hz hAC

open Classical in
/-- The fixed-point pinch-frequency bridge accepts a reference with a trivial origin germ
on a different sample space. The local event representatives, stationarity,
one-scale probability bound and local joint law comparison remain explicit. -/
theorem ae_internal_pinchBlockDensity_of_trivial_reference
    {Ω Ξ : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) (Q : Measure Ξ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hD : Ξ → (ℂ → ℝ) → ℝ}
    (α : ℝ) {r : ℝ} (hr : 0 < r)
    (hP : Measurable (localModConstPairings α hC (ball 0 r)))
    (hQmap : Measurable (localModConstPairings α hD (ball 0 r)))
    (hQtrivial : ∀ A : Set Ξ, (∀ ε : ℝ, 0 < ε →
      MeasurableSet[Section6.fieldSigmaAlgebraModConst α hD (ball 0 ε)] A) →
      Q A = 0 ∨ Q A = 1)
    (hAC : P.map (localModConstPairings α hC (ball 0 r)) ≪
      Q.map (localModConstPairings α hD (ball 0 r)))
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ)
    (U T Q' V : Set ℂ) (M : ℝ) (X : ℕ → Ω → ℝ)
    (hXm : ∀ n, Measurable (X n)) (hbound : ∀ n ω, X n ω ∈ Icc (0 : ℝ) 1)
    (hX : ∀ᵐ ω ∂P, ∀ n, X n ω = if pinchPointEventWithInternalBounds (μ ω) (D ω)
      U T Q' V M ((2 : ℝ)⁻¹ ^ n) 0 then 1 else 0)
    (hXgerm : ∀ ε, 0 < ε → ∃ K, ∀ n, K ≤ n →
      Measurable[Section6.fieldSigmaAlgebraModConst α hC (ball 0 ε)] (X n))
    (hstat : P.map (fun ω n => X (n + 2) ω) = P.map (fun ω n => X (n + 1) ω))
    (δ : ℝ) (hδ : δ < (P {ω | pinchPointEventWithInternalBounds (μ ω) (D ω)
      U T Q' V M ((2 : ℝ)⁻¹ ^ 1) 0}).toReal) :
    ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop, δ * N ≤
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' V M ((2 : ℝ)⁻¹ ^ n) 0}.ncard : ℝ) := by
  let g : ℝ → MeasurableSpace Ω := fun ε =>
    Section6.fieldSigmaAlgebraModConst α hC (ball 0 (min ε r))
  have hm : Section6.fieldSigmaAlgebraModConst α hC (ball 0 r) ≤ mΩ := by
    rw [fieldSigmaAlgebraModConst_eq_comap_localModConstPairings]
    exact measurable_iff_comap_le.mp hP
  have hgle : ∀ ε, 0 < ε → g ε ≤ mΩ := by
    intro ε _
    exact (fieldSigmaAlgebraModConst_mono α hC (ball_subset_ball (min_le_right ε r))).trans hm
  have hgerm : ∀ ε, 0 < ε → ∃ K, ∀ n, K ≤ n → @Measurable Ω ℝ (g ε) _ (X n) := by
    intro ε hε
    exact hXgerm (min ε r) (lt_min hε hr)
  have htrivial : ∀ A : Set Ω, (∀ ε, 0 < ε → MeasurableSet[g ε] A) →
      P A = 0 ∨ P A = 1 := by
    intro A hA
    apply origin_modConst_germ_trivial_of_trivial_reference P Q α hr hP hQmap hQtrivial hAC A
    intro ε hε
    exact (fieldSigmaAlgebraModConst_mono α hC (ball_subset_ball (min_le_left ε r))) _ (hA ε hε)
  let F : Ω → ℕ → ℝ := fun ω n => X (n + 1) ω
  let : IsFiniteMeasure (P.map F) := P.isFiniteMeasure_map F
  exact ae_eventually_internal_pinch_block_density_of_ae_rep_of_lt_prob P μ D U T Q' V M 0 X
    g hgle hgerm htrivial hXm hbound hX (pointwiseBirkhoff_of_latticeProb _ _ _) hstat δ hδ

open Classical in
/-- The fixed-point pinch-frequency bridge accepts a comparison GFF living
on a different sample space. The local event representatives, stationarity,
one-scale probability bound and local joint law comparison remain explicit. -/
theorem ae_internal_pinchBlockDensity_of_pairing_law_realizations
    {Ω Ξ : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) (Q : Measure Ξ) [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hD : Ξ → (ℂ → ℝ) → ℝ}
    {hcirc : Ξ → ℝ → ℂ → ℝ}
    (hQ : IsWholePlaneGFF Q hD hcirc) (α : ℝ) {r : ℝ} (hr : 0 < r)
    (hP : Measurable (localModConstPairings α hC (ball 0 r)))
    (hAC : P.map (localModConstPairings α hC (ball 0 r)) ≪
      Q.map (localModConstPairings α hD (ball 0 r)))
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ)
    (U T Q' V : Set ℂ) (M : ℝ) (X : ℕ → Ω → ℝ)
    (hXm : ∀ n, Measurable (X n)) (hbound : ∀ n ω, X n ω ∈ Icc (0 : ℝ) 1)
    (hX : ∀ᵐ ω ∂P, ∀ n, X n ω = if pinchPointEventWithInternalBounds (μ ω) (D ω)
      U T Q' V M ((2 : ℝ)⁻¹ ^ n) 0 then 1 else 0)
    (hXgerm : ∀ ε, 0 < ε → ∃ K, ∀ n, K ≤ n →
      Measurable[Section6.fieldSigmaAlgebraModConst α hC (ball 0 ε)] (X n))
    (hstat : P.map (fun ω n => X (n + 2) ω) = P.map (fun ω n => X (n + 1) ω))
    (δ : ℝ) (hδ : δ < (P {ω | pinchPointEventWithInternalBounds (μ ω) (D ω)
      U T Q' V M ((2 : ℝ)⁻¹ ^ 1) 0}).toReal) :
    ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop, δ * N ≤
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' V M ((2 : ℝ)⁻¹ ^ n) 0}.ncard : ℝ) := by
  let : IsProbabilityMeasure Q := hQ.isProbabilityMeasure
  have hQmap : Measurable (localModConstPairings α hD (ball 0 r)) := by
    apply measurable_iff_comap_le.mpr
    rw [← fieldSigmaAlgebraModConst_eq_comap_localModConstPairings]
    exact (Section6.fieldSigmaAlgebraModConst_le α hD _).trans (hQ.fieldSigmaAlgebra_le α _)
  exact ae_internal_pinchBlockDensity_of_trivial_reference P Q α hr hP hQmap
    (hQ.origin_germ_trivial α) hAC μ D U T Q' V M X hXm hbound hX hXgerm hstat δ hδ

open Classical in
/-- A shifted and randomly recentered whole-plane GFF on a separate sample
space can be used as the reference for the fixed-point frequency bridge. -/
theorem ae_internal_pinchBlockDensity_of_shifted_gff_realization
    {Ω Ξ : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) (Q : Measure Ξ) [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hD : Ξ → (ℂ → ℝ) → ℝ}
    {hcirc : Ξ → ℝ → ℂ → ℝ}
    (hQ : IsWholePlaneGFF Q hD hcirc) (α : ℝ) {r : ℝ} (hr : 0 < r)
    (d : (ℂ → ℝ) → ℝ) (c : Ξ → ℝ)
    (hP : Measurable (localModConstPairings α hC (ball 0 r)))
    (hAC : P.map (localModConstPairings α hC (ball 0 r)) ≪
      Q.map (localModConstPairings α (fun ω =>
        addFunPairing (fun φ => hD ω φ + d φ) (fun _ => c ω)) (ball 0 r)))
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ)
    (U T Q' V : Set ℂ) (M : ℝ) (X : ℕ → Ω → ℝ)
    (hXm : ∀ n, Measurable (X n)) (hbound : ∀ n ω, X n ω ∈ Icc (0 : ℝ) 1)
    (hX : ∀ᵐ ω ∂P, ∀ n, X n ω = if pinchPointEventWithInternalBounds (μ ω) (D ω)
      U T Q' V M ((2 : ℝ)⁻¹ ^ n) 0 then 1 else 0)
    (hXgerm : ∀ ε, 0 < ε → ∃ K, ∀ n, K ≤ n →
      Measurable[Section6.fieldSigmaAlgebraModConst α hC (ball 0 ε)] (X n))
    (hstat : P.map (fun ω n => X (n + 2) ω) = P.map (fun ω n => X (n + 1) ω))
    (δ : ℝ) (hδ : δ < (P {ω | pinchPointEventWithInternalBounds (μ ω) (D ω)
      U T Q' V M ((2 : ℝ)⁻¹ ^ 1) 0}).toReal) :
    ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop, δ * N ≤
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' V M ((2 : ℝ)⁻¹ ^ n) 0}.ncard : ℝ) := by
  let : IsProbabilityMeasure Q := hQ.isProbabilityMeasure
  let hD' : Ξ → (ℂ → ℝ) → ℝ := fun ω =>
    addFunPairing (fun φ => hD ω φ + d φ) (fun _ => c ω)
  have heq (W : Set ℂ) : Section6.fieldSigmaAlgebraModConst α hD' W =
      Section6.fieldSigmaAlgebraModConst α hD W := by
    dsimp [hD']
    rw [fieldSigmaAlgebraModConst_add_random_constant]
    exact fieldSigmaAlgebraModConst_eq_of_deterministic_pairing_shift α hD
      (fun ω φ => hD ω φ + d φ) d (by intros; rfl) W
  have hQmap : Measurable (localModConstPairings α hD' (ball 0 r)) := by
    apply measurable_iff_comap_le.mpr
    rw [← fieldSigmaAlgebraModConst_eq_comap_localModConstPairings, heq]
    exact (Section6.fieldSigmaAlgebraModConst_le α hD _).trans (hQ.fieldSigmaAlgebra_le α _)
  have hz : ∀ A : Set Ξ, (∀ ε : ℝ, 0 < ε →
      MeasurableSet[Section6.fieldSigmaAlgebraModConst α hD' (ball 0 ε)] A) →
      Q A = 0 ∨ Q A = 1 := by
    intro A hA
    apply hQ.origin_germ_trivial α A
    intro ε hε
    rw [← heq]
    exact hA ε hε
  exact ae_internal_pinchBlockDensity_of_trivial_reference P Q α hr hP hQmap hz hAC
    μ D U T Q' V M X hXm hbound hX hXgerm hstat δ hδ


end HarmonicBalls
