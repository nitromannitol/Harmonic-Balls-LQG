import HarmonicBalls.Proofs.Sec11.ModConstPairingLaw

/-! # Random additive constants in local pairing laws

The Section 8 germ and Birkhoff arguments use Leonardo Bonanno's LatticeProb
formalization. These identities allow arbitrary random choices of additive
constant; they do not establish a rooted law comparison.
-/

namespace HarmonicBalls

open Set Metric Filter MeasureTheory

/-- Zero-integral local pairings are unchanged by an arbitrary random constant,
without a samplewise linearity or measurability assumption. -/
theorem localModConstPairings_add_random_constant {Ω : Type*} (α : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (c : Ω → ℝ) (U : Set ℂ) :
    localModConstPairings α (fun ω => addFunPairing (hC ω) (fun _ => c ω)) U =
      localModConstPairings α hC U := by
  funext ω φ
  simp only [localModConstPairings, fieldPairing, addFunPairing, integral_const_mul,
    φ.property.2, mul_zero, add_zero]

/-- Modulo-constant local field sigma algebras are insensitive to random
additive recentering. -/
theorem fieldSigmaAlgebraModConst_add_random_constant {Ω : Type*} (α : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (c : Ω → ℝ) (U : Set ℂ) :
    Section6.fieldSigmaAlgebraModConst α
        (fun ω => addFunPairing (hC ω) (fun _ => c ω)) U =
      Section6.fieldSigmaAlgebraModConst α hC U := by
  simp only [fieldSigmaAlgebraModConst_eq_comap_localModConstPairings,
    localModConstPairings_add_random_constant]

/-- The full joint zero-integral pairing law comparison is unchanged by
independently chosen random additive constants on two realizations. -/
theorem localModConstPairings_ac_add_random_constants_iff
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) (Q : Measure Ξ) (α β : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hD : Ξ → (ℂ → ℝ) → ℝ)
    (c : Ω → ℝ) (d : Ξ → ℝ) (U : Set ℂ) :
    P.map (localModConstPairings α
        (fun ω => addFunPairing (hC ω) (fun _ => c ω)) U) ≪
      Q.map (localModConstPairings β
        (fun ω => addFunPairing (hD ω) (fun _ => d ω)) U) ↔
    P.map (localModConstPairings α hC U) ≪ Q.map (localModConstPairings β hD U) := by
  rw [localModConstPairings_add_random_constant, localModConstPairings_add_random_constant]

/-- Local zero-integral pairing-law comparison yields the origin germ zero-one
law after arbitrary random recentering. -/
theorem origin_randomConstant_modConst_germ_trivial_of_pairing_law
    {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω) [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hQ : IsWholePlaneGFF Q hC hcirc) (α : ℝ) (c : Ω → ℝ)
    {r : ℝ} (hr : 0 < r)
    (hAC : P.map (localModConstPairings α hC (ball 0 r)) ≪
      Q.map (localModConstPairings α hC (ball 0 r))) :
    ∀ A : Set Ω, (∀ ε : ℝ, 0 < ε →
      MeasurableSet[Section6.fieldSigmaAlgebraModConst α
        (fun ω => addFunPairing (hC ω) (fun _ => c ω)) (ball 0 ε)] A) →
      P A = 0 ∨ P A = 1 := by
  intro A hA
  apply origin_modConst_germ_trivial_of_modConst_pairing_law P Q hQ α hr hAC A
  intro ε hε
  rw [← fieldSigmaAlgebraModConst_add_random_constant α hC c (ball 0 ε)]
  exact hA ε hε

open Classical in
/-- The fixed-point pinch-frequency bridge accepts local observables of an
arbitrarily recentered field. Stationarity, representatives, the one-scale
probability bound and the joint law comparison remain explicit. -/
theorem ae_internal_pinchBlockDensity_of_randomConstant_pairing_law
    {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω) [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hQ : IsWholePlaneGFF Q hC hcirc) (α : ℝ) (c : Ω → ℝ)
    {r : ℝ} (hr : 0 < r)
    (hAC : P.map (localModConstPairings α hC (ball 0 r)) ≪
      Q.map (localModConstPairings α hC (ball 0 r)))
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ)
    (U T Q' V : Set ℂ) (M : ℝ) (X : ℕ → Ω → ℝ)
    (hXm : ∀ n, Measurable (X n)) (hbound : ∀ n ω, X n ω ∈ Icc (0 : ℝ) 1)
    (hX : ∀ᵐ ω ∂P, ∀ n, X n ω = if pinchPointEventWithInternalBounds (μ ω) (D ω)
      U T Q' V M ((2 : ℝ)⁻¹ ^ n) 0 then 1 else 0)
    (hXgerm : ∀ ε, 0 < ε → ∃ K, ∀ n, K ≤ n →
      Measurable[Section6.fieldSigmaAlgebraModConst α
        (fun ω => addFunPairing (hC ω) (fun _ => c ω)) (ball 0 ε)] (X n))
    (hstat : P.map (fun ω n => X (n + 2) ω) = P.map (fun ω n => X (n + 1) ω))
    (δ : ℝ) (hδ : δ < (P {ω | pinchPointEventWithInternalBounds (μ ω) (D ω)
      U T Q' V M ((2 : ℝ)⁻¹ ^ 1) 0}).toReal) :
    ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop, δ * N ≤
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' V M ((2 : ℝ)⁻¹ ^ n) 0}.ncard : ℝ) := by
  apply ae_internal_pinchBlockDensity_of_modConst_pairing_law P Q hQ α hr hAC
    μ D U T Q' V M X hXm hbound hX _ hstat δ hδ
  intro ε hε
  obtain ⟨K, hK⟩ := hXgerm ε hε
  refine ⟨K, fun n hn => ?_⟩
  rw [← fieldSigmaAlgebraModConst_add_random_constant α hC c (ball 0 ε)]
  exact hK n hn


end HarmonicBalls
