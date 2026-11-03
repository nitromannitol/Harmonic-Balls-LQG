# α₀-uniformity of constants printed as depending on γ (and b) only: E9, E22, E28

Task `alpha-uniformity` (c2). Source: `paper/lqg_harmonic_ball-corrected.tex` (tex line numbers below). Lean drafts:
`HarmonicBalls/Draft/Section{4,6,10}.lean`. Inputs used: Fact 2.1 (tex 402-414; `Proposed/LQG.lean`: Weyl scaling
`LQGMeasureWeylScaling` l.88, coordinate change `LQGMeasureCoordChange` l.108, locality l.79), full support I1
(`LQGMeasureFullSupportStmt`, `Draft/Section2.lean:109`), and the GFF facts of tex 355-389.

Setting: γ ∈ (0,2) and α₀ ∈ (-∞, Q) are fixed once and for all (tex 373-377), h = h^ℂ - α₀ log|·| (tex 383).
"Uniform in α₀" means one constant for all α₀ < Q (quantifier order ∃ const ∀ α₀).

## Verdicts

| item | printed claim | verdict | decisive step |
|---|---|---|---|
| E9, Lemma 4.2 (tex 717, 722) | α = α(γ) | **counterexample** (α₀ ↑ Q). Every admissible exponent satisfies α ≤ γ(Q-α₀). | §1, Steps 2-3: Poisson-Jensen at the singularity + μ_h(B_s(0)) = s^{γ(Q-α₀)} e^{γ h^ℂ_s(0)} M_s |
| E28, Lemma 6.4 (tex 1186) | a = a(b,p,γ) | **counterexample** (α₀ → -∞), at the admissible (r,z) = (1,0) for b < 0.41, and at (1,10) for every b ∈ (0,1) | §2, Step 3: μ_h = \|x\|^{\|α₀\|γ} μ_{h^ℂ} sends the mass fraction of a set Y with a fixed crossing probability to 0 |
| E22, Lemma 10.1 (tex 2499) | K = ⌈1/α⌉, α = α(γ) | **not refuted; the paper's proof gives only K(γ,α₀)**. A uniform K follows by localization (§3), conditional on (L4) | §3: one may choose ρ ≤ ε^{3/4} ≪ \|w\|, where the weight \|x\|^{-α₀γ} is flat on B_{2ρ} |
| downstream | — | **α₀ is fixed throughout; no proof needs uniformity in α₀.** [C8], [C25] lose nothing | §4 |

Lean status. `LeastSupersolutionHolderStmt` (Section4.lean:116), `GoodAnnulusProbabilityStmt` (Section6.lean:261),
`HarnackTypeEstimateStmt` (Section6.lean:197) and `VeryGoodAnnulusHarnackTypeStmt` (Section6.lean:403) already have
the order ∀ α₀ ∃ constant. **`ClusterBoundedCrossingsStmt` (Section10.lean:54) has the uniform order
`∃ α ∈ (0,1), ∀ α₀ < Q`**, which the drafted Section 6 statements do not give by the paper's proof (§3).

## 1. E9: Lemma 4.2 (odometer:cont, tex 721-727). Counterexample

**Claim.** Let γ ∈ (0,2), α > 0 and α₀ ∈ (Q - α/γ, Q), so that α > γ(Q-α₀). Fix t > 0. Almost surely there is no
C < ∞ with |w^0_t(x) - w^0_t(y)| ≤ C|x-y|^α for all x, y ∈ B_1. (Here w^0_t is the least supersolution
`leastSupersolution μ 1 0 t`, tex 588.) So no α = α(γ) > 0 serves all α₀ < Q, and [C8] needs α ≤ γ(Q-α₀).

*Step 1 (local equation; on the a.s. events of Lemmas 3.1, 3.2 and Prop 4.1).* w := w^0_t is continuous on the
closed unit disc (Lemma 3.1, tex 621-624). There is a random ε > 0 with B_ε(0) ⊂ Λ^0_t (Prop 4.1, tex 676-678,
with z = 0 ∈ B_1). On the open set B_ε(0) ⊂ Λ^0_t we have ∂Λ ∩ B_ε(0) = ∅, so Δw = μ_h there (Lemma 3.2,
tex 631). In particular w is subharmonic on B_ε(0).

*Step 2 (Poisson-Jensen formula at the centre).* For a continuous subharmonic u near the closed disc B̄_r(0) with
Riesz measure Δu (normalization Δ log|·| = 2π δ_0):
(1/2π)∫_0^{2π} u(re^{iθ}) dθ - u(0) = (1/2π) ∫_{B_r(0)} log(r/|y|) Δu(dy)
(Ransford, *Potential Theory in the Complex Plane*, §4.5; Armitage-Gardiner §4.5). The paper's Δ satisfies
ΔG_O(x,·) = -δ_x (tex 631, with G_O the Green function of BM, tex 469), so its Δ is a fixed positive multiple of
the standard one; write c_Δ > 0 for the resulting constant. For r < ε, with log(r/|y|) ≥ log 2 on B_{r/2}(0):
sup_{|x|=r} |w(x) - w(0)| ≥ avg_{∂B_r} w - w(0) ≥ c_Δ log 2 · μ_h(B_{r/2}(0)).
If the Hölder bound held with exponent α, then μ_h(B_{r/2}(0)) ≤ C r^α/(c_Δ log 2) for all r < ε. That is,
limsup_{s↓0} μ_h(B_s(0)) s^{-α} < ∞.

*Step 3 (law of the mass of small balls at the singularity).* Let s ∈ (0,1). The coordinate change for x ↦ sx
(Fact 2.1 IV, tex 412) and Weyl scaling by the constant Q log s + h_s(0) (Fact 2.1 III) give
μ_h(B_s(0)) = s^{γQ} e^{γ h_s(0)} M_s, where M_s := μ_{h(s·) - h_s(0)}(B_1(0)).
The circle average of -α₀ log|·| on ∂B_s(0) is -α₀ log s, so h_s(0) = h^ℂ_s(0) - α₀ log s. Hence
μ_h(B_s(0)) = s^{γ(Q-α₀)} e^{γ h^ℂ_s(0)} M_s.
By eq:h-coordinate-change (tex 386) and the measurability of the field-to-measure map (Fact 2.1 II),
M_s has the law of μ_h(B_1(0)). That law is supported in (0,∞): finiteness holds since μ_h is Radon, and
positivity by full support I1. Moreover h^ℂ_s(0) ~ N(0, log(1/s)) for the normalization h^ℂ_1(0) = 0 (tex 379).
Put δ := α - γ(Q-α₀) > 0 and fix K ≥ 1. A union bound gives
P[μ_h(B_s(0)) < K s^α] ≤ P[N(0,1) < -(δ/2γ) (log 1/s)^{1/2}] + P[μ_h(B_1(0)) < K s^{δ/2}],
and both terms tend to 0 as s ↓ 0. So F_K := {∃ s ∈ (0,1/K) : μ_h(B_s(0)) ≥ K s^α} has P(F_K) = 1, since it
contains each of these events. On ∩_K F_K we get limsup_{s↓0} μ_h(B_s(0)) s^{-α} = ∞, which contradicts Step 2.
This proves the claim, so the conclusion of Lemma 4.2 with exponent α has probability 0, not just less than 1. ∎

Remarks.
- The obstruction sits at the singularity and only as α₀ ↑ Q. It matches [C1]: the upper volume exponent at z = 0
  is γ(Q-α₀) (E1). The same argument bounds the random exponent of Prop 2.5 (`GreenPotentialLiouvilleHolderStmt`)
  for f = 1 and any O ∋ 0. That draft has a random exponent, so nothing there is false.
- For α₀ ≤ α₁ < Q one expects a uniform exponent below min{(2-γ)²/2, γ(Q-α₁)}, by the Campanato route of Prop 2.5.
  This is not needed (§4) and not proved here.

## 2. E28: Lemma 6.4 (lemma:annulus-hit, tex 1185-1189). Counterexample

Lemma 6.4: for b, p ∈ (0,1) there is a = a(b,p,γ) with P[E_r(z;a,b)] ≥ p for all r > 0 and all z with
dist(𝔸_{3r,5r}(z), 0) ≥ r/100. Here E_r(z;a,b) is eq:good-annulus-harmonic (tex 1117-1121).

*Step 1 (reading of the event).* Write A := 𝔸_{3r,5r}(z), τ_A and τ_Y for the exit times, and u ∈ ∂B_{4r}(z).
"B^u exits A before exiting Y" can only mean τ_A ≤ τ_Y, the reading recorded in `Defs/Annuli.lean` (slip at tex
1120). Indeed Y ⊂ A forces τ_Y ≤ τ_A, so the strict reading τ_A < τ_Y would make the probability 0 and E_r(z)
trivial.

*Step 2 (a set with a fixed crossing probability).* Take r = 1 and z = 0, which is admissible since
dist(𝔸_{3,5}(0), 0) = 3 ≥ 1/100. Let Y := 𝔸_{3,4.9}(0) and |u| = 4. If B^u hits ∂B_3 before ∂B_{4.9}, then
τ_A = τ_Y. Hence P[τ_A ≤ τ_Y] ≥ log(4.9/4)/log(4.9/3) = 0.4136… (the harmonic function log(4.9/|x|)/log(4.9/3)).
So for b < 0.4136 we have E_1(0;a,b) ⊂ {μ_h(Y) > a μ_h(A)}.

*Step 3 (Weyl scaling).* On the annulus 𝔸_{2,6}(0), h = h^ℂ + f with f := -α₀ log max{|·|, 1}. This f is continuous
on ℂ and equals -α₀ log|·| there. Locality and Weyl scaling (Fact 2.1 II, III; also tex 2211) give
μ_h = |x|^{-α₀γ} μ_{h^ℂ} on 𝔸_{2,6}(0). For α₀ < 0 the weight |x|^{|α₀|γ} is increasing in |x|, so
μ_h(Y)/μ_h(A) ≤ (4.9/4.95)^{|α₀|γ} R, with R := μ_{h^ℂ}(𝔸_{3,4.9}(0)) / μ_{h^ℂ}(𝔸_{4.95,5}(0)).
R is a.s. in (0,∞): the numerator is finite because μ is Radon, and the denominator is positive by full support I1.
The law of R does not depend on α₀.

*Step 4.* P[E_1(0;a,b)] ≤ P[R > a (4.95/4.9)^{|α₀|γ}] → 0 as α₀ → -∞. So for b ∈ (0, 0.41], p ∈ (0,1) and any
a ∈ (0,1), some α₀ < 0 gives P[E_1(0;a,b)] < p. Hence no a(b,p,γ) serves all α₀ < Q. ∎

*Strengthening: every b ∈ (0,1), with the configuration actually used.* The proof of Lemma 6.3 uses Lemma 6.4 for
z ∈ ℂ \ B_{10r} (tex 1289). Take r = 1 and z = 10, which is admissible (dist = 5). Let p₀ := 15 be the point of
∂B_5(z) farthest from 0. Put Cap_δ := A ∩ {|x| ≥ 15-δ} and Y := A \ Cap_δ. Cap_δ lies in B̄_{d}(p₀) with
d = d(δ) → 0 as δ → 0, because points y = x - z with |y| ≤ 5 and |x| ≥ 15-δ satisfy y·(z/|z|) ≥ 5 - 1.5δ.
BM from u ∈ ∂B_4(z) must hit B̄_d(p₀) before leaving B_{10}(p₀) ⊃ A, and |u - p₀| ≥ 1. So
P[τ_A ≤ τ_Y] ≥ 1 - log 10/log(10/d) → 1. Meanwhile
μ_h(Y)/μ_h(A) ≤ ((15-δ)/(15-δ/2))^{|α₀|γ} · μ_{h^ℂ}(A)/μ_{h^ℂ}(A ∩ {|x| > 15-δ/2}) → 0 as α₀ → -∞.
The denominator is a.s. positive by I1, since A ∩ {|x| > 15-δ/2} is a nonempty open set. So the obstruction is not
z = 0 itself: any annulus at distance ≍ r from the singularity fails as α₀ → -∞. This includes the uses at tex 1289
and in Lemma 6.7 Step 1 (tex 1321-1345, G19).

*What does hold.* For α₀ ∈ [-A, Q), a uniform a exists. If dist(𝔸_{3r,5r}(z), 0) ≥ r/100, then
sup/inf of |x|^{-α₀γ} on 𝔸_{3r,5r}(z) is ≤ 1001^{|α₀|γ}. (If |z| ≤ 2.99r then |x| ∈ [r/100, 7.99r]; if
|z| ≥ 5.01r then the ratio (|z|+5r)/(|z|-5r) is ≤ 1001.) So the corrected Step 1 (G19(i),(ii)) gives
a := a'·1001^{-max(A,Q)γ}, where a' is the α₀ = 0 constant. As α₀ ↑ Q there is no obstruction for 6.4: the
weight stays bounded on annuli away from 0. [C25] (a = a(b,p,γ,α₀)) is the natural correction.

## 3. E22: Lemma 10.1 (lemma:cannot-cross, tex 2496-2545)

Printed: K := ⌈1/α⌉ with α = α(γ) ∈ (0,1) "as in Prop 6.2" (tex 2499).

*3.1 What the paper's proof gives.* The proof (tex 2505-2545) takes a very good ρ ∈ [ε, ε^{1/2}] from Prop 6.1
plus Borel-Cantelli (tex 2505-2507). It then uses Prop 6.2 to give each crossing component mass
≥ α μ_h(𝔸_{ρ/2,ρ}(x₀)), and concludes there are ≤ 1/α of them. The α is that of eq:choice-of-alpha,
α = a 2^{-N₀β⁻}/(C₁⁻ ∨ 1) (tex 1855). Here a, C₁^±, C₂^±, N₀ come from Lemmas 6.6/6.7 (tex 1296-1316). Those get their
α₀-dependence from the Weyl reductions (tex 1198-1217, 1321-1341; G19(iii)), and §2 shows that dependence is
genuine for Lemmas 6.4/6.7 as stated "for all r (ρ)". The same computation as §2 refutes an α₀-uniform C₁⁻ in
Lemma 6.7 at the admissible x₀ = 0 (dist(𝔸_{ρ/4,2ρ}(0), 0) = ρ/4). As α₀ → -∞,
M^h_1(0)/μ_h(𝔸_{1/4,2}(0)) ≤ (5/(4·1.95))^{|α₀|γ} M^{h^ℂ}_1(0)/μ_{h^ℂ}(𝔸_{1.95,2}(0)) → 0.
So the paper's proof gives only **K = K(γ, α₀)**. This matches the Section 6 drafts (∀ α₀ ∃ α) but not
`ClusterBoundedCrossingsStmt`, which is drafted with α before α₀.

*3.2 No counterexample by the E9/E28 mechanism.* That mechanism needs either the singular point itself (E9) or an
annulus at distance ≍ its radius from 0 (E28). In Lemma 10.1 we have w ∉ B_{20√ε}. The radius ρ ∈ [ε, ε^{1/2}] is
ours to choose, and "each small enough ε" has a random threshold that may depend on α₀. By the definition at tex
338-339 (P ≥ 1 - O(r^p)), the same holds for every "polynomially high probability". Choosing ρ ≤ ε^{3/4} makes
ρ/|x₀| ≤ ε^{1/4}/10 → 0, so the weight is flat at the relevant scales.

*3.3 Localization proof that K can be chosen depending on γ only.* Fix α₀. Let P = (N₀, a, b, C₁^±, C₂^±, C₃) and
β⁻ = β⁻(γ) > (2+γ)²/2 be the parameters of the α₀ = 0 instance of the proof of Prop 6.1 (Lemma 6.6 at α₀ = 0;
b by eq:choice-of-b, tex 1908). Put P' := (N₀', a/2, b, C₁⁻/2, 2C₁⁺, C₂⁻/2, 2C₂⁺, C₃) with
N₀' := max{N₀, N₁(a/2, β⁻, C₁⁻/2, 2C₂⁺)} (eq:choice-of-N1, tex 1913). Raising N₀ only weakens (VG-iii). P' depends on γ
only.
- **(L1) Flatness.** Let |x₀| ≥ 10√ε, ρ ∈ [ε, ε^{3/4}] and u := 2ρ/|x₀| ≤ ε^{1/4}/5. For x ∈ B_{2ρ}(x₀) the weight
  g(x) := (|x|/|x₀|)^{-α₀γ} satisfies |log g| ≤ |α₀|γ·(-log(1-u)) ≤ 1.25 u|α₀|γ ≤ |α₀|γ ε^{1/4}/4. So
  g ∈ [2^{-1/2}, 2^{1/2}] once ε ≤ ε₀(α₀,γ) := (2 log 2/(|α₀|γ))^4.
- **(L2) Deterministic transfer.** On B_{2ρ}(x₀), μ_h = |x₀|^{-α₀γ} g μ_{h^ℂ}, by locality and Weyl scaling as in §2,
  Step 3. Each of (VG-i)-(VG-iii) involves μ only on B_{2ρ}(x₀): M_ρ uses balls in B_{5ρ/4}(x₀), SG uses
  𝔸_{ρ/4,2ρ}(x₀), and the annuli 𝔸_{3r,5r}(z) of (VG-iii) have z ∈ 𝔸_{ρ/2,ρ}(x₀) and r ≤ 2^{-N₀/2}ρ. Each condition is
  invariant under μ ↦ λμ (for E_r see tex 1290). Under μ ↦ gμ with sup g/inf g ≤ 2, each ratio moves by a factor
  ≤ 2, and BM probabilities do not involve μ. Hence E̅_ρ(x₀; P)[μ_{h^ℂ}] ⊂ E̅_ρ(x₀; P')[μ_h].
- **(L3) Counting at α₀ = 0 on the sub-range.** Run the proof of Lemma 6.6 (Lemma 6.5 iteration, tex 1262-1291,
  1371, with Lemma 6.7 at α₀ = 0) on the ≈ (1/4) log₈ ε^{-1} radii in [ε, ε^{3/4}] ∩ {8^{-n}} instead of
  [ε, ε^{1/2}]. With polynomially high probability, every grid x₀ ∈ B_{1+ε} \ B_{10√ε} then has ≥ c'' log ε^{-1}
  radii ρ ∈ [ε, ε^{3/4}] with E̅_ρ(x₀; P)[μ_{h^ℂ}], for a universal c'' > 0. The exponent of Lemma 6.5 is free, which
  beats the O(ε^{-2}) union bound exactly as at tex 1282-1291.
- **(L4) α₀-free Harnack constant.** The audit of tex 1386-1955 found that Lemma 6.11 is "purely deterministic"
  (tex 1600). It uses μ only on B_{2ρ}(x₀), and nothing in tex 1386-1955 mentions α₀, the origin or the weight. Its
  constants are explicit: α = a 2^{-N₀β⁻}/(C₁⁻ ∨ 1) (tex 1855), b = 2^{-2β⁻/((C'C₃)∨1)} (tex 1908), and
  N₁(a, β⁻, C₁⁻, C₂⁺, C₄, c) (tex 1913). The constants C', C₄, c come from Lemmas 6.13, 6.8, 6.10 and are geometric.
  β⁻ is only a chosen exponent there (eq:ball-volume is not used). Lines 1600, 1855, 1908 and 1913 were checked
  directly. Lemma 6.11 for μ_h at P' therefore gives α' := α(P', β⁻), which depends on γ only.

With (L1)-(L4), the proof of Lemma 10.1 at tex 2505-2545 runs verbatim with ρ ∈ [ε, ε^{3/4}] ⊂ [ε, ε^{1/2}] and
Borel-Cantelli over ε = 2^{-n}, n ≥ max{M₀, log₂ ε₀^{-1}}. It gives **K = ⌈1/α'⌉ = K(γ)**. The same argument shows
that the printed γ-only constants of Lemma 6.3 (a(b,γ)), Lemma 6.6 and Prop 6.1 (α(γ), universal c) are true: these
are multi-scale statements over x₀ ∉ B_{10√ε}. The α₀-independent gaps of the paper's own proofs (G18, G28, G32, the
constant slips at 1859, 1899, 1916) are unaffected. The ε^{3/4} cap is also compatible with the G32(d) fix
(ε' = 2^{-n} ≥ ε).

*Verdict E22.* The printed uniformity is **true** (proof §3.3). The paper's proof gives only K(γ,α₀): this is a gap,
not a false statement. Recommendation: keep `ClusterBoundedCrossingsStmt` uniform as printed, and register the gap
"10.1 needs (L1)-(L4)" in GRAPH. Alternatively, change the draft to ∀ α₀ ∃ α. That form follows from the drafted
Prop 6.1/6.2 by the printed proof, and nothing downstream needs more (§4). It would, however, be weaker than the
printed true statement.

## 4. Downstream: α₀ is fixed; nothing needs uniformity

- α₀ is fixed once (tex 373, 377) and every result is about that h. The paper never takes a limit, supremum or
  infimum over α₀. The only other values ever used are two fixed instances:
  - α₀ = 0: the reductions in Lemma 6.4 (tex 1195-1220), Lemma 6.7 (tex 1318-1349), Section 11 Step 1 (tex 2834)
    and Lemma 11.12 (tex 3136-3137);
  - α₀ = γ: Lemma 8.3 (lemma:doubling-alpha), applied inside the proof of Lemma 8.2 (tex 2220) at μ_h-typical
    points (DS14 Lemma A.10, tex 2213). Lemma 8.3 uses Lemma 6.7 at x₀ = 0 (tex 2175-2178), which is admissible.
    The constants are those at α₀ = γ, so they depend on γ.
  Statements quantified ∀ α₀ < Q ∃ constants (all Draft Stmts except 10.1) supply both instances.
- Consumers of the α of Prop 6.1, at the fixed α₀:
  - Prop 7.1 (tex 1969-1996), Prop 7.2 (tex 2031-2078) and Lemma 10.1 (tex 2505-2519);
  - Thm 5.5, through Props 5.1-5.4. Its scale invariance (Lemma 5.7, tex 885-899) rescales about 0 and keeps α₀.
  Each consumer needs α to be deterministic and positive, nothing more. Section 10 needs only K < ∞.
- Order of constants under [C25]. Only a, C₁^±, C₂^± (and N₁) gain α₀. C₃ and c stay universal: they come from
  Lemma 6.3's c and Lemma 6.5, and the Weyl steps change only a, C₁^±, C₂^±. So the order of G28,
  C₃ → b(γ, C₃, β⁻) (Lemma 6.11) → (a, C^±, N₀) (Lemma 8.3 at α₀ = γ, Lemma 6.6 at α₀), has no cycle.
- Same-type slip, harmless: Section 11 Step 2 (tex 2857-2866) calls the Weyl constant "universal" under only
  dist(𝔸_{r,6r}(z), 0) > r/100. It is universal (≤ 2, say) once n ≥ N(z, α₀), by (L1). The proof is free to take N(z)
  that large.
- **Conclusion.** [C8] (α = α(γ,α₀), with necessarily α ≤ γ(Q-α₀)) and [C25] (a = a(b,p,γ,α₀)) lose nothing
  downstream. Both are forced: §1 and §2 are counterexamples to the printed uniformity. For Lemma 10.1, Prop 6.1,
  Lemma 6.3 and Lemma 6.6 the printed uniformity is true (§3.3), but nothing downstream uses it.
