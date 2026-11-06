# General-domain time convexity

Scope: the frozen `supersolutionsOn` and `leastSupersolutionOn` in
`HarmonicBalls/Draft/Section5.lean:103` and `:109`. The paper's ball
competitor and infimum definitions are in `paper/lqg_harmonic_ball-corrected.tex:583`
and `:588`; the general-domain extension is at line 1017. This audit concerns
these derived scalar estimates and does not certify a numbered result.

For locally finite μ, `0 < R`, `VolumeGrowth μ R βm βp`, open
`U ⊆ ball 0 R`, `z ∈ U`, and `x ∈ closure U`, the new module proves that
`leastSupersolutionOn μ U z · x` is antitone and convex on `Ici 0`, and locally
Lipschitz on `Ioi 0`. At the pole it uses the proved enclosing-disc potential
lower bound to establish actual real GLB semantics. Off the pole it uses the
existing GLB result; zero is an admissible competitor for nonnegative time.
Convex combinations preserve the distributional Laplacian inequality and the
interpolated obstacle. Approximation of both real infima proves convexity.

For `0 < s ≤ T`, `leastSupersolutionOn_uniform_lipschitz_time` supplies one
constant for all `x ∈ closure U` and both times in `[s,T]`, stronger than the
requested compact-set estimate. In the interior, the disc potential gives the
lower bound; at the boundary the frozen infimum is zero. Continuity of the disc
potential on the closed enclosing ball gives a uniform bound. The Mathlib
convex-function Lipschitz estimate then gives a uniform constant.

The proofs use potential-theoretic infrastructure of Leonardo Bonanno. They
make no claim of boundary regularity, admissibility of the infimum, or right
continuity of cluster closures at boundary contact. No literature proposition
is introduced as an input.
