# General-domain noncontact harmonicity

Scope: the frozen `supersolutionsOn`, `leastSupersolutionOn` and `clusterOn`
in `HarmonicBalls/Draft/Section5.lean:103`, `:110` and `:114`. The paper's
ball definitions are at `paper/lqg_harmonic_ball-corrected.tex:583`–592;
its general-domain extension is stated at line 1017. The analogous ball
argument for openness and harmonicity appears at lines 3650–3666. This is
an audit of these derived general-domain statements, not a numbered-result
closure or a certification of the general-domain boundary convention.

For locally finite μ satisfying `VolumeGrowth μ R βm βp`, `0 < R`, open
`U ⊆ ball 0 R`, `z ∈ U` and `0 < t`, the new module proves:

- `isOpen_clusterOn_of_volumeGrowth`: the frozen cluster is open. At the pole,
  the existing punctured-neighborhood result handles the singular obstacle.
- `harmonicOnNhd_shifted_infimum_clusterOn`: the actual frozen infimum plus
  the enclosing-disc potential is harmonic on the whole cluster, pole included.
- `hasLaplacian_leastSupersolutionOn_clusterOn`: the unshifted infimum has
  `HasLaplacian ... μ 0` on the cluster, i.e. Δv = μ with the signs of
  `HarmonicBalls/Defs/Laplacian.lean:72`.

The uniform compact approximation lemma takes finite minima of actual frozen
competitors. The Poisson identity then combines that approximation with the
previously proved admissible Poisson modification and superharmonic inequality;
it does not identify the infimum with a separately defined envelope. Off the
pole the strict obstacle gap and continuity give a constant barrier; at the
pole the existing minus-infinity limit gives one. The Laplacian identity uses
Δq = −μ and Δ(v + q) = 0. No boundary regularity or global admissibility of
the infimum is assumed.

The proofs rely on potential-theoretic infrastructure of Leonardo Bonanno.
The unrelated issues of irregular-boundary semantics and numbered-result
source/definition/binder/dependency certification remain outside this audit.
