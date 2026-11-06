# Interior regularity of the general-domain infimum

The frozen competitor class requires continuity on `closure U`, and the
potential-shifted class of all nonnegative superharmonic majorants is larger.
The existing Green-regular proof establishes equality with that larger envelope
by proving that its infimum is a continuous competitor on the whole closure.
That step is unavailable on an arbitrary bounded open domain; punctured-domain
examples show that closure continuity cannot be assumed.

`GeneralDomainInteriorInfimum.lean` proves boundedness below and upper
semicontinuity at every interior point, including the pole. At any off-pole
contact point it also proves continuity, using the continuous Green obstacle.
It reduces both desired conclusions to the following still-unproved statement:

```lean
IsSuperharmonicOn U (fun x => leastSupersolutionOn μ U z t x +
  greenPotentialBall μ R x)
```

Here the assumptions are `IsLocallyFiniteMeasure μ`, `0 < R`,
`VolumeGrowth μ R βm βp`, `IsOpen U`, `U ⊆ ball 0 R`, `z ∈ U`, and
`0 < t`. This is a derived local envelope claim, not a literature input.
It would follow from a proved local Poisson-modification argument preserving
closure continuity and the obstacle, or from a proved interior identification
with an appropriate superharmonic envelope. The present results do not prove
that claim and do not establish interior continuity at noncontact points or the
distributional inequality. No source or numbered-result closure is claimed.
