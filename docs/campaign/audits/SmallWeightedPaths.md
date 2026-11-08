# Small weighted paths: progress audit

Task: `deterministic-small-weighted-paths-from-diameter-bounds`.
The exact requested construction is recorded as `SmallWeightedPathExistence`;
this proposition is not yet proved.

`SmallWeightedPaths.lean` proves selection of an annular band, first contact
with an inner sphere, a stopped subpath, image-preserving arc-length
reparametrization, and existence of one annular piece with its stated weighted
cost bound. It also proves convergence of the real tails and the direct Weyl
bound supplied by a suitable path.

Still required: recursively choose compatible pieces, concatenate them, prove
that their concatenation avoids zero before its endpoint and remains in the
initial ball, reverse it, and control duration and weighted cost by the tails.
Then prove the unconditional Weyl estimate and uniform convergence.
No additional mathematical premise is claimed as necessary.
