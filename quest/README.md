# rind questline

## Goal

Keep rind's living work organized as visible, versioned quests, grouped into
milestones ordered by priority.

## Plan

m0 holds urgent fixes: security advisories, broken CI, anything that breaks
MoQ on a published rind, a published adapter that diverges from its
upstream, and work that starves the agent hosts. m1 is everything MoQ needs
from rind to drop C cryptography, ending in the release MoQ switches to, and
the agent hosts' smaller costs. m2 holds work that
follows that release: the API audit's fixes, adoption beyond MoQ, and the
checks, measurements, and proof groundwork that keep rind correct and fast.
m3 holds work deferred by priority or waiting on the outside world. m4 holds
long-term work: C and regulated deployments, post-quantum and protocol
building blocks, and a proof of every hot path. m5 holds the cold tiers'
proofs.
