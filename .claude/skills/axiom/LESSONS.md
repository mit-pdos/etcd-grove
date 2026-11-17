# Lessons from review

One entry per critique of a run: date, the axiom, what the user said, the rule it became (in
`SKILL.md`).

## 2026-11-09: the Linux file extension flip-flopped for lack of a fixed configuration

Rounds 1-4 of the Fs v2 review each tested a different corner (xfs or ext4, a 256 MiB or 1 GiB
image, `commit=300` or `commit=1`, a one-byte starting file) of a semantics that claimed "ext4 or
xfs, Linux 6.x"; the ordered-growth rule was adopted on a test whose one-byte starting file made
ext4 order the data, and refuted by the next round on an empty file. The user: fix a target
configuration, a reasonable etcd deployment, and keep the semantics uniform (few special cases).
Rule (SKILL.md, step 3): test kernel claims on the extension's configuration through its helper,
vary the starting state, include the client's exact case, and test a source-argued claim before a
proof uses it.

## 2026-11-17: premise entailments that hold in every heap (ContextReadErrs.descs)

`ContextReadErrs.descs` (a premise of 50 closed results) and the axiom `incomingOf_cancelCtx` argued
per execution ("a location's persistent field value is fixed within an execution"), but were stated
as entailments from persistent points-tos, which hold in every heap: a fresh heap with just those
cells makes the pure conclusion a Lean fact at every location (`crossWorld`, proved;
`notes/axiom-review/ctx-descs.md`). Approved by the user, 2026-11-17, via etcd-grove-03, as a check of
the skill. Rule (SKILL.md, step 3, "A cross-world entailment"): check every entailment whose left side
bare persistent cells satisfy and whose conclusion is a pure equation of an opaque function of a
pointer.
