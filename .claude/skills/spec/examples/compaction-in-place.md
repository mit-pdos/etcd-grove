# M2, the apply side: compaction in the server's model, stated in place (2026-10-30/31)

**Target.** The server's apply side with compaction entries admitted
(`notes/m2-apply-plan.md`): the request kinds' premise `dispatchOk`, the KV invariant `kvInv`,
the uber-applier's and the apply loop's specs over them, the views tying the KV names' mode to
the server's, and the mvcc specs the compaction calls (`store.Compact`, `updateCompactRev`,
`compactLockfree`).

**Candidate 1 (Drafts, review rounds 1-3).** A compaction-mode family beside today's: a
mode-indexed `dispatchOkM`, `entryOkM`/`logShapeM`, a second invariant copy `kvInvD` inside a
drafted `isServerReqD`, with the off members `rfl`-equal to today's. mvcc's specs drafted
without the `ErrFutureRev` arm (`specD`).

**Review (spec reviewers, rounds 1-3).** Each round found a carrier the copies missed: round 1's
repair (`dispatchOkM`) left `rqShape`/`logShape` at today's premise (N-1, R3-1); the second
invariant copy left `isServerReq`'s readers at the old one (N-2, R3-2). First-tier findings 6, 2,
2, and most were caused by the previous round's repair.

**The user's critique (Q6 (a)).** State the switch in place: redefine `dispatchOk` and `kvInv`,
keep the text of every carrier (`rqShape`, `logShape`, `kvWork`, `entryOk`, `srvC`, the apply-loop
specs), read under the redefinitions, with laws that compaction off means today's
(`kvInvD_off : kvInvD γ γk false ⊣⊢ kvInv γ γk`, `dispatchOkD_iff`).

**Candidate 2 (approved by the user, 2026-10-31).** In place, as above (items 1-21 and 14'). Rounds
4-7 found 1, 2, 1 and then 0 first-tier findings, none of them a missed carrier. mvcc's three
specs lose the `ErrFutureRev` arm: the caller's certificate of a log with `rev` is of a prefix
of the committed log, so the arm cannot be taken, and `updateCompactRev`'s proof shows that branch
contradictory (`idxLogAuth_cert_prefix`). They also lose the `NoDelPutAt` premise, which the fork's
fixed `doCompact` no longer needs (the Probe's first step, `78024e8cd9` and after).

**What it shows.**
- A mode that widens a family of shared predicates goes in place, with laws for the old mode.
  Copies indexed by the mode must reach every carrier, and the reviews keep finding the one they
  missed.
- An error arm the precondition excludes costs every caller a case. Drop it and say why in the
  docstring.
