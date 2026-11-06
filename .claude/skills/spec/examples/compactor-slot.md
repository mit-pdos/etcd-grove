# The compactor's slot: a hub's inline mode premise sealed, and a new mode in its body (2026-11-04)

**Kind:** a configuration premise of the server's hub (`NewServer.specG`), copied into a starter's
spec, converted to a sealed slot of the slot convention (`notes/spec-first-plan.md`), and widened in
the same change to a mode the old premise excluded (compaction with etcd's compactor off:
Kubernetes' deployment).

**Approved by the user** as Draft 2 ("approved"), after one `spec-reviewer` round. The module:
`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/BootCfg.lean`; the decision:
`notes/decisions.md`, "The compactor's slot".

## First version (Draft 1)

`v3compactor.bootCfg mode ret cmp cret := ret = 0 ∨ (cmp = true ∧ (revision … ∨ periodic …))`
replaces `if cmp then (revision … ∨ periodic …) ∧ on = false else ret = 0` in the hub and the
starter. The auth conjunct becomes its own premise, `cmp = true → on = false`. The introduction laws
were stated at literals (`bootCfg_off : bootCfg mode (W64 0) cmp cret`, `bootCfg_periodic … :
bootCfg "periodic" ret true 0`). There were three elimination laws, one per consumer fact (the
compaction mode, `New`'s premise, the permit). The proof re-read the slot at a second point to
rebuild the permit.

## Critiques and what they changed (the reviewer's)

1. **Introduction laws at literals burden callers.** Callers hold `retention = W64 0` and
   `cret = 0` as hypotheses, so each call needed a rewrite. Now the laws take them as premises
   (`bootCfg_off … : ret = W64 0 → …`).
2. **Three eliminations together restate the body.** Each was consumer-shaped, but a third mode
   would change all three and the hub's proof. Now there is one law, `bootCfg_build` (at `ret ≠ 0`:
   what the proof hands `New` and the permit's consumer), used once. The permit is carried in the
   proof's join disjunct instead of re-eliminated later.
3. **A coupling belongs to the subsystems it ties.** `on = false` was inside the compactor's branch.
   The proof showed it is the auth-on KV invariant's need, with or without a compactor, so it stays
   inline as `cmp = true → on = false`, not in the compactor's slot.
4. **The sealed docstring is now the only place a reader sees the scope restrictions** (`0 < ret`
   in revision mode, where Go accepts any nonzero retention). The doc says so.

## The approved spec

Draft 2 as above: the slot, three introduction laws from hypotheses, one narrow elimination, the auth
coupling inline. The fixed-mode starters' texts are unchanged (their proofs use the introduction
laws).

**Principles shown:** a slot's body can admit a new mode without changing the hub's text; state
introduction laws from what callers hold; one narrow elimination per consumption point, not one per
fact; put a coupling with the subsystems whose invariants need it.
