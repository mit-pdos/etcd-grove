---
title: auth.ValidSpec is false (isValidSimpleToken panics on a nil context)
found: 2026-11-12
by: the etcd_auth_safe Scope (etcd-grove-81's agent), /shared/tmp/auth-safe/scope.md
blocks-proof: yes (for an auth closed theorem)
status: fixed on branch auth-schema-fix (2026-11-12; 9e624451ee, d9f4a2dd66); not landed, pending etcd-grove-81's axiom re-review
---
# `auth.ValidSpec` is false

A bug in this repository's specs, not in etcd.

`auth.ValidSpec` (`Proof/go_etcd_io/etcd/server/v3/auth/TokenSimple.lean:253`) claims that
`isValidSimpleToken` returns for every context, nil included. In Go a nil context with a token of the
simple provider's shape (`x.1`) panics: a `select` evaluates every channel operand on entry, so
`ctx.Done()` runs on the nil interface even when the other case is ready
(`/shared/tmp/auth-safe/nilctx/main.go`: "nil pointer dereference"). The simple provider is
constructible (`token_simple_new`), so the hypothesis is refutable through adequacy.

**Reach.** Exported results that take it, and are vacuous until the fix: `srv_auth_tp_on`,
`server_new_auth_on`, `authkv_startServer`, `authkv_Main`. No closed `*_safe` theorem rests on it.
`etc/tcb-report.py` does not show it (a hypothesis, not an axiom or `sorry`).

**Fix (decided by etcd-grove-81).** No trust change: the request side already holds a real context;
the token contract's `info` clause takes `auth.ctxDoneAny` ("`Done()` returns nil or a channel safe to
receive on"), and `ValidSpec` goes. Scheduled after k8s 7f-4's request-side changes.

## Fixed (branch `auth-schema-fix`, 2026-11-12; accepted by etcd-grove-81)

`ValidSpec` is deleted (with `tokenSimple_info`, `tokenProviderOkCtx`, `tokenSimple_okCtx`); no axiom
or premise replaces it.

- **The context** (`9e624451ee`): the token contract's `info` clause (`tokenProviderOkA`/
  `tokenProviderOk`, `auth/InvAuth.lean`) takes `auth.ctxDoneRecv ci` (`auth/CtxDone.lean`,
  hlc-generic: `Done()` returns nil or a channel safe to receive on; `ctxDoneRecv_of_ctxDoneAny` at
  `hasLC`). `isValidSimpleToken` is proved over it, a nil `Done()` included (the `select` blocks on
  the nil channel's clause). `authInfoFromToken`/`AuthInfoFromCtx` take it; `AuthReqDerive` gets it
  from `isReqAuth`'s `ctxDoneAny`.
- **The provider's readiness** (`d9f4a2dd66`, option A of blocker 2): the simple provider's waiter
  closure reads `srv.applyWait`, which Go sets only in `start`, so the contract cannot be proved at
  `NewServer`. The `info` clause also takes `auth.tpReady M` (in `.on γa`, a persistent one-shot
  "shot" at the new ghost name `AuthNames.rdy`; `True` in the other modes). `NewServer` allocates
  `srvTpInv` (`etcdserver/InvStart.lean`: pending, or shot with the persistent `applyWait` field and
  its `isWaitTime`) and proves the closure's contract under it; `start` fires the shot after it
  sets `s.applyWait`. Holders from before `start` carry `□ (auth.tpReady M -∗ …)`.
- `authSrvTP_on`, `srv_auth_tp_on`, `server_new_auth_on` and examples/etcd/auth's results drop
  `hValid`. In its place the server supplies the index waiter's contract, which holds once the
  readiness cell is shot: `authSrvTP true` (the conclusion of `srv_auth_tp_on`) gained a universally
  quantified `γy`, a premise (the waiter's contract `□ (⌜on⌝ → ∀ idx, {{ tpShot γy }} iw idx
  {{ anyRecv }})`) and a post conjunct `γa.rdy = γy`: a different statement, true of Go, not a
  strengthening (`ValidSpec` stood in for the waiter's contract, so the old one asked nothing of
  `iw`). `NewServer` discharges the new premise through `srvTpInv`, so for `ValidSpec` `server_new_auth_on`
  and the authkv results lose a premise; they are not strictly stronger overall, because the same
  branch's unknown-fields tightening (R-M1, and the review's MAJ-1/MAJ-2) makes their premise D22
  (`authSchemaSrv`) harder to meet on reads: the read contract now promises messages without
  unknown fields (and stored permissions without any, `Options` holding the record's bytes), which
  the real backend's derivation must show. (Re-review 2026-11-13, M3; M1-M2: `newAuthStore_boot` and
  `auth_store_boot_on` take the readiness cell's name `γy` and return `γa.rdy = γy`, and
  `simpleWaitOk`, `token_simple_new`/`token_simple_ok` are keyed by the cell's name, `tpShot γy`,
  instead of a mode.)
