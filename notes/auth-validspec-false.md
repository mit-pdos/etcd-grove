---
title: auth.ValidSpec is false (isValidSimpleToken panics on a nil context)
found: 2026-11-12
by: the etcd_auth_safe Scope (etcd-grove-81's agent), /shared/tmp/auth-safe/scope.md
blocks-proof: yes (for an auth closed theorem)
status: open; fix decided (S1 of the etcd_auth_safe Scope: the token contract's info clause takes a context Done() fact, auth.ctxDoneAny)
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
