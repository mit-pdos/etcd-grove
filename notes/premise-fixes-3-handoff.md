# premise-fixes-3: handoff

Branch `premise-fixes-3` (worktree `/shared/etcd-grove-pf3`, off lean `de9c19e020`), scratch
`/shared/tmp/premise-fixes-3/`. Two trust-boundary defects reaching the closed k8s results
(collections `k8s.txt`, `k8setcd3.txt`), fixes decided by etcd-grove-81.

## Done

1. `Proof/reflect/Values.lean`: the axiom `value_typed_pointsto` (elaborated as
   `{GF} → TypedPointsto reflect.Value`, independent of `hG`) is now an instance,
   `heapTypedPointsto reflect.Value value_intoVal_inj.intoVal_inj`, over a new axiom
   `value_intoVal_inj [reflect.Assumptions] : go.IntoValInj reflect.Value`. Built alone
   (`lake build Proof.reflect.Values`); its type now takes `hG`, `sem` and `reflect.Assumptions`;
   `#print axioms` shows `value_intoVal_inj` and no `value_typed_pointsto`. Net axiom count 0.
   Its importers (210 modules) are not rebuilt yet: the new `[reflect.Assumptions]` binder may need
   adding where a `reflect.Value` points-to is used without it.
2. `examples/premisefix/recordetcdrequest/` (own go.mod, from `examples/k8s/etcd3/go.mod`):
   a typed-nil `*status.Error` makes `metrics.RecordEtcdRequest` panic (nil dereference in
   `GRPCStatus`, via `errorReason` → `status.FromError`); nil, `ErrTransactionConflict`, a status
   error and an `errors.New` leaf return. Passes under go1.27.1 and go1.27.3. Note: gates step 9
   (premise-fixes-1) runs `./premisefix/...` in the examples module, which skips a nested module:
   extend it to run this one.

## Next, in order

1. Fix 2 in Lean:
   - `Spec/.../metrics/RecordEtcdRequest.lean`: add `go_etcd_io.etcd.cache.v3.statusErrOk err` to
     the precondition; docstring cites metrics.go:217-223 (and errorReason, 225-243).
   - `ErrTransactionConflict`: `etc/gen-init.py`'s `SPECIAL[_K3 + '.metrics']` states the init
     axiom as `errorsNewVarInit ErrTransactionConflict.init ErrTransactionConflict "transaction
     conflict"` (the idiom of the other `errors.New` variables, `Proof/errors/NewVar.lean`), and
     `metricsInit` (`storage/etcd3/Base.lean`) becomes `EtcdGrove.errorsNewVar
     ErrTransactionConflict "transaction conflict"`. This restates a trust-boundary axiom: stop.
   - `txnError.spec`: post `statusErrOk err -∗ statusErrOk e` (or `e = err ∨ err = nil ∧ the
     variable's value`), proved from `metricsInit` by `errorString_errLeaf` and
     `statusErrOk_of_leafMsg` (`server/v3/etcdserver/apply/Base.lean`; it needs `ErrorStringLeaf`,
     an instance from `errors.Assumptions`).
   - Call sites (`store__{GetCurrentResourceVersion,getCurrentState}`: the client's err, so case
     on `Hget` before `wp_apply wp_RecordEtcdRequest`, `statusErrOk_nil` in the success branch;
     `store__{Create,updateOnce,deleteOnce}`: through `txnError`).
2. Merge lean (premise-fixes-1), full build, interfaces, `tcb --check --update` (baseline, k8s,
   k8setcd3 and whatever else moves), STATUS entry, decisions.md entry, gates.

## Pitfalls

- Disk: /shared was full on 2026-11-10 (a 28G `.lake/build` seed did not fit; 8 GB free). This
  worktree's `.lake/packages` is a symlink to the main checkout's; always pass
  `--packages=/shared/tmp/manifest-ddc.json`.

## Build

`flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G lake build
--packages=/shared/tmp/manifest-ddc.json`
