# `ContextReadErrs` is unsatisfiable: `DeadlineExceeded` as a `SafeMapKey` (found 2026-11-25)

A bug in this repository's own premises (CLAUDE.md, "Issues in the verified code": `notes/`, not
`issues/`). Found by an independent review; Lean evidence below.

## What

`ctxDeadlineLeafW` and `ctxDeadlineLeaf` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/BaseApply.lean`)
say of `context.DeadlineExceeded`'s value `e` both

- `∀ T, e.ty ≠ go.GoType.PointerType T` (true: Go's `deadlineExceededError{}`), and
- `SafeMapKey (GF := GF) go.error (GoInterface.ok e)` at the default `MapKeys GoInterface` instance.

Since Perennial `293bcbdd8` ("maps compare keys with Go's ==", P8c), the only `MapKeys GoInterface`
instance is `mapKeys_interface` (Perennial `Golang/Theory/Map.lean`), whose keys are `nil` or a
pointer, and `SafeMapKey` has the field `key_ok : MapKeys.keyOk k`. A non-pointer, non-nil interface
is therefore never a `SafeMapKey`: the two conjuncts contradict each other. (Before P8c `SafeMapKey`
asked only that comparing the key with itself does not panic, which `deadlineExceededError{}` meets.)

So:

- the premise class `EtcdGrove.ContextReadErrs` (`Proof/.../etcdserver/read/Init.lean`; its field
  `errs : isPkgInit context ⊢ errVarLeafW Canceled ∗ ctxDeadlineLeafW`) gives
  `ContextReadErrs → isPkgInit context ⊢ False`;
- the read package's own fact `readInit` (its `isPkgInit`) holds `ctxDeadlineLeaf`, so
  `isPkgInit read ⊢ False` as well; the only way to build it was from `ContextReadErrs`;
- the top-level premise `Hctx : ∀ hG, ContextReadErrs …` cannot be met, and every closed result
  that takes it (or `[ContextReadErrs]`) is vacuous.

`client.ctxErrTargets` (`Proof/go_etcd_io/etcd/client/v3/InvLessor.lean`) has the same false
conjunct (`SafeMapKey go.error` of `DeadlineExceeded`'s value): it is unsatisfiable, so every result
taking it as a premise is vacuous (`isEtcdLease_of_lessor`, `isEtcdLeaseClient_of_new`,
`client_lessor_isEtcdLease`, `client_new_isEtcdLeaseClient`, `client_lessor_isEtcdLease_served`,
`client_new_isEtcdLeaseClient_served` of `client/v3/Results.lean`; the specs
`lessor.KeepAlive.spec`, `lessor.recvKeepAliveLoop.spec`, `canceledByCaller.spec` take it). Nothing
discharges it: no closed theorem reaches those results.

## Since when

The conjunct was added with the read loop (2026-10-13, `190ad33227`), when it was true; it became
false with the Perennial pin `f73703285` (`ee9054ae66`, 2026-10-26), the first to contain P8c.
`ctxErrTargets` (2026-10-18) likewise.

## Which closed results are vacuous

Every statement taking `Hctx`/`ContextReadErrs` (all premises of the same class):

- the robustness statements `etcd_robust_single_process.spec`
  (`Spec/.../examples/etcd/all/TopLevelRobustness.lean`), `etcd_leaseexpiryN_robust_single_process.spec`
  (`.../etcd/leaseexpiryN/`), `k8s_robust_single_process.spec` (`.../k8s/all/`) and
  `putget_safe.spec` (`.../etcd/dist/putget/`), with their proofs;
- the closed theorems `etcd_safe_single_process` (`etcd/all/Results.lean`),
  `etcd_leaseexpiryN_safe_single_process`, `k8s_safe_single_process`, `k8s_all_Main`,
  `k8setcd3_Main`, `k8setcd3_MainCluster`, `k8setcd3_MainPartition`, `cache_end_to_end_new`
  (`cache/v3/Results.lean`);
- every example `Main.spec` that binds `[ContextReadErrs]`, and so the example results proving them:
  `etcd_all_Main`, `authkv_*` (`etcd/auth/Results.lean`), `auth3_Main`, `authN_Main`,
  `authlease_Main`, `cachekv_Main`, `putgetc_Main`, `compactkv_Main`, `leasekv_Main`, `leaseN_Main`,
  `leasecatchup_Main`, `leaseexpiry_Main`, `leaseexpiryN_Main`, `leasegrant_Main`,
  `linkv3p_Main`, `linkv3p_MainWatch`, `putget_Main`, `putget3_Main`, `putgetN_Main`,
  `linkvtxn_Main`, `txnlinfaultsN_Main`, `watchkv_Main`, `k8s_compactor_Main`,
  `k8s_compactor_MainPartition`.

(The statements that do not take the class, such as `etcd_robust.spec` of `etcd/dist`, the raft
examples', the osfs examples', are not affected.)

## The Lean evidence

Checked against a build of `lean` (Lean's three axioms only), the review's `Chk.lean`/`Chk2.lean`:

```lean
theorem ctxDeadline_pure_false (e : GoInterfaceOk)
    (hty : ∀ T, e.ty ≠ go.GoType.PointerType T)
    (hk : SafeMapKey (GF := GF) go.error (GoInterface.ok e)) : False := by
  have h := hk.key_ok
  rcases h with h | ⟨t, l, h⟩
  · simp [interface.nil] at h
  · obtain ⟨ty, v⟩ := e
    simp [interface.mkOk] at h
    exact hty t h.1

theorem ctxReadErrs_kills [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)] :
    isPkgInit (PROP := IProp GF) pkg_id.context ⊢ False
```

The same review found that the other premise, `Hcec : ContextErrsClient`, is a theorem
(`contextErrsClient_holds [context.Assumptions] [errors.Assumptions]`, from `context.isInit`'s
`"#HCanceledCell"`/`"#HDeadlineExceededTy"` and the method sets goose emits).

## The fix

Branch `ctx-leaf-fix/2026-11-25`: drop the false conjuncts, prove the rest of `ContextReadErrs`
from Perennial's `context.isInit`, and remove `Hctx`/`Hcec` from the statements (see `STATUS.md`).
Where `togRPCError` needs `DeadlineExceeded` as a key of its `map[error]error`, it gets it under a
`MapKeys` instance of its own that admits it (as `v3rpc.streamKeys` does for the leader monitor).

A sibling finding of the same review: [bcrypt-invalidcost-false.md](bcrypt-invalidcost-false.md).
