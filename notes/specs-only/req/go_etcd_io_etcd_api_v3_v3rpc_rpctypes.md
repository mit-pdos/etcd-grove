# Requirements on `go.etcd.io/etcd/api/v3/v3rpc/rpctypes` (batch 2a)

## from W0

The client's specs say an error is etcd's error `e` by `err = errVal e` (`api/v3/State.lean`:
`errVal`, opaque, with `errVal_inj` and `errVal_ty`), and classify a call's errors with `callErr err
k` (`client/v3/Api.lean`). What W0 needs of rpctypes:

1. **The package's error variables** (`init.spec` of rpctypes): after initialization each
   `rpctypes.ErrX` holds `errVal .x` (`ErrCompacted` ↦□ `errVal .compacted`, ..., one per
   constructor of `EtcdModel.EtcdErr`), and `errVal e` is the value `Error(ErrGRPCX)` computes
   (`EtcdError{code, desc}`), never written afterwards.
   ```go
   if err == rpctypes.ErrCompacted { ... }          // clients compare with the variables
   err = rpctypes.ErrInvalidSortOption               // kv.Do's own error
   ```
   Used by: `kv.Do.spec` (the invalid-sort refusal), the snippets `clientv3kv/errors.go`,
   `history.go`.

2. **`Error(err)`** over `callErr err k`: `.etcd e` gives `errVal e`; `.notSent` and `.other` give
   `err` itself (their messages are none of `errStringToError`'s keys). **`ErrorDesc(err)`**: the
   status's message (`.notSent`: grpc's two messages).
   Used by: `ContextError.spec`, `isSafeRetryMutableRPC.spec`, `isSafeRetryImmutableRPC.spec`.

3. **The laws** `callErr_errVal` (`⊢ callErr (errVal e) (.etcd e)`) and `callErr_ctxErr` (a context's
   error is `.other`), and `errVal_inj`, `errVal_ty`: obligations of this package's realization
   with grpc's (`req/google_golang_org_grpc.md` item 2).
