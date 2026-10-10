/-
`NewKV(cl, pfx, opts...)` (`client/v3/leasing/kv.go`). Lean-first (no Rocq counterpart); see `InvLeasingKV.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingKV

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- **`NewKV(cl, pfx, opts...)`**, for a client of etcd (`isLeasingEtcdClient`: its `KV`'s gets,
`Do`s and transactions over the whole keyspace, its watcher and leases, a session client whose
session options `opts` give a cancelable context; its own context cancelable), a non-empty
prefix, and fewer than `2^31 - 2` live threads: the `KV` interface value of a leasing KV
(`isLeasingKV`) with its handles, the close function (`lkv.Close`, `leasingCloseFn`), and
`waitSession`'s error (`newKVResult`); the session monitor and `clearOldRevokes` running. It takes
`closedChInit`, the package's ghost fact that `closedCh` is closed (`init` closes it; as the cache's
`New` takes `context.isClosedchanInit`). -/
abbrev NewKV.spec : Prop :=
  ∀ (cl : Loc) (pfx : GoString) (osl : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ closedChInit ∗ isLeasingEtcdClient cl osl ∗
      ⌜pfx ≠ [] ∧ threadBound GF + leasingWgOwedMax ≤ 2 ^ 31⌝ }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.v3.leasing.NewKV)) (Val #cl)) (Val #pfx)) (Val #osl))
  {{ (kv : GoInterface) (cf : GoFunc) (err : GoInterface), RET (PairV (PairV #kv #cf) #err);
      newKVResult pfx kv cf err }}

end spec

end leasing
end EtcdGrove
end Perennial
