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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- **`NewKV(cl, pfx, opts...)`**, for a client of etcd (`isLeasingEtcdClient`: its `KV`'s gets,
`Do`s and transactions over the whole keyspace, its watcher and leases, a session client whose
session options `opts` give a cancelable context; its own context cancelable), a non-empty prefix,
and fewer than `2^31 - 2` live threads: the `KV` interface value of a leasing KV (`isLeasingKV`)
with its handles, the close function (`lkv.Close`, `leasingCloseFn`), and `waitSession`'s error
(`newKVResult`); the session monitor and `clearOldRevokes` running. It takes `closedChInit`, the
package's ghost fact that `closedCh` is closed (`init` closes it; as the cache's `New` takes
`context.isClosedchanInit`). The prefix is at most `2 ^ 26` bytes, kept in `isLeasingKV` (leasing's
own requests carry it with the user's key; 2026-10-30, `notes/decisions.md`, "Leasing's sizes"). -/
abbrev NewKV.spec : Prop :=
  ∀ (cl : Loc) (pfx : GoString) (osl : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ closedChInit ∗ isLeasingEtcdClient cl osl ∗
      ⌜pfx ≠ [] ∧ pfx.length ≤ 2 ^ 26 ∧ threadBound GF + leasingWgOwedMax ≤ 2 ^ 31⌝ }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.v3.leasing.NewKV)) (Val #cl)) (Val #pfx)) (Val #osl))
  {{ (kv : GoInterface) (cf : GoFunc) (err : GoInterface), RET (PairV (PairV #kv #cf) #err);
      newKVResult pfx kv cf err }}

end spec

end leasing
end EtcdGrove
end Perennial
