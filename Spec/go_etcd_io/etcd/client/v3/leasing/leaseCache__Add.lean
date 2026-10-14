/-
`leaseCache.Add(key, resp, op)` (`client/v3/leasing/cache.go`). Lean-first (no Rocq counterpart); see `InvLeaseCache.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeaseCache

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- **`lc.Add(key, resp, op)`** (write lock): the response `resp` (owned: an acquisition's get of
`key`, `e0`'s response, with the entry facts of its revision) becomes `key`'s entry, with a fresh
`*leaseKey` and the closed channel as waiter (`LeaseCacheSt.add`: the old entry is frozen, the
cache's header is updated if newer); returns the cached get's answer to `op` (`getResult`), a
fresh response. The entries map must have been made (`leaseCacheReady`). -/
abbrev leaseCache.Add.spec : Prop :=
  ∀ (lc : Loc) (γ : LeaseCacheNames) (pfx : GoString) (X : LeaseCacheSt → Qp → IProp GF)
    (Qr : LeaseCacheSt → IProp GF) (key : GoString) (e0 : LeaseEntry) (opv : go_etcd_io.etcd.client.v3.Op) (o : OpFull)
    (Q : LeaseCacheSt → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeaseCache lc γ pfx X ∗ lcPeek X Qr ∗ leaseCacheReady γ ∗
      respOwn e0 (DFrac.own 1) ∗ entryFacts pfx key e0 ∗
      ⌜e0.rev = e0.hm.revision ∧ e0.acq = e0.kv⌝ ∗ opFullAt opv o ∗
      (∀ (st : LeaseCacheSt) (li : Loc) (ch : GoChan),
        X st 1 ={⊤}=∗ X (st.add key { e0 with li := li, waitc := ch }) 1 ∗ Q st) }}
    (App (App (App (Val (lc @!! go.GoType.PointerType leaseCache.ty @!! go!"Add")) (Val #key)) (Val #e0.resp)) (Val #opv))
  {{ (ret : Loc), RET #ret; ∃ st : LeaseCacheSt, □ Qr st ∗ Q st ∗
      freshGetResp ret e0.hm e0.more e0.count (getResult o e0) }}

end spec

end leasing
end EtcdGrove
end Perennial
