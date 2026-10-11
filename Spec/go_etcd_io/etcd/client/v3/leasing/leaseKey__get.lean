/-
`leaseKey.get(op)` (`client/v3/leasing/cache.go`). Lean-first (no Rocq counterpart); see `InvLeaseCache.lean`.
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
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- **`lk.get(op)`** on the `*leaseKey` `lkp` of the entry `e` (read on any fractions): the
cached get's answer to `op` (`getResult`), in a fresh response with a copy of the cached
response's header, `More` and `Count`. -/
abbrev leaseKey.get.spec : Prop :=
  ∀ (lkp : Loc) (e : LeaseEntry) (dq1 dq2 : DFrac) (opv : go_etcd_io.etcd.client.v3.Op) (o : OpFull),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ lkp ↦{dq1} e.lk ∗ respOwn e dq2 ∗ opFullAt opv o }}
    (App (Val (lkp @!! go.GoType.PointerType leaseKey.ty @!! go!"get")) (Val #opv))
  {{ (ret : Loc), RET #ret; lkp ↦{dq1} e.lk ∗ respOwn e dq2 ∗
      freshGetResp ret e.hm e.more e.count (getResult o e) }}

end spec

end leasing
end EtcdGrove
end Perennial
