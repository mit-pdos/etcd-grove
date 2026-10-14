/-
`evalCmp(resp, tcmp)` (`client/v3/leasing/util.go`). Lean-first (no Rocq counterpart); see `InvLeaseCache.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeaseEval

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

/-- **`evalCmp(resp, tcmp)`** on the entry `e`'s response (read on any fraction): `evalCmp`'s
comparison of its cached key-value (`leaseCmpHolds`, not etcd's `cmpHolds`: see
`InvLeaseEval.lean`). -/
abbrev evalCmp.spec : Prop :=
  ∀ (e : LeaseEntry) (dq : DFrac) (c : go_etcd_io.etcd.client.v3.Cmp) (m : CmpModel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ respOwn e dq ∗ cmpSetAt c m }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.leasing.evalCmp)) (Val #e.resp)) (Val #c))
  {{ RET #(leaseCmpHolds m e.kv); respOwn e dq }}

end spec

end leasing
end EtcdGrove
end Perennial
