/-
`clientv3.Op.MinCreateRev()` (`client/v3/op.go`, translated for the cache). Lean-first (no Rocq
counterpart); see `InvCache.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvCache

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `op.MinCreateRev()` (called through a pointer, as the cache does): the minimum create revision, `o.minCreateRev`. A read, on
any fraction. -/
abbrev Op.MinCreateRev.spec : Prop :=
  ∀ (opp : Loc) (op : go_etcd_io.etcd.client.v3.Op) (o : OpModel) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ opp ↦{dq} op ∗ opAt op o }}
    (App (Val (opp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Op.ty @!! go!"MinCreateRev")) (Val #()))
  {{ RET #(o.minCreateRev); opp ↦{dq} op }}

end spec

end EtcdGrove
end Perennial
