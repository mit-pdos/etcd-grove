/-
`clientv3.NewOp()` (`client/v3/op.go`, translated for the cache). Lean-first (no Rocq
counterpart); see `InvOp.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvOp

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
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `NewOp()`: a fresh `&Op{key: []byte("")}`, modelled by `OpFull.newOp`. -/
abbrev NewOp.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (Val (@! go_etcd_io.etcd.client.v3.NewOp)) (Val #()))
  {{ (opp : Loc) (op : go_etcd_io.etcd.client.v3.Op), RET #opp; opp ↦ op ∗ opFullAt op OpFull.newOp }}

end spec

end EtcdGrove
end Perennial
