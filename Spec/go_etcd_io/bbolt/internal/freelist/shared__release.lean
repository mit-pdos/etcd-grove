module
public import Proof.go_etcd_io.bbolt.internal.freelist.Model
public import Proof.go_etcd_io.bbolt.internal.freelist.Iface

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt.internal.freelist

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- `t.release(txid)`: `FLState.release` (up to order). Not proved: it deletes map entries while ranging over the map (allowed in Go, stuck in
the GooseLang map model, whose range body runs under a read of the map). -/
abbrev shared.release.spec : Prop :=
  ∀ (I : FLImpl (GF := GF)) (s : Loc) (σ : FLState) (txid : w64), I.MergeSpansSpec →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ I.hdl s ∗ ownShared s I.iface σ ∗ I.own s σ.free }}
    (App (Val (s @!! go.GoType.PointerType shared.ty @!! go!"release")) (Val #txid))
  {{ (σ' : FLState), RET #(); ⌜σ'.equiv (σ.release txid)⌝ ∗
      ownShared s I.iface σ' ∗ I.own s σ'.free }}

end spec

end bbolt
end EtcdGrove
end Perennial
