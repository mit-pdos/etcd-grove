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

/-- `t.releaseRange(begin, end)`: `FLState.releaseRange` (up to order). Not proved: it deletes map entries while ranging over the map (allowed in Go, stuck in
the GooseLang map model, whose range body runs under a read of the map). -/
abbrev shared.releaseRange.spec : Prop :=
  ∀ (I : FLImpl (GF := GF)) (s : Loc) (σ : FLState) (b e : w64), I.MergeSpansSpec →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ I.hdl s ∗ ownShared s I.iface σ ∗ I.own s σ.free }}
    (App (App (Val (s @!! go.GoType.PointerType shared.ty @!! go!"releaseRange")) (Val #b)) (Val #e))
  {{ (σ' : FLState), RET #(); ⌜σ'.equiv (σ.releaseRange b e)⌝ ∗
      ownShared s I.iface σ' ∗ I.own s σ'.free }}

end spec

end bbolt
end EtcdGrove
end Perennial
