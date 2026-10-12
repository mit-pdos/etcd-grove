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

/-- `t.release(txid)`: `FLState.release` (up to order). -/
abbrev shared.release.spec : Prop :=
  ∀ (I : FLImpl (GF := GF)) (s : Loc) (sv : shared) (c : GMap w64 Unit) (σ : FLState) (txid : w64),
  I.MergeSpansSpec →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ I.hdl s ∗ ownSharedC s sv I.iface σ c ∗ ⌜cacheOK c σ ∧ σ.WF⌝ ∗ I.own s σ.free }}
    (App (Val (s @!! go.GoType.PointerType shared.ty @!! go!"release")) (Val #txid))
  {{ (σ' : FLState), RET #(); ⌜σ'.equiv (σ.release txid) ∧ σ'.readonly = σ.readonly⌝ ∗
      ownSharedC s sv I.iface σ' c ∗ ⌜cacheOK c σ' ∧ σ'.WF⌝ ∗ I.own s σ'.free }}

end spec

end bbolt
end EtcdGrove
end Perennial
