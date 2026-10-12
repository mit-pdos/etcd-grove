module
public import Proof.go_etcd_io.bbolt.internal.freelist.Model

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

/-- `t.Count()`: the number of free and pending pages (`FreeCount` called back through the
interface). -/
abbrev shared.Count.spec : Prop :=
  ∀ (I : FLImpl (GF := GF)) (s : Loc) (σ : FLState), I.FreeCountSpec →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownShared s I.iface σ ∗ I.own s σ.free }}
    (App (Val (s @!! go.GoType.PointerType shared.ty @!! go!"Count")) (Val #()))
  {{ RET #(W64 ((σ.free.length + σ.pendingCount : Nat) : Int));
      ownShared s I.iface σ ∗ I.own s σ.free }}

end spec

end bbolt
end EtcdGrove
end Perennial
