module
public import Proof.go_etcd_io.bbolt.Init

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `atomicLoadDuration(ptr)`: the `time.Duration` at `ptr`, read atomically (as an `int64`). -/
abbrev atomicLoadDuration.spec : Prop :=
  ∀ (ptr : Loc) (dq : DFrac) (v : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ptr ↦{dq} v }}
    (App (Val #(functions atomicLoadDuration [])) (Val #ptr))
  {{ RET #v; ptr ↦{dq} v }}

end spec

end bbolt
end EtcdGrove
end Perennial
