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

/-- `atomicAddDuration(ptr, du)`: adds `du` to the `time.Duration` at `ptr` atomically and
returns the sum. -/
abbrev atomicAddDuration.spec : Prop :=
  ∀ (ptr : Loc) (v du : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ptr ↦ v }}
    (App (App (Val #(functions atomicAddDuration [])) (Val #ptr)) (Val #du))
  {{ RET #(v + du); ptr ↦ (v + du) }}

end spec

end bbolt
end EtcdGrove
end Perennial
