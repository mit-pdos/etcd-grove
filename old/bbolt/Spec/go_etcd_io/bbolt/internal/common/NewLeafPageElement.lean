module
public import Proof.go_etcd_io.bbolt.internal.common.Init

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt.internal.common

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- `NewLeafPageElement(flags, pos, ksize, vsize)`: a new leaf element with those fields. -/
abbrev NewLeafPageElement.spec : Prop :=
  ∀ (flags pos ksize vsize : w32),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common }}
    (App (App (App (App (Val #(functions NewLeafPageElement [])) (Val #flags)) (Val #pos))
      (Val #ksize)) (Val #vsize))
  {{ (l : Loc), RET #l; l ↦ leafPageElement.mk flags pos ksize vsize }}

end spec

end bbolt
end EtcdGrove
end Perennial
