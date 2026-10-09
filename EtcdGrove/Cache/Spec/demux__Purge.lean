/-
`demux.Purge()`. Lean-first (no Rocq counterpart); see `InvDemux.lean`.
-/
import EtcdGrove.Cache.InvDemux

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `d.Purge()`, by the writer: every watcher stopped, the state reset (`DemuxCore.init`). -/
abbrev demux.Purge.spec : Prop :=
  ∀ (d : Loc) (γd : DemuxNames) (cap : Nat) (c : DemuxCore),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isDemux d γd cap ∗ demuxWriter d γd cap c }}
    (App (Val (d @!! go.GoType.PointerType demux.ty @!! go!"Purge")) (Val #()))
  {{ RET #(); demuxWriter d γd cap DemuxCore.init }}

end spec

end EtcdGrove
end Perennial
