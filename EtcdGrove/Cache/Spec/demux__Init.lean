/-
`demux.Init(minRev)`. Lean-first (no Rocq counterpart); see `InvDemux.lean`.
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

/-- `d.Init(minRev)`, by the writer: the state becomes `(initCore c minRev).1` (the code's four
cases; a purge stops every watcher, whose registrants then find it closed). -/
abbrev demux.Init.spec : Prop :=
  ∀ (d : Loc) (γd : DemuxNames) (cap : Nat) (c : DemuxCore) (minRev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isDemux d γd cap ∗ demuxWriter d γd cap c }}
    (App (Val (d @!! go.GoType.PointerType demux.ty @!! go!"Init")) (Val #minRev))
  {{ RET #(); demuxWriter d γd cap (initCore c minRev).1 }}

end spec

end EtcdGrove
end Perennial
