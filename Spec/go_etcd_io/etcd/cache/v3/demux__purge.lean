/-
`demux.purge()`. Lean-first (no Rocq counterpart); see `InvDemux.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvDemux

@[expose] public section

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

/-- `d.purge()`, under the write lock: the state reset (`DemuxCore.init`), the history emptied,
every mapped watcher stopped (its view closed, frozen) and both maps replaced by empty ones. -/
abbrev demux.purge.spec : Prop :=
  ∀ (d : Loc) (γd : DemuxNames) (cap : Nat) (c : DemuxCore)
    (regs : GMap Loc RegInfo) (views : GMap Loc View),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      demuxLocked d γd cap c c.stream.length regs views ∗ ⌜DemuxInv cap c⌝ }}
    (App (Val (d @!! go.GoType.PointerType demux.ty @!! go!"purge")) (Val #()))
  {{ RET #(); ∃ views', demuxLocked d γd cap DemuxCore.init 0 regs views' }}

end spec

end EtcdGrove
end Perennial
