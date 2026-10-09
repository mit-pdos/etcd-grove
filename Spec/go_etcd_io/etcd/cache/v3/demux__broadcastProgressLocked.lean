/-
`demux.broadcastProgressLocked(progressRev)`. Lean-first (no Rocq counterpart); see `InvDemux.lean`.
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

/-- `d.broadcastProgressLocked(progressRev)`, under the write lock, for `progressRev = maxRev`
(non-zero): every active watcher not past it is sent a progress notification and, if the
send succeeded, its next revision becomes `progressRev + 1`. -/
abbrev demux.broadcastProgressLocked.spec : Prop :=
  ∀ (d : Loc) (γd : DemuxNames) (cap : Nat) (C : DemuxCert GF) (c : DemuxCore)
    (regs : GMap Loc RegInfo) (views : GMap Loc View) (progressRev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      demuxLocked d γd cap C c c.stream.length regs views ∗
      ⌜DemuxInv cap c ∧ progressRev = c.maxRev ∧ progressRev ≠ W64 0⌝ }}
    (App (Val (d @!! go.GoType.PointerType demux.ty @!! go!"broadcastProgressLocked")) (Val #progressRev))
  {{ RET #(); ∃ views', demuxLocked d γd cap C c c.stream.length regs views' }}

end spec

end EtcdGrove
end Perennial
