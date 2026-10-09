/-
`newDemux(historyWindowSize, resyncInterval)`. Lean-first (no Rocq counterpart); see `InvDemux.lean`.
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

/-- `newDemux(historyWindowSize, resyncInterval)`: an empty demux (`DemuxCore.init`, no
registrations) with a history of capacity `historyWindowSize`, which must be in
`(0, 2^61]` (`newRingBuffer`'s bound; Go's caller validates it). Returns the persistent
`isDemux` (for any certificate `C` of the caller's choice: the stream starts empty), the
writer's view, and the `RWMutex`'s other tokens. -/
abbrev newDemux.spec : Prop :=
  ∀ (C : DemuxCert GF) (historyWindowSize : w64) (resyncInterval : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      ⌜0 < sint.Z historyWindowSize ∧ sint.Z historyWindowSize ≤ 2 ^ 61⌝ }}
    (App (App (Val (@! newDemux)) (Val #historyWindowSize)) (Val #resyncInterval))
  {{ (d : Loc) (γd : DemuxNames), RET #d;
      isDemux d γd (sint.nat historyWindowSize) C ∗
      demuxWriter d γd (sint.nat historyWindowSize) C DemuxCore.init ∗
      [∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - 1) (),
        demuxHandle d γd (sint.nat historyWindowSize) C }}

end spec

end EtcdGrove
end Perennial
