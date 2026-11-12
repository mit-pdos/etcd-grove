/-
Proof of the spec of the same name: `WatchStream.Chan.contract` at `*watchStream` (stage 2 of the
mvcc API, 2026-11-05). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchStream__Chan
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import all Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.StreamHandle

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.watchStream.Chan.wp_proof : mvcc.watchStream.Chan.spec (GF := GF) (hG := hG) := by
  intro w γ ι
  wp_start as Hws
  icases mvcc.api.isMvccWatchStream_open w γ ι $$ Hws with
    ⟨%γw, %γc, %s, %st, %γo, %hι, #Hinv, #Hws, #Htp, #Hrp, #Hpf⟩
  obtain ⟨hι, hγ⟩ := hι
  iunfold mvcc.isWatchStreamAt at Hws
  iNamed Hws
  wp_auto
  iapply HΦ
  ipureintro
  unfold mvcc.api.wsChanOf
  rfl

end proof

end EtcdGrove
end Perennial
