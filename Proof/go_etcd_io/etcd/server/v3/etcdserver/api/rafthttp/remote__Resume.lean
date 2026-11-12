/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/remote__Resume.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.remote__Resume

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

theorem rafthttp.remote.Resume.wp_proof : rafthttp.remote.Resume.spec (GF := GF) (hG := hG) := by
  intro Rh lid pid R g
  wp_start as #Hg
  iunfold remoteOk at Hg
  icases Hg with ⟨%lg, %ps, %pl, -, -, -, -, -, -, -, -, #Hmu⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock _ (remoteLockInv g) $$ [] as ⟨Hlocked, Hinv⟩
  · iexact Hmu
  iunfold remoteLockInv at Hinv
  icases Hinv with ⟨%b, Hb⟩
  (try wp_auto)
  wp_apply sync.Mutex.wp_Unlock $$ [Hlocked Hb]
  · iframe Hmu Hlocked
    inext; iunfold remoteLockInv; iexists _; iframe
  (try wp_auto)
  iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
