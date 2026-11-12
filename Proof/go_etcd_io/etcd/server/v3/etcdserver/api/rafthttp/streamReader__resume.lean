/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/streamReader__resume.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamReader__resume


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

theorem rafthttp.streamReader.resume.wp_proof :
    rafthttp.streamReader.resume.spec (GF := GF) (hG := hG) := by
  intro Rh lid pid γd cr
  wp_start as #Hf
  iunfold srFixed at Hf
  icases Hf with ⟨%lg, %tr, %ps, %rc, %pc, %γr, %γp, %ctx, %cd, -, -, -, -, -, -, -, -, -, -, -,
    #Hmu, -, -⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  wp_apply sync.Mutex.wp_Lock _ (srLockInv cr) $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iunfold srLockInv at Hinv
  icases Hinv with ⟨%p, %c, Hp, Hc, Hcor⟩
  wp_auto
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hp Hc Hcor]
  · inext
    iunfold srLockInv
    iexists _, _
    iframe
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
