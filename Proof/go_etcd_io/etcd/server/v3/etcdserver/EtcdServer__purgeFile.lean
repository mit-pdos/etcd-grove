/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__purgeFile.lean` (wal-link L2, 2026-11-17:
until then an axiom). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__purgeFile
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.purgeFile.wp_proof (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG)) :
    EtcdServer.purgeFile.spec (GF := GF) (hG := hG) := by
  intro s γg
  wp_start as ⟨#Hgok, #Hmw, Htf⟩
  ihave ⟨%ch, #Hchf, #Hstop⟩ := srvGoAttachOk_stopping s γg $$ Hgok
  iunfold srvGoAttachOk at Hgok
  icases Hgok with ⟨%ch', %c, -, -, -, -, -, -, ⟨%l, #Hlgf, #Hlgok⟩, #Hpool, -⟩
  icases (threadTokFrom_succ (GF := GF) 1 (threadBound_gt (GF := GF))).1 $$ Htf with ⟨H1, H2⟩
  wp_auto_lc 1
  imod raftPool_borrowL (srvLgReader s) ⊤ (fun _ _ => CoPset.mem_full) $$ [Hlc1 H1] with ⟨Hlr, Hloan⟩
  · iframe Hlc1 H1; iexact Hpool
  wp_apply hLg s l $$ [Hlr] as ⟨-, Hlr⟩
  · iframe #; iframe Hlr
  iapply fupd_wp
  imod raftLoanL_giveBack (srvLgReader s) ⊤ (fun _ _ => CoPset.mem_full) $$ [Hloan Hlr] with H1
  · iframe
  imodintro
  (try wp_auto)
  wp_apply_core chan.wp_select_blocking_nil
  iapply BigAndL.bigAndL_cons.2
  isplit
  · iright
    iapply (chan.nilClausePre_recv GoInterface (zero_val GoChan) _ rfl)
  iapply BigAndL.bigAndL_cons.2
  isplit
  · ileft
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch, γg.ch
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ownStopChan_is_chan $$ Hstop
    iapply stop_chan_receive ch γg.ch _ _ .Unknown $$ Hstop
    iintro ⟨-, -⟩
    wp_auto
    iapply HΦ
    iapply (threadTokFrom_succ (GF := GF) 1 (threadBound_gt (GF := GF))).2
    iframe
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial
