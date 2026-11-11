/-
The proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/compactor__runCompactLoop.lean` (K4 of
`notes/k8s-compactor-plan.md`). Lean-first.

The loop runs under `wait.ContextForChannel(stop)`, a context the client takes (`chanCtx_ok`, at
the stop channel's internal names). Its invariant: the next round's `expectVersion` (`0` or
`Seen`) and `rev` (`revOk`), and the client's resources. Each round waits on the timer or the
stop channel (`wp_select_bag_stop`), runs `Compact`, logs a failure (`klog.Errorf`), and records a
compaction (`UpdateCompactRevision`, its `recRevOk`).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.compactor__runCompactLoop
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.Compact
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.compactor__UpdateCompactRevision
public import Spec.k8s_io.apimachinery.pkg.util.wait.ContextForChannel
public import Spec.k8s_io.apimachinery.pkg.util.wait.channelContext__Done
public import Spec.k8s_io.apimachinery.pkg.util.wait.channelContext__Err
public import Spec.k8s_io.utils.clock.RealClock__After
public import Spec.k8s_io.klog.v2.Errorf
public import Spec.go_etcd_io.etcd.client.v3.Client__Endpoints
public import Proof.go_etcd_io.etcd.client.v3.ChanCtx
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.LoopSelect
import all Proof.k8s_io.apiserver.pkg.storage.etcd3.CompactorDefs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [ctxDescs : EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)]
variable [sync_sem : sync.Assumptions]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem compactor.runCompactLoop.wp_proof
    (wp_ContextForChannel : wait.ContextForChannel.spec (GF := GF) (hG := hG))
    (wp_Done : wait.channelContext.Done.spec (GF := GF) (hG := hG))
    (wp_Err : wait.channelContext.Err.spec (GF := GF) (hG := hG))
    (wp_ClockAfter : clock.RealClock.After.spec (GF := GF) (hG := hG))
    (wp_Compact : Compact.spec (GF := GF) (hG := hG))
    (wp_UpdateCompactRevision : compactor.UpdateCompactRevision.spec (GF := GF) (hG := hG))
    (wp_Endpoints : EtcdGrove.Client.Endpoints.spec (GF := GF) (hG := hG))
    (wp_Errorf : klog.Errorf.spec (GF := GF) (hG := hG)) :
    compactor.runCompactLoop.spec (GF := GF) (hG := hG) := by
  intro _ _ c cl ms V γk Seen recorded _ _ γc sc γs hsame hcmp hcret
  wp_start as ⟨#Hc, #Hstop, #Hcl, Hone, Hregs, #Hko, #Hcas⟩
  ihave #Hc' := Hc
  iunfold compactorCore at Hc'
  icases Hc' with ⟨%Hpers, #Hclf, ⟨%iv, #Hiv, %hiv⟩, ⟨%ck, #Hck⟩, #Honc, #Hmu, -⟩
  iunfold compactorChanOk at Hstop
  icases Hstop with ⟨#Hsc, #Hbc⟩
  icases ownBroadcastChan_open _ _ _ _ $$ Hbc with ⟨%γi, #Hint, -⟩
  ihave #Pw : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.wait $$ []
  · iPkgInit
  ihave #Pclk : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.clock $$ []
  · iPkgInit
  ihave #Pklog : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.klog.v2 $$ []
  · iPkgInit
  ihave ⟨#Hctx, #Hce⟩ := chanCtx_ok wp_Done wp_Err EtcdGrove.rpctypesEtcdError_asTarget sc γs γi iprop(True)
    $$ [Pw Hint]
  · iframe #
  (try wp_auto)
  wp_apply wp_ContextForChannel sc
  (try wp_auto)
  ihave HI : iprop(∃ (cv rv cr : w64) (e : GoInterface),
      "compactTime" ∷ compactTime_ptr ↦ cv ∗ "rev" ∷ rev_ptr ↦ rv ∗
      "compactRev" ∷ compactRev_ptr ↦ cr ∗ "err" ∷ err_ptr ↦ e ∗
      "Hcv" ∷ (⌜cv = W64 0⌝ ∨ Seen) ∗ "Hrv" ∷ revOk γk rv ∗
      "Hone" ∷ client.clientWriteOnce cl (ms.map client.SrvAt.addr) ∗
      "Hregs" ∷ ([∗list] x ∈ ms, client.kvRegsAt x))
    $$ [compactTime rev compactRev err Hone Hregs]
  · iexists W64 0, W64 0, W64 0, GoInterface.nil
    iframe
    isplitl []
    · ileft; ipureintro; rfl
    unfold revOk; ileft; ipureintro; rfl
  ihave #Hcl' := Hcl
  iunfold isNewClient at Hcl'
  icases Hcl' with ⟨-, #Hrco, -, -⟩
  ipersist c
  ipersist ctx
  wp_for HI
  (try wp_auto)
  wp_apply (lc := 2) (wp_ClockAfter ck iv) $$ [$Pclk] as %ach %γach #Hbag
  (try wp_auto)
  wp_apply (wp_Done sc) $$ [$Pw]
  (try wp_auto)
  wp_apply_core (wp_select_bag_stop ach γach sc γs iprop(True)) $$ Hbag Hbc [$Hlc1 $Hlc2]
  isplit
  · iintro %t
    (try wp_auto)
    wp_apply (wp_Compact cl ms V γk (chanCtxVal sc) (chanCd γi) Seen recorded cv rv hsame hcmp hcret)
        $$ [$Hone $Hregs $Hcv $Hrv] as %cv' %cr' %crev %err ⟨Hone, Hregs, Hcv, Hrv, #Hrec, %Herr⟩
    · iframe #
    cases err with
    | ok ei =>
      -- a failed round: logged, the next one at the returned version and revision
      (try wp_auto)
      wp_apply wp_Endpoints cl $$ [] as %esl ⟨%eps, Hesl, -⟩
      · iframe #
      (try wp_auto)
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl -
      (try wp_auto)
      wp_apply wp_Errorf _ _ $$ []
      (try wp_auto)
      wp_for_post
      iframe
      iexists cv', cr', crev, GoInterface.ok ei
      iframe
    | nil =>
      -- a round without error: its compaction, if any, recorded
      (try wp_auto)
      wp_if_destruct
      · (try wp_auto)
        wp_for_post
        iframe
        iexists _, _, _, _
        iframe
      · (try wp_auto)
        wp_apply (wp_UpdateCompactRevision c cl γk recorded γc crev) $$ [Hrec] as -
        · iframe #
        (try wp_auto)
        wp_for_post
        iframe
        iexists _, _, _, _
        iframe
  · (try wp_auto)
    wp_for_post
    (try wp_auto)
    iapply HΦ
    itrivial

end proof

end k8s
end EtcdGrove
end Perennial
