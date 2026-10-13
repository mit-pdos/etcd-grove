/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__GoAttach.lean`. Lean-first (no
Rocq counterpart); see `InvGoAttach.lean`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__GoAttach
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_uber_org.zap.Logger__Warn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvServer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_uber_org

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.GoAttach.wp_proof
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hW : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    EtcdServer.GoAttach.spec (GF := GF) (hG := hG) := by
  intro s f P
  wp_start as ⟨Hgr, Hlr, HP, Hf⟩
  iunfold srvGoRes at Hgr
  icases Hgr with ⟨Hwr, Htok⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold srvWgReader at Hwr
  icases Hwr with ⟨%γ, #Hok, Hrd⟩
  ihave #Hok' := Hok
  iunfold srvGoAttachOk at Hok'
  icases Hok' with ⟨%ch, %c, #Hch, #Hint, #Hwg, #Hinv, #Hguard, #Hctx, ⟨%l, #Hlg, %Hlgnn⟩, %Hbound⟩
  wp_apply sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hlk, HP0⟩
  ihave #His_ch : isChan ch γ.ch Unit $$ []
  · iunfold isStopChanInternal at Hint; icases Hint with ⟨$, -⟩
  iunfold wgMuP at HP0
  icases HP0 with ⟨%b, Hb, Hs⟩
  cases b
  · -- `stopping` closed: the receive is ready, `f` is dropped
    iunfold stopPart at Hs
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hs with #Hs
    wp_apply_core chan.wp_select_nonblocking_alt [iprop(False)] iprop(True)
      $$ [HΦ Hlk Hb Hlr Htok defer s f] [] []
    · iapply BigSepL2.bigSepL2_singleton.2
      iintro -
      simp only [chan.nonblockingAltClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch, γ.ch
      isplitr
      · ipureintro; rfl
      isplitr
      · iexact His_ch
      iapply stop_chan_nonblocking_receive_done ch γ.ch γ.chi iprop(True) _ _ $$ Hint Hs
      (try wp_auto)
      wp_apply hLg s l $$ [$Hlr] as ⟨%Hl, Hlr⟩
      · iframe #; ipureintro; exact Hlgnn
      (try wp_auto)
      wp_apply hW l _ _ $$ []
      · ipureintro; exact Hl
      (try wp_auto)
      wp_apply sync.RWMutex.wp_RUnlock $$ [$Hlk Hb] as Hrd
      · inext; iunfold wgMuP; iexists false; iframe Hb; iunfold stopPart
        simp only [Bool.false_eq_true, ↓reduceIte]; iexact Hs
      (try wp_auto)
      iapply HΦ
      iframe Hlr
      iunfold srvGoRes
      iframe Htok
      iunfold srvWgReader
      iexists γ
      iframe Hok Hrd
    · iintro Hnr
      icases BigSepL.bigSepL_singleton.1 $$ Hnr with Hf
      iexfalso; iexact Hf
  · -- `stopping` open: not ready; `Add`, `go`
    iunfold stopPart at Hs
    simp only [↓reduceIte]
    wp_apply_core chan.wp_select_nonblocking_alt
      [dghostVar γ.chi.doneGn (DFrac.own sync.rfrac.half) false] iprop(True) $$ [Hs] []
      [HΦ Hlk Hb Hlr Htok defer s f HP Hf]
    · iapply BigSepL2.bigSepL2_singleton.2
      iintro -
      simp only [chan.nonblockingAltClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch, γ.ch
      isplitr
      · ipureintro; rfl
      isplitr
      · iexact His_ch
      iapply stop_chan_nonblocking_receive_open ch γ.ch γ.chi iprop(True) _ _ _ $$ Hint Hs
      iintro Hs
      iframe Hs
    · iintro Hnr
      icases BigSepL.bigSepL_singleton.1 $$ Hnr with Hs
      (try wp_auto)
      wp_apply wp_goAttach_Add s γ sync.rfrac.half Hbound $$ [$Hsync $Hwg $Hinv $Hb $Htok]
        as ⟨Hrun, Hb⟩
      (try wp_auto)
      wp_apply wp_fork_tok_self $$ [Hrun HP Hf s f] as Htok
      · (try wp_auto)
        wp_apply wp_with_defer as %defer' defer'
        (try wp_auto)
        wp_bind (App (Val #f) (Val #()))
        iapply Hf $$ HP
        inext
        iintro -
        (try wp_auto)
        wp_apply wp_goAttach_Done s γ $$ [$Hsync $Hwg $Hinv $Hrun] as Htok
        (try wp_auto)
        iframe Htok
      (try wp_auto)
      wp_apply sync.RWMutex.wp_RUnlock $$ [$Hlk Hb Hs] as Hrd
      · inext; iunfold wgMuP; iexists true; iframe Hb; iunfold stopPart
        simp only [↓reduceIte]; iexact Hs
      (try wp_auto)
      iapply HΦ
      iframe Hlr
      iunfold srvGoRes
      iframe Htok
      iunfold srvWgReader
      iexists γ
      iframe Hok Hrd

end proof

end EtcdGrove
end Perennial
