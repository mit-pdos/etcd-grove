/-
Proofs of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/restartN/newMember.lean` (restart3 C2/C3,
2026-11-15). Lean-first (no Rocq counterpart).

`newMember.wp_proof`: `net.Listen` at the peer address (registered with the raft protocol,
`http.register`), the swap allocated (`new(sync.Mutex)`, `s.RaftHandler()`, its ghost state from the
member's `httpProcSlots` serving copies, `sw_alloc`, and its mutex, `sync.init_Mutex`), `go
http.Serve(pl, sw)` (the swap's handler contract, `swap_handlerOk`, from `raftSwap.ServeHTTP.spec`),
`s.Start()` (the member built with its peer address served) and the record. As etcdstart's
`NewMember.lean`, with the swap in place of the raft handler.

`restartMember.wp_proof`: `build` (`build.specRestart`) on the record's name, peer URLs and client
address, `m.sw.set(s.RaftHandler())` (the new incarnation's serving copies to the swap,
`raftSwap.set.spec`), `s.Start()`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.newMember
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.build
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.raftSwap
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__RaftHandler
public import Spec.net.Listen
public import Spec.net.ListenHttp
public import Proof.net.http.Axioms
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartStop
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Start

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_restartN

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver
open etcd_restart

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Assumptions]

/-- **A member's peer handler is a handler of its peer address** lending a slot token. -/
theorem swap_handlerOk (wp_ServeHTTP : raftSwap.ServeHTTP.spec (GF := GF) (hG := hG))
    (sw : Loc) (γS : SwNames) (γn : NetNames GF) (a : GoString) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.restartN ∗
      swapOk sw γS γn a ⊢
      http.handlerOk (raftHttpNet (netRh γn)) a (swTok γS)
        (interface.mkOk (go.GoType.PointerType
          github_com.mit_pdos.etcd_grove.examples.etcd.restartN.raftSwap.ty) #sw) := by
  iintro ⟨#Hpkg, #Hsw⟩
  unfold http.handlerOk
  iexists _
  isplitr
  · ipureintro; rfl
  iintro !> %wi %r %R %γk %rd Hra %Hr #Hreq Htk Hbody Hw Hhd %Hfl HRs
  iapply (wp_ServeHTTP sw γS γn a wi r R γk rd) $$ Hpkg Hsw Hra %Hr Hreq Htk Hbody Hw Hhd %Hfl HRs

theorem newMember.wp_proof
    (wp_ListenHttp : net.Listen.specHttp (GF := GF) (hG := hG))
    (wp_RaftHandler : EtcdServer.RaftHandler.spec (GF := GF) (hG := hG))
    (wp_Start : EtcdServer.Start.spec (GF := GF) (hG := hG))
    (wp_ServeHTTP : raftSwap.ServeHTTP.spec (GF := GF) (hG := hG)) :
    newMember.spec (GF := GF) (hG := hG) := by
  intro N s name peerAddr client peer ρ E₀ lg γn id RcB RcN Hown
  wp_start as ⟨Htok, Hmb, #Hpeer, Haddr, Hpown⟩
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  ihave #Ppkg : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.restartN $$ []
  · iPkgInit
  (try wp_auto)
  -- `net.Listen("tcp", peerAddr)`
  ihave #Pnet : isPkgInit (PROP := IProp GF) pkg_id.net $$ []
  · iPkgInit
  wp_apply (wp_ListenHttp go!"tcp" peerAddr) $$ [Haddr] as %lis %lerr Hlis
  · iframe; ipureintro; rfl
  icases Hlis with (⟨%Hlerr, Hlis⟩ | %Hlerr)
  rotate_left
  · cases lerr with
    | nil => exact absurd rfl Hlerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ileft; iframe Htok; ipureintro; simp
  subst Hlerr
  wp_auto
  iunfold etcdstart.memberBuilt at Hmb
  simp only [etcdstart.memberPeerServeRes, Bool.false_eq_true, ↓reduceIte]
  icases Hmb with ⟨%γA, %ci, %TM, %E, %γrn, %b, %cfg, %γk, %τ, %HE, Hstk, #Hwb, Hsb, Hserve, Hsv, #Hoff,
    Hlgm, Hrc, #Hnm, Htokp, HServeR, #Hlr, Hkeep⟩
  -- the listener serves the peer address with the raft protocol
  imod (http.register lis peerAddr (raftProto (netRh γn))) $$ Hlis Hpown with Hlis
  -- `&raftSwap{mu: new(sync.Mutex), h: s.RaftHandler()}`
  wp_apply (wp_RaftHandler s γn id τ peerAddr Hown) as %h #Hh
  · iframe #
  -- the swap's ghost state, from the member's serving copies, and its mutex
  imod sw_alloc γn τ http.httpProcSlots $$ HServeR with ⟨%γS, %c, %b', %Hn, #HG, Hcur, Htoks⟩
  iStructNamed «$r0»
  ipersist mu
  imod (sync.init_Mutex (swLock «$r0_ptr» γS γn peerAddr) ⊤ «$v0_ptr») $$ «$v0» [h Hcur] with #Hlock
  · inext
    iunfold swLock
    iexists h, c, b', τ
    iframe; iframe #
  ihave #Hsw : swapOk «$r0_ptr» γS γn peerAddr $$ []
  · iunfold swapOk
    isplitr
    · ipureintro; exact Hn
    iexists «$v0_ptr»
    iframe #
  -- `go http.Serve(pl, sw)`
  wp_apply wp_fork $$ [Hlis Htoks]
  · wp_apply (http.Serve_ok (raftHttpNet (netRh γn)) lis _ peerAddr (swTok γS)) $$ [Hlis Htoks]
      as %serr -
    · iframe Htoks
      isplitl [Hlis]
      · rw [show (raftHttpNet (netRh γn)).proto peerAddr = raftProto (netRh γn) from rfl]
        iexact Hlis
      iapply swap_handlerOk wp_ServeHTTP
      iframe #
    ipureintro; exact isPanic_intoVal serr
  (try wp_auto)
  -- `s.Start()`, the member built with its peer address served
  wp_apply (etcdstart.wp_Start_built wp_Start s ρ E₀ lg γn id N true
      (ReceiptBoundLe.le (GF := GF) (N + 1)) .none (ReceiptBoundLe.le (GF := GF) (2 ^ 48)))
    $$ [Hstk Hsb Hserve Hsv Hlgm Hrc Htokp Hkeep Htok] as Hup
  · iframe Htok
    iunfold etcdstart.memberBuilt
    iexists γA, ci, TM, E, γrn, b, cfg, γk, τ
    simp only [etcdstart.memberPeerServeRes, ↓reduceIte]
    iframe; iframe #
    ipureintro; exact HE
  -- the record, read-only from here on
  (try wp_auto)
  iapply HΦ
  iright
  isplitr
  · ipureintro; rfl
  iexists γS
  iframe Hup
  iunfold memberRec
  iexists _, peer
  iframe «$r0»
  iframe #

theorem restartMember.wp_proof
    (wp_build : build.specRestart (GF := GF) (hG := hG))
    (wp_RaftHandler : EtcdServer.RaftHandler.spec (GF := GF) (hG := hG))
    (wp_set : raftSwap.set.spec (GF := GF) (hG := hG))
    (wp_Start : EtcdServer.Start.spec (GF := GF) (hG := hG)) :
    restartMember.spec (GF := GF) (hG := hG) := by
  intro N m γS name peerAddr client cluster lg M iu Uok ps bootLog ctxs dir id γ ρ γn
    ThB RcB RcN HwbN hvs hrule hboot hblen Hγn1 Hγn2 Hdirok Hdir Hdirps HU Hpf Hcf Haf Hbuq Hdbo
  wp_start as ⟨#Hzlg, Htok, Hrec, #Hcl, #Hsls, #Hboot, #Hcci, Hrr, #Hnet, #Hrfs, #Hvoff⟩
  iunfold memberRec at Hrec
  icases Hrec with ⟨%sw, %peer, Hm, #Hpeer, #Hsw⟩
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  (try wp_auto)
  -- `build(m.name, m.peer, m.client, cluster, lg)`, on the stopped data directory
  wp_apply (wp_build N name peerAddr client peer cluster lg M iu Uok ps bootLog ctxs dir id γ ρ γn
      HwbN hvs hrule hboot hblen Hγn1 Hγn2 Hdirok Hdir Hdirps HU Hpf Hcf Haf Hbuq Hdbo)
    $$ [Htok Hrr] as %s %err Hres
  · iframe; iframe #
  icases Hres with (⟨%Herr, Htok⟩ | ⟨%Herr, Htok, %ρ', %E₀, %Hρ', Hmb, #Hdd⟩)
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ileft; iframe Htok; ipureintro; simp
  subst Herr
  wp_auto
  iunfold etcdstart.memberBuiltR at Hmb
  simp only [etcdstart.memberPeerServeRes, Bool.false_eq_true, ↓reduceIte]
  icases Hmb with ⟨%γA, %ci, %TM, %E, %γrn, %b, %cfg, %γk, %τ, %at₀, %A, %HE, Hstk, #Hwb, Hsb, Hserve,
    Hsv, #Hoff, Hlgm, Hrc, #Hnm, Htokp, HServeR, Hrest⟩
  -- `m.sw.set(s.RaftHandler())`: the member owns its peer address (the directory's)
  have Hown : (netRh γn).owner peerAddr = id := by
    rw [netRh_owner]
    exact netOwner_of_mem γn.dir (by rw [Hγn2]; exact Hdirok.2.1) id peerAddr
      (by rw [Hγn2]; exact Hdir)
  wp_apply (wp_RaftHandler s γn id τ peerAddr Hown) as %h #Hh
  · iframe #
  wp_apply (wp_set sw γS γn peerAddr h τ) $$ [HServeR]
  · iframe; iframe #
  -- `s.Start()`
  wp_apply (etcdstart.wp_Start_builtR wp_Start s ρ' E₀ lg γn id N true
      (ReceiptBoundLe.le (GF := GF) (N + 1)) (ReceiptBoundLe.le (GF := GF) (2 ^ 48)))
    $$ [Hstk Hsb Hserve Hsv Hlgm Hrc Htokp Hrest Htok] as Hup
  · iframe Htok
    iunfold etcdstart.memberBuiltR
    iexists γA, ci, TM, E, γrn, b, cfg, γk, τ, at₀, A
    simp only [etcdstart.memberPeerServeRes, ↓reduceIte]
    iframe; iframe #
    ipureintro; exact HE
  (try wp_auto)
  iapply HΦ
  iright
  isplitr
  · ipureintro; rfl
  iexists ρ', E₀
  iframe Hup
  ipureintro; exact Hρ'

end proof

end etcd_restartN
end EtcdGrove
end Perennial
