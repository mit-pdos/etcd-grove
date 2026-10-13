/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/read/NewRead.lean`. Lean-first (no Rocq
counterpart); the request path's unit 4a.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.read.NewRead
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.read.newNotifier
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.read.Read__LinearizableReadNotify

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.read

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.read.Assumptions]

theorem read.NewRead.wp_proof
    (hNN : read.newNotifier.spec (GF := GF) (hG := hG))
    (hNotify : read.Read.LinearizableReadNotify.spec (GF := GF) (hG := hG)) :
    read.NewRead.spec (GF := GF) (hG := hG) := by
  intro srv rf γr RQ LR NR x
  wp_start as ⟨#Hsrv, #Hraft, #Hcci, Hgx⟩
  wp_auto
  wp_apply chan.wp_make2 (V := Unit) (W64 1) as %wc %γw ⟨#Hwc, -, Hwo⟩
  · ipureintro; word
  ihave #Hwc' := Hwc
  imod start_bag (V := Unit) (fun _ => iprop(True)) _ wc γw (by trivial) $$ Hwc' Hwo with #Hbag
  wp_apply hNN γr as %nc ⟨%γn, #Hnis, Hown, Hauth⟩
  wp_alloc r as Hr
  iStructNamed Hr
  ipersist server
  ipersist raft
  ipersist waitC
  imod ghostVar_update (nc, γn) γr.notifier x $$ Hgx with Hg
  icases (read_ghostVar_halves γr.notifier (nc, γn)).1 $$ Hg with ⟨Hg1, Hg2⟩
  imod monoNatLbOwn_0 γr.committed with #H0
  ihave #Hc0 : committedAtLeast (GF := GF) γr (W64 0) $$ []
  · iunfold committedAtLeast; rw [show uint.nat (W64 0) = 0 by word]; iexact H0
  imod inv_alloc readInvN ⊤ iprop(∃ (nc : Loc) (γn : GName) (n : w64),
      ghostVar γr.notifier (1 : Qp).half (nc, γn) ∗ notifierIs nc γn γr ∗ notifierOwn nc γn γr ∗
      monoNatAuthOwn γn 1 (uint.nat n) ∗ committedAtLeast γr n) $$ [Hg2 Hown Hauth] with #Hinv
  · inext; iexists nc, γn, (W64 0); iframe Hg2 Hnis Hown Hc0
    rw [show uint.nat (W64 0) = 0 by word]; iexact Hauth
  imod sync.init_RWMutex (readMuP r γr) (readMuAddr r) $$ [notifier Hg1] mux with Hslots
  · inext; iunfold readMuP; iexists nc, γn; iframe notifier Hg1
  icases read_guard_of_slots _ _ $$ Hslots with ⟨Hslots, #Hguard⟩
  ihave #Hrd : readInv (GF := GF) γr $$ []
  · iunfold readInv; iexact Hinv
  ihave #Hpre : isReadPre (GF := GF) r γr $$ []
  · iunfold isReadPre
    iexists srv, wc, γw
    iframe server waitC Hbag Hrd
    iunfold isReadServer at Hsrv
    icases Hsrv with ⟨#Hd, -⟩
    iexact Hd
  wp_auto
  iapply HΦ
  isplitr
  · iunfold isRead
    iintro !> %ctx %cd %c %Φ' !> ⟨#Hctx, #Hc, Hrr⟩ HΦ'
    iapply hNotify r γr ctx cd c $$ [Hrr] HΦ'
    iframe #; iframe Hrr
  isplitr
  · iunfold isReadLoopPre
    iexists srv, rf, wc, γw
    iframe #
  rw [show readReader (GF := GF) r γr = sync.ownRWMutex (readMuAddr r) (readMuP r γr) from rfl]
  iexact Hslots

end proof

end EtcdGrove
end Perennial
