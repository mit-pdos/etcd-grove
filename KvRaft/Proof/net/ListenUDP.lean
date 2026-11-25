-- The copy for the part `KvRaft/` of `Net/Proof/net/ListenUDP.lean` (etc/copy-part.py; rerun it, do not edit).
/-
The proof of `Net/Spec/net/ListenUDP.lean`: `ListenUDP.impl`'s extension `Listen`
(`Udp.wp_udp_Listen`), then a new `*UDPConn` holding the socket's id.
-/
module

public import KvRaft.Spec.net.ListenUDP
public import KvRaft.Proof.net.UdpModels

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Udp

namespace net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt udpExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions] [field_sem : net.UdpFieldAssumptions]
variable [go.BasicIntoValInj]

theorem ListenUDP.wp_proof : ListenUDP.spec (GF := GF) (hG := hG) := by
  intro p ip port a
  wp_start as ⟨#Hp, %Hv⟩
  ihave %Hnn : ⌜p ≠ null⌝ $$ [Hp]
  · unfold udpAddrAt
    icases Hp with ⟨%sl, %z, #Hpt, -⟩
    iapply typedPointsto_not_null _ _ _ $$ Hpt
  rw [UDPAddr_ty_eq, UDPConn_ty_eq]
  (try wp_auto)
  (try rw [decide_eq_false Hnn])
  (try simp only [Hnn, ↓reduceIte, decide_false, Bool.false_eq_true])
  (try wp_auto)
  wp_apply wp_udpDest p ip port $$ Hp
  wp_bind (ExternalOp _ _ _)
  iapply wp_udp_Listen ip port a $$ %Hv
  isplit
  · -- a failure: the `Err` an `*os.SyscallError` or a bare `Errno`
    unfold failV
    wp_auto
    wp_bind (ExternalOp _ _ _)
    iapply wp_udp_AnyBool
    iintro %bb
    cases bb
    · wp_auto
      wp_bind (ExternalOp _ _ _)
      iapply wp_udp_AnyString
      iintro %nm
      wp_apply wp_udpKindErr _ nm
      iintro %e #He
      (try wp_auto)
      (try rw [udp_Addr_ty_eq])
      (try wp_auto)
      wp_apply wp_udpListenOpError _ _ e $$ [He]
      · ileft; iexact He
      iintro %err #Herr
      (try wp_auto)
      iapply HΦ
      iright
      isplitr
      · ipureintro; rfl
      iexact Herr
    · wp_auto
      wp_bind (ExternalOp _ _ _)
      iapply wp_udp_AnyErrno
      iintro %n %hn
      rw [udp_Errno_ty_eq, udp_Addr_ty_eq]
      (try wp_auto)
      wp_apply wp_udpListenOpError _ _ (interface.mkOk syscall.Errno.ty #n) $$ []
      · iright; ipureintro; exact ⟨n, hn, rfl⟩
      iintro %err #Herr
      (try wp_auto)
      iapply HΦ
      iright
      isplitr
      · ipureintro; rfl
      iexact Herr
  · -- a new socket
    iintro %s %hs0 #Hs
    wp_auto
    wp_apply wp_anyUDPAddr
    iintro %la #Hla
    (try rw [udp_Addr_ty_eq])
    iapply wp_fupd
    wp_auto
    ipersist c
    imodintro
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists s
    unfold udpConnAt
    iexists _
    dsimp only
    iframe c Hs
    isplitr
    · unfold udpAddr
      icases Hla with ⟨%v, #Hv⟩
      iexists la, v
      iframe Hv
      ipureintro; rfl
    ipureintro; exact hs0

end proof

end net
end Perennial
