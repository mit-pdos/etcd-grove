/-
The UDP models' helpers (`Net/TrustedCode/net.lean`, section "UDP": `model.udpSysErr`,
`model.udpKindErr`, `model.anyUDPAddr`, `model.udpDest`, `model.udpErr`), as WP lemmas the proofs of
`net`'s UDP specs use, over the UDP extension alone (`HasExt udpExt`): each gives the error's or the
address's predicate of `UdpBase.lean` (`sysErr`, `udpErr`), or the extension's argument.
-/
module

public import Net.Proof.net.UdpBase

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

/-- `model.udpSysErr name`: an `*os.SyscallError` around an arbitrary nonzero `Errno`. -/
theorem wp_udpSysErr (name : GoString) (Φ : val → IProp GF) :
    (∀ e, sysErr (GF := GF) (fun _ => True) e -∗ Φ #e) -∗
    WP (App (Val model.udpSysErr) (Val #name)) {{ Φ }} := by
  iintro HΦ
  unfold model.udpSysErr
  rw [udp_Errno_ty_eq]
  (try wp_auto)
  wp_bind (ExternalOp _ _ _)
  iapply wp_udp_AnyErrno
  iintro %n %hn
  iapply wp_fupd
  wp_auto
  ipersist p
  imodintro
  iapply HΦ
  unfold sysErr
  iexists p_ptr, name, n
  isplitr
  · ipureintro; exact ⟨rfl, trivial, hn⟩
  iexact p

/-- `model.udpKindErr code name`: the `Err` of a UDP failure, an `*os.SyscallError`. -/
theorem wp_udpKindErr (code : w64) (name : GoString) (Φ : val → IProp GF) :
    (∀ e, sysErr (GF := GF) (fun _ => True) e -∗ Φ #e) -∗
    WP (App (App (Val model.udpKindErr) (Val #code)) (Val #name)) {{ Φ }} := by
  iintro HΦ
  unfold model.udpKindErr
  (try wp_auto)
  wp_apply wp_udpSysErr name
  iexact HΦ

/-- `model.opError op "udp4" src addr e`, `e` an `*os.SyscallError`: a new `*OpError` (`udpErr`). -/
theorem wp_udpOpError (op : GoString) (src addr e : GoInterface) (Φ : val → IProp GF) :
    sysErr (GF := GF) (fun _ => True) e -∗ (∀ err, udpErr (GF := GF) op src addr err -∗ Φ #err) -∗
    WP (App (App (App (App (App (Val model.opError) (Val #op)) (Val #(go!"udp4"))) (Val #src))
      (Val #addr)) (Val #e)) {{ Φ }} := by
  iintro #He HΦ
  unfold model.opError
  rw [udp_OpError_ty_eq, udp_Addr_ty_eq]
  iapply wp_fupd
  wp_auto
  ipersist pe
  imodintro
  iapply HΦ
  unfold udpErr
  iexists pe_ptr, e
  isplitr
  · ipureintro; rfl
  iframe pe He

/-- `model.opError "listen" "udp4" src addr e`, `e` an `*os.SyscallError` or a bare nonzero `Errno`:
a new `*OpError` (`udpListenErr`). -/
theorem wp_udpListenOpError (src addr e : GoInterface) (Φ : val → IProp GF) :
    (sysErr (GF := GF) (fun _ => True) e ∨ ⌜∃ n : w64, n ≠ 0 ∧ e = interface.mkOk syscall.Errno.ty #n⌝) -∗
    (∀ err, udpListenErr (GF := GF) src addr err -∗ Φ #err) -∗
    WP (App (App (App (App (App (Val model.opError) (Val #(go!"listen"))) (Val #(go!"udp4")))
      (Val #src)) (Val #addr)) (Val #e)) {{ Φ }} := by
  iintro #He HΦ
  unfold model.opError
  rw [udp_OpError_ty_eq, udp_Addr_ty_eq]
  iapply wp_fupd
  wp_auto
  ipersist pe
  imodintro
  iapply HΦ
  unfold udpListenErr
  iexists pe_ptr, e
  isplitr
  · ipureintro; rfl
  iframe pe He

/-- `model.anyUDPAddr #()`: a new `*UDPAddr` with arbitrary fields, read-only. -/
theorem wp_anyUDPAddr (Φ : val → IProp GF) :
    (∀ p : Loc, (∃ v : UDPAddr, p ↦□ v) -∗ Φ #p) -∗
    WP (App (Val model.anyUDPAddr) (Val #())) {{ Φ }} := by
  iintro HΦ
  unfold model.anyUDPAddr
  rw [UDPAddr_ty_eq, udp_IP_ty_eq]
  (try wp_auto)
  wp_bind (ExternalOp _ _ _)
  iapply wp_udp_AnyString
  iintro %ip
  wp_apply wp_string_to_bytes ip as %sl ⟨-, -⟩
  (try wp_auto)
  wp_bind (ExternalOp _ _ _)
  iapply wp_udp_AnyW64
  iintro %port
  (try wp_auto)
  wp_bind (ExternalOp _ _ _)
  iapply wp_udp_AnyString
  iintro %z
  iapply wp_fupd
  wp_auto
  ipersist p
  imodintro
  iapply HΦ
  iexists _
  iexact p

/-- `model.udpDest p`: the `IP` (as bytes) and `Port` of the `*UDPAddr` `p`. -/
theorem wp_udpDest (p : Loc) (ip : List w8) (port : w64) (Φ : val → IProp GF) :
    udpAddrAt (GF := GF) p ip port -∗ Φ (PairV (#ip) (#port)) -∗
    WP (App (Val model.udpDest) (Val #p)) {{ Φ }} := by
  iintro #Hp HΦ
  unfold udpAddrAt
  icases Hp with ⟨%sl, %z, #Hp, #Hsl⟩
  unfold model.udpDest
  rw [UDPAddr_ty_eq, udp_IP_ty_eq]
  ihave #Hp2 := Hp
  iStructNamed Hp2
  (try wp_auto)
  wp_apply wp_bytes_to_string sl ip _ $$ Hsl as -
  (try wp_auto)
  iexact HΦ

/-- `model.udpErr op c addr code name` on the `*UDPConn` `c` (network `"udp4"`, local address
`la`): a new `*OpError` (`udpErr`) with `Source` `la`. -/
theorem wp_udpErr (op : GoString) (c : Loc) (s : w64) (la addr : GoInterface) (code : w64)
    (name : GoString) (Φ : val → IProp GF) :
    (c ↦□ (UDPConn.mk s la go!"udp4") : IProp GF) -∗
    (∀ err, udpErr (GF := GF) op la addr err -∗ Φ #err) -∗
    WP (App (App (App (App (App (Val model.udpErr) (Val #op)) (Val #c)) (Val #addr)) (Val #code))
      (Val #name)) {{ Φ }} := by
  iintro #Hc HΦ
  ihave #Hc2 := Hc
  iStructNamed Hc2
  unfold model.udpErr
  rw [UDPConn_ty_eq, udp_Addr_ty_eq]
  (try wp_auto)
  wp_apply wp_udpKindErr code name
  iintro %e #He
  (try wp_auto)
  wp_apply wp_udpOpError op la addr e $$ He
  iexact HΦ

end proof

end net
end Perennial
