/-
The trusted models' error and address helpers (`Net/TrustedCode/net.lean`: `model.opError`,
`model.kindErr`, `model.sysErr`, `model.anyTCPAddr`), as WP lemmas the proofs of `net`'s specs use:
each gives the error's or the address's predicate of `Base.lean` (`opErr`, `kindErr`, `sysErr`,
`netAddr`).
-/
module

public import Net.Proof.net.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions] [field_sem : net.FieldAssumptions]
variable [go.BasicIntoValInj]

theorem wp_opError (op : GoString) (src addr e : GoInterface) (Φ : val → IProp GF) :
    (∀ err, opErr (GF := GF) op src addr e err -∗ Φ #err) -∗
    WP (App (App (App (App (Val model.opError) (Val #op)) (Val #src)) (Val #addr)) (Val #e))
      {{ Φ }} := by
  iintro HΦ
  unfold model.opError
  rw [OpError_ty_eq, Addr_ty_eq']
  iapply wp_fupd
  wp_auto
  ipersist pe
  imodintro
  iapply HΦ
  unfold opErr
  iexists pe_ptr
  isplitr
  · ipureintro; rfl
  iexact pe

theorem wp_sysErr (name : GoString) (nm : GoString → Prop) (hnm : nm name) (Φ : val → IProp GF) :
    (∀ e, sysErr (GF := GF) nm e -∗ Φ #e) -∗
    WP (App (Val model.sysErr) (Val #name)) {{ Φ }} := by
  iintro HΦ
  unfold model.sysErr
  rw [Errno_ty_eq]
  (try wp_auto)
  wp_bind (ExternalOp _ _ _)
  iapply wp_net_AnyErrno
  iintro %n %hn
  iapply wp_fupd
  wp_auto
  ipersist p
  imodintro
  iapply HΦ
  unfold sysErr
  iexists p_ptr, name, n
  isplitr
  · ipureintro; exact ⟨rfl, hnm, hn⟩
  iexact p

/-- The `Err` of a failure of kind `k` (its code), `name` the system call's. -/
theorem wp_kindErr (k : NetErr) (ed : Option GoInterface) (name : GoString)
    (nm : GoString → Prop) (hnm : nm name) {c : w64} (hc : c = errCode (some k))
    (Φ : val → IProp GF) :
    (match k, ed with
     | .timeout, some e => iprop(globalAddr internal.poll.ErrDeadlineExceeded ↦□ e)
     | .timeout, none => iprop(False)
     | _, _ => iprop(True)) -∗
    (∀ e, kindErr (GF := GF) k ed nm e -∗ Φ #e) -∗
    WP (App (App (Val model.kindErr) (Val #c)) (Val #name)) {{ Φ }} := by
  subst hc
  iintro Hed HΦ
  unfold model.kindErr
  cases k
  · wp_auto
    unfold model.closedErr
    wp_auto
    iapply HΦ
    unfold kindErr
    ipureintro; rfl
  · cases ed with
    | none => dsimp only; iexfalso; iexact Hed
    | some e =>
      wp_auto
      unfold model.deadlineErr
      wp_auto
      iapply HΦ
      unfold kindErr
      ipureintro; rfl
  · wp_auto
    wp_apply wp_sysErr name nm hnm
    iintro %e He
    iapply HΦ
    unfold kindErr
    iexact He

theorem wp_anyTCPAddr (Φ : val → IProp GF) :
    (∀ x, netAddr (GF := GF) x -∗ Φ #x) -∗
    WP (App (Val model.anyTCPAddr) (Val #())) {{ Φ }} := by
  iintro HΦ
  unfold model.anyTCPAddr
  rw [TCPAddr_ty_eq, IP_ty_eq, Addr_ty_eq']
  (try wp_auto)
  wp_bind (ExternalOp _ _ _)
  iapply wp_net_AnyString
  iintro %z
  wp_apply wp_string_to_bytes z as %sl ⟨-, -⟩
  (try wp_auto)
  wp_bind (ExternalOp _ _ _)
  iapply wp_net_AnyW64
  iintro %port
  (try wp_auto)
  wp_bind (ExternalOp _ _ _)
  iapply wp_net_AnyString
  iintro %ip
  iapply wp_fupd
  wp_auto
  ipersist p
  imodintro
  iapply HΦ
  unfold netAddr
  iexists p_ptr, _
  isplitr
  · ipureintro; rfl
  iexact p

/-- A new `*TCPConn` for the end `s` of `cn`, with new addresses. -/
theorem wp_newConn (cn : Nat) (s : Bool) (a : GoString) (Φ : val → IProp GF) :
    netConnAt (extGlobalGS netExt (G := hG.goose_globalGS)) cn a -∗
    (∀ c, isConn (GF := GF) c cn s a -∗ Φ #c) -∗
    WP (App (Val model.newConn) (Val #(endId cn s))) {{ Φ }} := by
  iintro #Hat HΦ
  unfold model.newConn
  rw [TCPConn_ty_eq, conn_ty_eq', Conn_ty_eq, Addr_ty_eq']
  iapply wp_fupd
  wp_auto
  wp_apply wp_anyTCPAddr as %la #Hla
  (try wp_auto)
  wp_apply wp_anyTCPAddr as %ra #Hra
  (try wp_auto)
  ipersist t
  imodintro
  iapply HΦ
  unfold isConn connAt
  iexists t_ptr, la, ra
  dsimp only
  iframe t Hat Hla Hra
  ipureintro; rfl

end proof

end net
end Perennial
