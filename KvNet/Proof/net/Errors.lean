-- The copy for the part `KvNet/` of `Net/Proof/net/Errors.lean` (etc/copy-part.py; rerun it, do not edit).
/-
The trusted models' error and address helpers (`Net/TrustedCode/net.lean`: `model.opError`,
`model.kindErr`, `model.sysErr`, `model.epollErr`, `model.anyTCPAddr`), as WP lemmas the proofs of `net`'s specs use:
each gives the error's or the address's predicate of `Base.lean` (`opErr`, `kindErr`, `sysErr`,
`epollErr`, `netAddr`). And `(*OpError).Error()` (`OpError.Error.impl`): a message of Go's form, its
operation, then `": "` (`opErrMsg`, `wp_OpError_Error`).
-/
module

public import KvNet.Proof.net.Base

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

theorem wp_opError (op nw : GoString) (src addr e : GoInterface) (Φ : val → IProp GF) :
    ⌜tcpNet nw⌝ -∗ (∀ err, opErr (GF := GF) op src addr e err -∗ Φ #err) -∗
    WP (App (App (App (App (App (Val model.opError) (Val #op)) (Val #nw)) (Val #src)) (Val #addr))
      (Val #e)) {{ Φ }} := by
  iintro %hnw HΦ
  unfold model.opError
  rw [OpError_ty_eq, Addr_ty_eq']
  iapply wp_fupd
  wp_auto
  ipersist pe
  imodintro
  iapply HΦ
  unfold opErr
  iexists pe_ptr, nw
  isplitr
  · ipureintro; exact ⟨rfl, hnw⟩
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

/-- The bare `Errno` of a failed poller registration (`model.epollErr`): `ENOMEM` or `ENOSPC`. -/
theorem wp_epollErr (Φ : val → IProp GF) :
    (∀ e, ⌜epollErr e⌝ -∗ Φ #e) -∗
    WP (App (Val model.epollErr) (Val #())) {{ Φ }} := by
  iintro HΦ
  unfold model.epollErr
  rw [Errno_ty_eq]
  (try wp_auto)
  wp_bind (ExternalOp _ _ _)
  iapply wp_net_AnyBool
  iintro %b
  cases b
  · wp_auto
    iapply HΦ
    ipureintro; exact .inr rfl
  · wp_auto
    iapply HΦ
    ipureintro; exact .inl rfl

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

/-- D23. The networks the models accept (`model.netOk`): `true` for `"tcp"` and `"tcp4"`. -/
theorem wp_netOk (nw : GoString) (hnw : tcpNet nw) (Φ : val → IProp GF) :
    Φ #true -∗ WP (App (Val model.netOk) (Val #nw)) {{ Φ }} := by
  iintro HΦ
  unfold model.netOk
  rcases hnw with rfl | rfl
  · wp_auto; iexact HΦ
  · wp_auto; iexact HΦ

/-- A new `*TCPConn` for the end `s` of `cn` on the network `nw`, with new addresses. -/
theorem wp_newConn (cn : Nat) (s : Bool) (a nw : GoString) (Φ : val → IProp GF) :
    ⌜tcpNet nw⌝ -∗ netConnAt (extGlobalGS netExt (G := hG.goose_globalGS)) cn a -∗
    (∀ c, isConn (GF := GF) c cn s a -∗ Φ #c) -∗
    WP (App (App (Val model.newConn) (Val #(endId cn s))) (Val #nw)) {{ Φ }} := by
  iintro %hnw #Hat HΦ
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
  isplitr
  · ipureintro; rfl
  iexists nw
  iframe t Hat Hla Hra
  ipureintro; exact hnw

end proof

/-- Go's form of an `*OpError`'s message (`OpError.Error.impl`, `net.go`): the operation `op`,
some string (the network and the addresses), `": "`, some string (the error's message). -/
def opErrMsg (op msg : GoString) : Prop :=
  ∃ s1 s2 : GoString, msg = op ++ s1 ++ go!": " ++ s2

theorem opErrMsg_ne (op msg : GoString) (h : opErrMsg op msg) : msg ≠ [] := by
  obtain ⟨s1, s2, rfl⟩ := h
  simp

section errorMsg
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions]

/-- `e.Error()` on an `*OpError` `pe`: a message of Go's form (`opErrMsg`) for its `Op`. -/
theorem wp_OpError_Error (pe : Loc) (v : net.OpError) (Φ : val → IProp GF) :
    (pe ↦□ v : IProp GF) -∗ ▷ (∀ msg : GoString, ⌜opErrMsg v.Op' msg⌝ -∗ Φ #msg) -∗
    WP (App (Val #(methods (go.GoType.PointerType OpError.ty) go!"Error" #pe)) (Val #()))
      {{ Φ }} := by
  iintro #Hpe HΦ
  ihave %hnn := typedPointsto_not_null _ _ _ $$ Hpe
  ihave #H2 := Hpe
  iStructNamed H2
  wp_method_call
  wp_call
  unfold OpError.Error.impl
  rw [OpError_ty_eq]
  wp_auto
  (try rw [decide_eq_false hnn])
  (try simp only [hnn, ↓reduceIte, decide_false, Bool.false_eq_true])
  wp_auto
  wp_bind (ExternalOp _ _ _)
  iapply wp_net_AnyString
  iintro %s1
  wp_auto
  wp_bind (ExternalOp _ _ _)
  iapply wp_net_AnyString
  iintro %s2
  wp_auto
  iapply HΦ
  ipureintro
  exact ⟨s1, s2, by simp [List.append_assoc]⟩

end errorMsg

end net
end Perennial
