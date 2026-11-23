/-
Proof of `Spec/go_etcd_io/etcd/client/v3/contextErrToGRPCErr.lean` (prove-ps2-wrb, 2026-11-22), over
`errors.Is` (Perennial's, for the pointer target `context.Canceled`; `errors.IsDeadlineExceeded` for
`context.DeadlineExceeded`, an empty struct) and grpc's `status.Error`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.contextErrToGRPCErr
public import Spec.errors.Is
public import Spec.errors.IsDeadlineExceeded
public import Spec.google_golang_org.grpc.status.Error
public import Proof.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Init

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (statusErrOk errCellOk errorMsgIs ctxErrMsg ctxErrShape descIs)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

set_option hygiene false in
/-- The tail of each case: `return status.Error(c, err.Error())`, `c ≠ OK`. -/
local macro "cetg_tail" : tactic => `(tactic| (
  (try wp_auto)
  wp_apply Hmt
  wp_apply wp_status_Error as %e1 ⟨%He1, #He1s, #Hd, %He1ty, -⟩
  · iframe #
    ipureintro
    simp only [google_golang_org.grpc.codes.OK]
    exact fun h => absurd (go.intoVal_inj h) (by decide)
  obtain ⟨e1o, rfl⟩ : ∃ e1o, e1 = GoInterface.ok e1o := by
    cases e1 with
    | nil => exact absurd rfl He1
    | ok e => exact ⟨e, rfl⟩
  ihave #He1s' := He1s
  iunfold statusErrOk at He1s'
  ihave ⟨-, %Hl1, -, -⟩ := He1s' $$ %e1o %rfl
  (try wp_auto)
  iapply HΦ
  isplitl []
  · unfold clientErrOk
    isplitl []
    · ipureintro; intro _
      exact clientErr_statusError e1o Hl1 (He1ty e1o rfl) EtcdGrove.rpctypesEtcdError_asTarget
    isplitl []
    · iexact He1s
    iapply go_etcd_io.etcd.cache.v3.errCellOk_of_ty
    rw [He1ty e1o rfl]
    unfold google_golang_org.grpc.internal.status.Error.ty _root_.Perennial.errors.errorString.ty
    simp
  isplitl []
  · unfold notHandlerErr go_etcd_io.etcd.cache.v3.notDescIn
    isplitl []
    · ipureintro; exact He1
    iexists m
    iframe Hd
    ipureintro; exact ctxErrMsg_not_handler hm
  iexists e, m
  iframe Hm Hd
  ipureintro; exact ⟨rfl, hm⟩))

set_option maxHeartbeats 0 in
theorem contextErrToGRPCErr.wp_proof
    (wp_IsDE : errors.IsDeadlineExceeded.spec (GF := GF) (hG := hG))
    (wp_Is : errors.Is.spec (GF := GF) (hG := hG))
    (wp_status_Error : status.Error.spec (GF := GF) (hG := hG)) :
    contextErrToGRPCErr.spec (GF := GF) (hG := hG) := by
  intro err
  wp_start as #Hl
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Perr : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  ihave #Pst : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.status $$ []
  · iPkgInit
  ihave Hci : (_root_.Perennial.context.isInit : IProp GF) $$ []
  · iapply _root_.Perennial.context.isInit_access $$ Pctx
  iNamed Hci
  icases HCanceledCell with ⟨%xc, #Hxc, -⟩
  ihave #Hl' := Hl
  iunfold ctxErrLeaf at Hl'
  icases Hl' with ⟨%e, %m, %Hem, #Hm⟩
  obtain ⟨rfl, hm, hsh, hleaf, hptr, hde⟩ := Hem
  ihave #Hmt : iprop({{ True }} (App (Val #(methods e.ty go!"Error" e.v)) (Val #()))
      {{ RET #m; True }}) $$ []
  · iintro !> %Φ - HΦ
    iunfold errorMsgIs at Hm
    iapply Hm
    inext
    iapply HΦ
    itrivial
  -- the one-error tree of `err`, without an `Is` method
  have hT := fun (tgt : GoInterface) =>
    _root_.Perennial.errors.errorIsTree_leaf (GF := GF) e (fun _ => False) tgt hleaf hsh.2
  wp_auto
  wp_apply (wp_IsDE (· = GoInterface.ok e) (fun _ => False) (GoInterface.ok e)
    (interface.mkOk _root_.Perennial.context.deadlineExceededError.ty
      #(zero_val _root_.Perennial.context.deadlineExceededError))) $$ [] as %b1 -
  · iframe #
    isplitl []
    · iapply hT
    · isplitl []
      · ipureintro; rfl
      · ipureintro; exact deTyped_single e hde
  cases b1
  · -- not `DeadlineExceeded`
    wp_auto
    wp_apply (wp_Is (· = GoInterface.ok e) (fun _ => False) (GoInterface.ok e)
      (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #xc)
      (fun tii h => by cases h; exact ⟨_, _, rfl, rfl⟩)
      (fun ii tii hS ht hty => hptr ii hS.symm (by cases hS; cases ht; exact hty))) $$ [] as %b2 -
    · iframe #
      isplitl []
      · iapply hT
      · ipureintro; rfl
    cases b2
    · wp_auto
      cetg_tail
    · wp_auto
      cetg_tail
  · cetg_tail

end proof

end EtcdGrove
end Perennial
