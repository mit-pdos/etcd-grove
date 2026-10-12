/-
The auth applier's permission checks of a transaction (`server/v3/etcdserver/apply`, auth.go):
`checkTxnPermission` and `checkTxnReqsPermission` are mutually recursive (a nested
transaction), so their joint proof is here, by Löb induction; each `Proof/` file takes it.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.checkTxnPermission
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.checkTxnReqsPermission
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.checkPutAuth
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Packaging

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-! ## The auth layer's KV methods: a rejection, or the inner applier's answer -/

/-- **An auth rejection** of a KV request (the check failed, before any write): the outcome
`.rejected .auth`, the log unchanged, `Pre` back, the `authInfo` returned to the chain's
resources. -/
theorem apply.auth_reject_kvPost (E : apply.AEnv GF) (c : apply.Chain) (p : Loc)
    (inner : GoInterface) (rq : IRRModel) (log : mvcc.Log) (R : apply.Outcome → IProp GF)
    (Pre Q Post : IProp GF) (hk : apply.authChecks (dispatchKind rq) = true) :
    structFieldRef authApplierV3 go!"applierV3" p ↦□ inner ⊢
      R (.rejected .auth) -∗ apply.kvOwn E log -∗ apply.authInfoOwn p -∗
      apply.chainRes c inner -∗ mvcc.csContract E.P E.f Pre Q Post -∗
      apply.kvPost E (.auth c) (interface.mkOk (go.GoType.PointerType authApplierV3.ty) #p) rq log
        R Pre Post := by
  iintro #Happ HR Hkv Hinfo Hres Hcs
  ihave HPre := apply.csContract_pre _ _ _ _ _ $$ Hcs
  iunfold apply.kvPost
  iexists (.rejected .auth)
  isplitr
  · ipureintro
    simp [apply.chainStep, hk]
  simp only [apply.Outcome.logAfter]
  iframe HR Hkv
  isplitl [Hinfo Hres]
  · iapply apply.chainRes_auth_in c p inner $$ Happ Hinfo Hres
  iright; iexact HPre

/-- **The inner applier's answer**, through the auth layer (its check passed). -/
theorem apply.auth_pass_kvPost (E : apply.AEnv GF) (c : apply.Chain) (p : Loc)
    (inner : GoInterface) (rq : IRRModel) (log : mvcc.Log) (R : apply.Outcome → IProp GF)
    (Pre Post : IProp GF) :
    structFieldRef authApplierV3 go!"applierV3" p ↦□ inner ⊢
      apply.kvPost E c inner rq log R Pre Post -∗ apply.authInfoOwn p -∗
      apply.kvPost E (.auth c) (interface.mkOk (go.GoType.PointerType authApplierV3.ty) #p) rq log
        R Pre Post := by
  iintro #Happ Hpost Hinfo
  iunfold apply.kvPost at Hpost
  iunfold apply.kvPost
  icases Hpost with ⟨%oc, %Hst, HR, Hkv, Hres, HPP⟩
  iexists oc
  iframe HR Hkv HPP
  isplitr
  · ipureintro
    simp only [apply.chainStep]
    split <;> simp [Hst]
  iapply apply.chainRes_auth_in c p inner $$ Happ Hinfo Hres

/-- A `*pb.RequestOp`'s four kinds, as `checkTxnReqsPermission`'s type switch sees them. -/
theorem apply.requestOpIs_cases_auth (p : Loc) (op : TxnOp) :
    txn.requestOpIs (GF := GF) p op ⊢ ⌜p ≠ null⌝ ∗
      ((∃ (w r : Loc) (o : OpFull),
          structFieldRef etcdserverpb.RequestOp go!"Request" p ↦□
            (interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestRange.ty) #w :
              GoInterface) ∗
          structFieldRef etcdserverpb.RequestOp_RequestRange go!"RequestRange" w ↦□ r ∗
          txn.rangeRequestIs r o) ∨
       (∃ (w r : Loc) (o : OpFull),
          structFieldRef etcdserverpb.RequestOp go!"Request" p ↦□
            (interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestPut.ty) #w :
              GoInterface) ∗
          structFieldRef etcdserverpb.RequestOp_RequestPut go!"RequestPut" w ↦□ r ∗
          txn.putRequestIs r o) ∨
       (∃ (w r : Loc) (o : OpFull),
          structFieldRef etcdserverpb.RequestOp go!"Request" p ↦□
            (interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestDeleteRange.ty) #w :
              GoInterface) ∗
          structFieldRef etcdserverpb.RequestOp_RequestDeleteRange go!"RequestDeleteRange" w ↦□ r ∗
          txn.deleteRangeRequestIs r o) ∨
       (∃ (w r : Loc) (t : TxnModel),
          structFieldRef etcdserverpb.RequestOp go!"Request" p ↦□
            (interface.mkOk (go.GoType.PointerType etcdserverpb.RequestOp_RequestTxn.ty) #w :
              GoInterface) ∗
          structFieldRef etcdserverpb.RequestOp_RequestTxn go!"RequestTxn" w ↦□ r ∗
          txn.txnRequestIs r t)) := by
  cases op
  case txn cs ts es =>
    unfold txn.requestOpIs
    iintro #⟨%Hpn, %w, %r, #HR, #Hw, %Hrn, %csl, %ssl, %fsl, %cps, %sps, %fps, #H1, #H2, #H3, #H4,
      #H5, #H6, #H7, #H8, #H9⟩
    isplitl []
    · ipureintro; exact Hpn
    iright; iright; iright
    iexists w, r, { cmps := cs, thenOps := ts, elseOps := es }
    iframe HR Hw
    unfold txn.txnRequestIs txn.txnFieldsIs
    isplitl []
    · ipureintro; exact Hrn
    iexists csl, ssl, fsl, cps, sps, fps
    iframe #
  all_goals
    unfold txn.requestOpIs
    iintro #⟨%Hpn, %u, %w, %r, %o, #HR, (⟨%Hu, #Hw, #Hr⟩ | ⟨%Hu, #Hw, #Hr⟩ | ⟨%Hu, #Hw, #Hr⟩)⟩
    all_goals
      obtain ⟨rfl, -⟩ := Hu
      isplitl []
      · ipureintro; exact Hpn
    · ileft; iexists w, r, o; iframe #
    · iright; ileft; iexists w, r, o; iframe #
    · iright; iright; ileft; iexists w, r, o; iframe #

/-- The `i`-th request of the list. -/
theorem apply.requestOpsIs_elem_auth :
    ∀ (ps : List Loc) (ops : List TxnOp) (i : Nat) (p : Loc), ps[i]? = some p →
      txn.requestOpsIs (GF := GF) ps ops ⊢ ∃ op, txn.requestOpIs p op
  | [], _, _, _, h => by simp at h
  | _ :: _, [], _, _, _ => by unfold txn.requestOpsIs; iintro H; iexfalso; iexact H
  | q :: ps, op :: ops, 0, p, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    unfold txn.requestOpsIs
    iintro ⟨H, -⟩
    iexists op
    iexact H
  | q :: ps, op :: ops, i + 1, p, h => by
    simp only [List.getElem?_cons_succ] at h
    unfold txn.requestOpsIs
    iintro ⟨-, H⟩
    iapply apply.requestOpsIs_elem_auth ps ops i p h $$ H

/-- `checkTxnPermission`'s triple, as a hypothesis (the Löb induction's). -/
def apply.txnPermT (st le : GoInterface) (γ : mvcc.StoreNames) (P : IProp GF) (f : val)
    (ai : Loc) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (dq : DFrac) : IProp GF :=
  iprop(□ ∀ (rt : Loc) (t : TxnModel) (Φ : val → IProp GF),
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.isAuthStore st P f ∗ apply.isApplyLessor le γ P f ∗ ai ↦{dq} info ∗
      txn.txnRequestIs rt t -∗
    (▷ ∀ err : GoInterface, ai ↦{dq} info -∗ Φ #err) -∗
    WP (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.checkTxnPermission))
      (Val #st)) (Val #ai)) (Val #le)) (Val #rt)) {{ Φ }})

instance apply.txnPermT_persistent (st le : GoInterface) (γ : mvcc.StoreNames) (P : IProp GF)
    (f : val) (ai : Loc) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (dq : DFrac) :
    Persistent (apply.txnPermT st le γ P f ai info dq) := by
  unfold apply.txnPermT; infer_instance

/-- **`checkTxnReqsPermission`, over `checkTxnPermission`'s triple** (`txnPermT`, for its
nested transactions). -/
theorem apply.checkTxnReqs_of
    (hPut : apply.checkPutAuth.spec (GF := GF) (hG := hG)) :
  ∀ (st le : GoInterface) (γ : mvcc.StoreNames) (P : IProp GF) (f : val) (ai : Loc)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (dq : DFrac) (reqs : GoSlice) (ps : List Loc)
    (ops : List TxnOp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.isAuthStore st P f ∗ apply.isApplyLessor le γ P f ∗ ai ↦{dq} info ∗
      reqs ↦*□ ps ∗ txn.requestOpsIs ps ops ∗ apply.txnPermT st le γ P f ai info dq }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.checkTxnReqsPermission))
      (Val #st)) (Val #ai)) (Val #le)) (Val #reqs))
  {{ (err : GoInterface), RET #err; ai ↦{dq} info }} := by
  intro st le γ P f ai info dq reqs ps ops
  wp_start as ⟨#Hst, #Hle, Hai, #Hreqs, #Hops, #IH⟩
  ihave %Hsll := ownSlice_len _ _ _ $$ Hreqs
  ihave #Hst' := Hst
  iunfold apply.isAuthStore at Hst'
  icases Hst' with ⟨%sti, %Hsti, #HPut, #HRange, #HDel, -⟩
  iunfold apply.permCheck3 at HRange
  iunfold apply.permCheck3 at HDel
  subst Hsti
  wp_auto
  irename «as» => Has
  ihave HI : iprop(∃ (n : w64) (q : Loc),
      "i" ∷ i_ptr ↦ n ∗ "requ" ∷ requ_ptr ↦ q ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z reqs.len⌝) $$ [i requ]
  · iexists W64 0, _
    iframe i requ
    ipureintro
    constructor
    · decide
    · have := Hsll.2; word
  wp_for HI
  wp_if_destruct
  · obtain ⟨p, hp⟩ : ∃ p, ps[(sint.Z n).toNat]? = some p :=
      ⟨_, List.getElem?_eq_getElem (by unfold sint.nat at Hsll; word)⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z reqs.len := ⟨Hn.1, Hif⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index reqs (sint.Z n) ps DFrac.discard p Hn.1 $$ [] as -
    · iframe Hreqs; ipureintro; exact hp
    ihave ⟨%op, #Hop⟩ := apply.requestOpsIs_elem_auth ps ops _ p hp $$ Hops
    icases apply.requestOpIs_cases_auth p op $$ Hop with ⟨%Hpn, (⟨%w, %r, %o, #HR, #Hw, #Hr⟩ |
      ⟨%w, %r, %o, #HR, #Hw, #Hr⟩ | ⟨%w, %r, %o, #HR, #Hw, #Hr⟩ | ⟨%w, %r, %t, #HR, #Hw, #Hr⟩)⟩
    · -- a range
      iunfold txn.rangeRequestIs at Hr
      icases Hr with ⟨%Hrn, %ksl, %esl, %k, %e, %x1, %x2, %x3, %x4, %x5, %x6, %x7, %x8, %x9, %x10,
        %x11, #HK, #Hk, #HE, #He, -⟩
      wp_auto
      simp only [Hrn, decide_false]
      wp_auto
      wp_apply HRange $$ %ai %info %dq %ksl %esl %k %e %DFrac.discard %DFrac.discard [Hai] as %err ⟨Hai, -⟩
      · iframe; iframe #
      cases err with
      | nil =>
        wp_auto
        wp_for_post
        iframe
        iexists n + W64 1, p
        iframe
        ipureintro; constructor <;> word
      | ok e' =>
        wp_auto
        wp_for_post
        iapply HΦ; iexact Hai
    · -- a put
      ihave #Hr' := Hr
      iunfold txn.putRequestIs at Hr'
      icases Hr' with ⟨%Hrn, -⟩
      wp_auto
      simp only [Hrn, decide_false]
      wp_auto
      wp_apply (hPut _ le γ P f ai info dq r o) $$ [$Hst $Hle $Hai $Hr] as %err Hai
      cases err with
      | nil =>
        wp_auto
        wp_for_post
        iframe
        iexists n + W64 1, p
        iframe
        ipureintro; constructor <;> word
      | ok e' =>
        wp_auto
        wp_for_post
        iapply HΦ; iexact Hai
    · -- a delete
      iunfold txn.deleteRangeRequestIs at Hr
      icases Hr with ⟨%Hrn, %ksl, %esl, %k, %e, %pk, #HK, #Hk, #HE, #He, #HPK, -⟩
      wp_auto
      simp only [Hrn, decide_false]
      wp_auto
      cases pk
      · wp_auto
        wp_apply HDel $$ %ai %info %dq %ksl %esl %k %e %DFrac.discard %DFrac.discard [Hai] as %err ⟨Hai, -⟩
        · iframe; iframe #
        cases err with
        | nil =>
          wp_auto
          wp_for_post
          iframe
          iexists n + W64 1, p
          iframe
          ipureintro; constructor <;> word
        | ok e' =>
          wp_auto
          wp_for_post
          iapply HΦ; iexact Hai
      wp_auto
      wp_apply HRange $$ %ai %info %dq %ksl %esl %k %e %DFrac.discard %DFrac.discard [Hai] as %err ⟨Hai, -⟩
      · iframe; iframe #
      cases err with
      | ok e' =>
        wp_auto
        wp_for_post
        iapply HΦ; iexact Hai
      | nil =>
      wp_auto
      wp_apply HDel $$ %ai %info %dq %ksl %esl %k %e %DFrac.discard %DFrac.discard [Hai] as %err ⟨Hai, -⟩
      · iframe; iframe #
      cases err with
      | nil =>
        wp_auto
        wp_for_post
        iframe
        iexists n + W64 1, p
        iframe
        ipureintro; constructor <;> word
      | ok e' =>
        wp_auto
        wp_for_post
        iapply HΦ; iexact Hai
    · -- a nested transaction
      ihave #Hr' := Hr
      iunfold txn.txnRequestIs at Hr'
      icases Hr' with ⟨%Hrn, -⟩
      wp_auto
      simp only [Hrn, decide_false]
      wp_auto
      iunfold apply.txnPermT at IH
      wp_apply IH $$ %r %t [Hai] as %err Hai
      · iframe; iframe #
      cases err with
      | nil =>
        wp_auto
        wp_for_post
        iframe
        iexists n + W64 1, p
        iframe
        ipureintro; constructor <;> word
      | ok e' =>
        wp_auto
        wp_for_post
        iapply HΦ; iexact Hai
  iapply HΦ; iexact Hai

theorem apply.checkTxnPermission_loeb
    (hPut : apply.checkPutAuth.spec (GF := GF) (hG := hG)) :
    apply.checkTxnPermission.spec (GF := GF) (hG := hG) := by
  intro st le γ P f ai info dq rt t
  iloeb as IH generalizing %rt %t
  wp_start as ⟨#Hst, #Hle, Hai, #Hrt⟩
  ihave #IHT : apply.txnPermT st le γ P f ai info dq $$ []
  · iunfold apply.txnPermT; iexact IH
  iclear IH
  iunfold txn.txnRequestIs at Hrt
  icases Hrt with ⟨%Hrtn, Hrt⟩
  iunfold txn.txnFieldsIs at Hrt
  icases Hrt with ⟨%csl, %ssl, %fsl, %cps, %sps, %fps, #Hc, #Hcsl, #Hcs, #Hs, #Hssl, #Hss, #Hf,
    #Hfsl, #Hfs⟩
  ihave %Hsll := ownSlice_len _ _ _ $$ Hcsl
  iunfold txn.comparesIs at Hcs
  icases Hcs with ⟨%Hcl, #Hcs⟩
  ihave #Hst' := Hst
  iunfold apply.isAuthStore at Hst'
  icases Hst' with ⟨%sti, %Hsti, -, #HRange, -⟩
  iunfold apply.permCheck3 at HRange
  subst Hsti
  wp_auto
  irename «as» => Has
  ihave HI : iprop(∃ (n : w64) (q : Loc),
      "i" ∷ i_ptr ↦ n ∗ "c" ∷ c_ptr ↦ q ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z csl.len⌝) $$ [i c]
  · iexists W64 0, _
    iframe i c
    ipureintro
    constructor
    · decide
    · have := Hsll.2; word
  wp_for HI
  wp_if_destruct
  · obtain ⟨p, hp⟩ : ∃ p, cps[(sint.Z n).toNat]? = some p :=
      ⟨_, List.getElem?_eq_getElem (by unfold sint.nat at Hsll; word)⟩
    obtain ⟨cm, hcm⟩ : ∃ cm, (t.cmps)[(sint.Z n).toNat]? = some cm :=
      ⟨_, List.getElem?_eq_getElem (by unfold sint.nat at Hsll; word)⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z csl.len := ⟨Hn.1, Hif⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index csl (sint.Z n) cps DFrac.discard p Hn.1 $$ [] as -
    · iframe Hcsl; ipureintro; exact hp
    ihave #Hp := Hcs $$ %_ %p %cm [] []
    · ipureintro; exact hp
    · ipureintro; exact hcm
    iunfold txn.compareIs at Hp
    icases Hp with ⟨%Hpn, %ksl, %esl, %e, %u, -, -, #HK, #Hk, #HE, #He, -⟩
    wp_auto
    wp_apply HRange $$ %ai %info %dq %ksl %esl %cm.key %e %DFrac.discard %DFrac.discard [Hai] as %err ⟨Hai, -⟩
    · iframe; iframe #
    cases err with
    | nil =>
      wp_auto
      wp_for_post
      iframe
      iexists n + W64 1, p
      iframe
      ipureintro; constructor <;> word
    | ok e' =>
      wp_auto
      wp_for_post
      iapply HΦ; iexact Hai
  wp_apply (apply.checkTxnReqs_of hPut _ le γ P f ai info dq ssl sps t.thenOps) $$ [$Hst $Hle $Hai $Hssl $Hss $IHT] as %err Hai
  cases err with
  | ok e' =>
    wp_auto
    iapply HΦ; iexact Hai
  | nil =>
  wp_auto
  wp_apply (apply.checkTxnReqs_of hPut _ le γ P f ai info dq fsl fps t.elseOps) $$ [$Hst $Hle $Hai $Hfsl $Hfs $IHT] as %err Hai
  iapply HΦ; iexact Hai

end proof

end EtcdGrove
end Perennial
