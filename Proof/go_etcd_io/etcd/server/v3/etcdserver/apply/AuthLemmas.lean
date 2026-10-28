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
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthClass

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-! ## The auth layer's KV methods: a rejection, or the inner applier's answer -/

/-- `auth_reject_kvPost` with a floor (unit V2): a rejection meets any floor (and says nothing of
the class: `chainClass_auth_rejected`). -/
theorem apply.auth_reject_kvPostF (E : apply.AEnv GF) (on : Bool) (c : apply.Chain) (p : Loc)
    (inner : GoInterface) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (rq : IRRModel)
    (log F : mvcc.Log) (R : apply.Outcome → IProp GF)
    (Pre Q Post : IProp GF) (hk : apply.authChecks (dispatchKind rq) = true)
    (hm : apply.authMayReject on rq) :
    structFieldRef authApplierV3 go!"applierV3" p ↦□ inner ⊢
      R (.rejected .auth) -∗ apply.kvOwn E log -∗
      structFieldRef authApplierV3 go!"authInfo" p ↦ info -∗
      apply.chainResAny c inner -∗ mvcc.csContract E.P E.f Pre Q Post -∗
      apply.kvPostF E (.auth on c) (interface.mkOk (go.GoType.PointerType authApplierV3.ty) #p) info rq
        log F R Pre Post := by
  iintro #Happ HR Hkv Hinfo Hres Hcs
  ihave HPre := apply.csContract_pre _ _ _ _ _ $$ Hcs
  iunfold apply.kvPostF
  iexists (.rejected .auth)
  isplitr
  · ipureintro
    exact ⟨by simp [apply.chainStep, hk, hm], fun _ _ h => by cases h⟩
  simp only [apply.Outcome.logAfter]
  iframe HR Hkv
  isplitl [Hinfo Hres]
  · iapply apply.chainRes_auth_in c p inner info $$ Happ Hinfo Hres
  isplitl [HPre]
  · iright; iexact HPre
  iapply apply.chainClass_auth_rejected

/-- `auth_pass_kvPost` with a floor (unit V2): the inner's post, the field, and the request's
class the passed checks established (A3). -/
theorem apply.auth_pass_kvPostF (E : apply.AEnv GF) (on : Bool) (c : apply.Chain) (p : Loc)
    (inner : GoInterface) (info info' : go_etcd_io.etcd.server.v3.auth.AuthInfo) (rq : IRRModel)
    (log F : mvcc.Log) (R : apply.Outcome → IProp GF) (Pre Post : IProp GF) :
    structFieldRef authApplierV3 go!"applierV3" p ↦□ inner ⊢
      apply.kvPostF E c inner info' rq log F R Pre Post -∗
      structFieldRef authApplierV3 go!"authInfo" p ↦ info -∗ apply.reqClass E.authMode info rq -∗
      apply.kvPostF E (.auth on c) (interface.mkOk (go.GoType.PointerType authApplierV3.ty) #p) info rq
        log F R Pre Post := by
  iintro #Happ Hpost Hinfo #Hcls
  iunfold apply.kvPostF at Hpost
  iunfold apply.kvPostF
  icases Hpost with ⟨%oc, %Hst, HR, Hkv, Hres, HPP, -⟩
  iexists oc
  iframe HR Hkv HPP
  isplitr
  · ipureintro
    refine ⟨?_, Hst.2⟩
    simp only [apply.chainStep]
    split <;> simp [Hst.1]
  ihave Hres := apply.chainResAny_of c inner info' $$ Hres
  isplitl [Hinfo Hres]
  · iapply apply.chainRes_auth_in c p inner info $$ Happ Hinfo Hres
  iapply apply.chainClass_auth_pass $$ Hcls

/-- `checkTxnPermission`'s triple, as a hypothesis (the Löb induction's). -/
def apply.txnPermT (st le : GoInterface) (γ : mvcc.StoreNames) (P : IProp GF) (f : val)
    (RD : IProp GF) (on : auth.AuthMode) (RW : IProp GF) (ai : Loc) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (dq : DFrac) :
    IProp GF :=
  iprop(□ ∀ (rt : Loc) (t : TxnModel) (Φ : val → IProp GF),
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.isAuthStore st γ P f RD on RW ∗ apply.isApplyLessorAny le γ P f RW ∗ ai ↦{dq} info ∗ RD ∗
      txn.txnRequestIs rt t -∗
    (▷ ∀ err : GoInterface, ai ↦{dq} info ∗ RD ∗ authApplyErrIs err ∗
        ⌜on.isOn = false → err = GoInterface.nil⌝ ∗
        (∀ _ : err = GoInterface.nil, apply.txnClass on info t) -∗ Φ #err) -∗
    WP (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.checkTxnPermission))
      (Val #st)) (Val #ai)) (Val #le)) (Val #rt)) {{ Φ }})

instance apply.txnPermT_persistent (st le : GoInterface) (γ : mvcc.StoreNames) (P : IProp GF)
    (f : val) (RD : IProp GF) (on : auth.AuthMode) (RW : IProp GF) (ai : Loc) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (dq : DFrac) : Persistent (apply.txnPermT st le γ P f RD on RW ai info dq) := by
  unfold apply.txnPermT; infer_instance

/-- **`checkTxnReqsPermission`, over `checkTxnPermission`'s triple** (`txnPermT`, for its
nested transactions). -/
theorem apply.checkTxnReqs_of
    (hPut : apply.checkPutAuth.spec (GF := GF) (hG := hG)) :
  ∀ (st le : GoInterface) (γ : mvcc.StoreNames) (P : IProp GF) (f : val) (RD : IProp GF) (on : auth.AuthMode) (RW : IProp GF)
    (ai : Loc) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (dq : DFrac) (reqs : GoSlice)
    (ps : List Loc) (ops : List TxnOp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.isAuthStore st γ P f RD on RW ∗ apply.isApplyLessorAny le γ P f RW ∗ ai ↦{dq} info ∗ RD ∗
      reqs ↦*□ ps ∗ txn.requestOpsIs ps ops ∗ apply.txnPermT st le γ P f RD on RW ai info dq }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.checkTxnReqsPermission))
      (Val #st)) (Val #ai)) (Val #le)) (Val #reqs))
  {{ (err : GoInterface), RET #err; ai ↦{dq} info ∗ RD ∗ authApplyErrIs err ∗
      ⌜on.isOn = false → err = GoInterface.nil⌝ ∗
      (∀ _ : err = GoInterface.nil, apply.opsClass on info ops) }} := by
  intro st le γ P f RD on RW ai info dq reqs ps ops
  wp_start as ⟨#Hst, #Hle, Hai, Hrd, #Hreqs, #Hops, #IH⟩
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
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z reqs.len⌝ ∗
      "#Hcls" ∷ apply.opsClass on info (ops.take (sint.nat n))) $$ [i requ]
  · iexists W64 0, _
    iframe i requ
    isplitl []
    · ipureintro
      constructor
      · decide
      · have := Hsll.2; word
    · rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
      iapply apply.opsClass_nil
  wp_for HI
  wp_if_destruct
  · obtain ⟨p, hp⟩ : ∃ p, ps[(sint.Z n).toNat]? = some p :=
      ⟨_, List.getElem?_eq_getElem (by unfold sint.nat at Hsll; word)⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z reqs.len := ⟨Hn.1, Hif⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index reqs (sint.Z n) ps DFrac.discard p Hn.1 $$ [] as -
    · iframe Hreqs; ipureintro; exact hp
    ihave ⟨%op, %hop, #Hop⟩ := txn.requestOpsIs_elem ps ops _ p hp $$ Hops
    icases txn.requestOpIs_cases p op $$ Hop with ⟨%Hpn, (⟨%w, %r, %o, %Hpo, #HR, #Hw, #Hr⟩ |
      ⟨%w, %r, %o, %Hpo, #HR, #Hw, #Hr⟩ | ⟨%w, %r, %o, %Hpo, #HR, #Hw, #Hr⟩ | ⟨%w, %r, %cs, %ts, %es, %Hpo, #HR, #Hw, #Hr⟩)⟩
    · -- a range
      iunfold txn.rangeRequestIs at Hr
      icases Hr with ⟨%Hrn, %ksl, %esl, %k, %e, %x1, %x2, %x3, %x4, %x5, %x6, %x7, %x8, %x9, %x10,
        %x11, #HK, #Hk, #HE, #He, -, -, -, -, -, -, -, -, -, -, -, %Ho, %Hkb⟩
      wp_auto
      simp only [Hrn, decide_false]
      wp_auto
      wp_apply HRange $$ %ai %info %dq %ksl %esl %k %e %DFrac.discard %DFrac.discard [Hai Hrd] as %err ⟨Hai, -, -, Hrd, #HeI1, %Hof1, #Hv1⟩
      · iframe; iframe #; try (ipureintro; exact Hkb)
      cases err with
      | nil =>
        wp_auto
        wp_for_post
        iframe
        iexists n + W64 1, p
        iframe
        isplitl []
        · ipureintro; constructor <;> word
        · ihave %Hel := ownSlice_len _ _ _ $$ He
          have hsn : sint.nat (n + W64 1) = sint.nat n + 1 := by unfold sint.nat at *; word
          rw [hsn, List.take_add_one, show ops[sint.nat n]? = some op from hop, Option.toList_some]
          iapply apply.opsClass_snoc
          iframe Hcls
          rw [Hpo]
          iapply apply.opClass_get
          unfold apply.rangeClass
          iexists e
          isplitl []
          · ipureintro; rw [Ho]; simp only [txn.rangeOpOf.proj_base]; exact apply.authEndOf_rangeEndOf esl e Hel.1
          · rw [Ho]; simp only [txn.rangeOpOf.proj_key]
            iapply (apply.classRes_of_permVerdict on info k e .read) $$ Hv1
      | ok e' =>
        wp_auto
        wp_for_post
        iapply HΦ; iframe Hai Hrd; isplitr; (first | iexact HeI9 | iexact HeI8 | iexact HeI7 | iexact HeI6 | iexact HeI5 | iexact HeI4 | iexact HeI3 | iexact HeI2 | iexact HeI1 | iapply authApplyErrIs_nil); isplitr; (ipureintro; first | assumption | (intro _; rfl)); (iintro %h; cases h)
    · -- a put
      ihave #Hr' := Hr
      iunfold txn.putRequestIs at Hr'
      icases Hr' with ⟨%Hrn, -⟩
      wp_auto
      simp only [Hrn, decide_false]
      wp_auto
      wp_apply (hPut _ le γ P f RD on RW ai info dq r o) $$ [$Hst $Hle $Hai $Hrd $Hr] as %err ⟨Hai, Hrd, #HeI2, %Hof2, #Hcls2⟩
      cases err with
      | nil =>
        wp_auto
        wp_for_post
        iframe
        iexists n + W64 1, p
        iframe
        isplitl []
        · ipureintro; constructor <;> word
        · have hsn : sint.nat (n + W64 1) = sint.nat n + 1 := by unfold sint.nat at *; word
          rw [hsn, List.take_add_one, show ops[sint.nat n]? = some op from hop, Option.toList_some]
          iapply apply.opsClass_snoc
          iframe Hcls
          rw [Hpo]
          iapply apply.opClass_put_of_putClass
          ihave #Hpc := Hcls2 $$ %rfl
          iexact Hpc
      | ok e' =>
        wp_auto
        wp_for_post
        iapply HΦ; iframe Hai Hrd; isplitr; (first | iexact HeI9 | iexact HeI8 | iexact HeI7 | iexact HeI6 | iexact HeI5 | iexact HeI4 | iexact HeI3 | iexact HeI2 | iexact HeI1 | iapply authApplyErrIs_nil); isplitr; (ipureintro; first | assumption | (intro _; rfl)); (iintro %h; cases h)
    · -- a delete
      iunfold txn.deleteRangeRequestIs at Hr
      icases Hr with ⟨%Hrn, %ksl, %esl, %k, %e, %pk, #HK, #Hk, #HE, #He, #HPK, %Ho, %Hkb⟩
      wp_auto
      simp only [Hrn, decide_false]
      wp_auto
      cases pk
      · wp_auto
        wp_apply HDel $$ %ai %info %dq %ksl %esl %k %e %DFrac.discard %DFrac.discard [Hai Hrd] as %err ⟨Hai, -, -, Hrd, #HeI3, %Hof3, #Hv3⟩
        · iframe; iframe #; try (ipureintro; exact Hkb)
        cases err with
        | nil =>
          wp_auto
          wp_for_post
          iframe
          iexists n + W64 1, p
          iframe
          isplitl []
          · ipureintro; constructor <;> word
          · ihave %Hel := ownSlice_len _ _ _ $$ He
            have hsn : sint.nat (n + W64 1) = sint.nat n + 1 := by unfold sint.nat at *; word
            rw [hsn, List.take_add_one, show ops[sint.nat n]? = some op from hop, Option.toList_some]
            iapply apply.opsClass_snoc
            iframe Hcls
            rw [Hpo]
            iapply apply.opClass_delete
            unfold apply.deleteClass
            iexists e
            isplitl []
            · ipureintro; rw [Ho]; simp only [txn.deleteOpOf.proj_base]; exact apply.authEndOf_rangeEndOf esl e Hel.1
            · rw [Ho]; simp only [txn.deleteOpOf.proj_key, txn.deleteOpOf.proj_base, Bool.false_eq_true, ↓reduceIte]
              iapply (apply.classRes_of_permVerdict on info k e .write) $$ Hv3
        | ok e' =>
          wp_auto
          wp_for_post
          iapply HΦ; iframe Hai Hrd; isplitr; (first | iexact HeI9 | iexact HeI8 | iexact HeI7 | iexact HeI6 | iexact HeI5 | iexact HeI4 | iexact HeI3 | iexact HeI2 | iexact HeI1 | iapply authApplyErrIs_nil); isplitr; (ipureintro; first | assumption | (intro _; rfl)); (iintro %h; cases h)
      wp_auto
      wp_apply HRange $$ %ai %info %dq %ksl %esl %k %e %DFrac.discard %DFrac.discard [Hai Hrd] as %err ⟨Hai, -, -, Hrd, #HeI4, %Hof4, #Hv4⟩
      · iframe; iframe #; try (ipureintro; exact Hkb)
      cases err with
      | ok e' =>
        wp_auto
        wp_for_post
        iapply HΦ; iframe Hai Hrd; isplitr; (first | iexact HeI9 | iexact HeI8 | iexact HeI7 | iexact HeI6 | iexact HeI5 | iexact HeI4 | iexact HeI3 | iexact HeI2 | iexact HeI1 | iapply authApplyErrIs_nil); isplitr; (ipureintro; first | assumption | (intro _; rfl)); (iintro %h; cases h)
      | nil =>
      wp_auto
      wp_apply HDel $$ %ai %info %dq %ksl %esl %k %e %DFrac.discard %DFrac.discard [Hai Hrd] as %err ⟨Hai, -, -, Hrd, #HeI5, %Hof5, #Hv5⟩
      · iframe; iframe #; try (ipureintro; exact Hkb)
      cases err with
      | nil =>
        wp_auto
        wp_for_post
        iframe
        iexists n + W64 1, p
        iframe
        isplitl []
        · ipureintro; constructor <;> word
        · ihave %Hel := ownSlice_len _ _ _ $$ He
          have hsn : sint.nat (n + W64 1) = sint.nat n + 1 := by unfold sint.nat at *; word
          rw [hsn, List.take_add_one, show ops[sint.nat n]? = some op from hop, Option.toList_some]
          iapply apply.opsClass_snoc
          iframe Hcls
          rw [Hpo]
          iapply apply.opClass_delete
          unfold apply.deleteClass
          iexists e
          isplitl []
          · ipureintro; rw [Ho]; simp only [txn.deleteOpOf.proj_base]; exact apply.authEndOf_rangeEndOf esl e Hel.1
          · rw [Ho]; simp only [txn.deleteOpOf.proj_key, txn.deleteOpOf.proj_base, ↓reduceIte]
            iapply apply.classRes_cons
            isplitl []
            · iapply (apply.classRes_of_permVerdict on info k e .write) $$ Hv5
            · iapply (apply.classRes_of_permVerdict on info k e .read) $$ Hv4
      | ok e' =>
        wp_auto
        wp_for_post
        iapply HΦ; iframe Hai Hrd; isplitr; (first | iexact HeI9 | iexact HeI8 | iexact HeI7 | iexact HeI6 | iexact HeI5 | iexact HeI4 | iexact HeI3 | iexact HeI2 | iexact HeI1 | iapply authApplyErrIs_nil); isplitr; (ipureintro; first | assumption | (intro _; rfl)); (iintro %h; cases h)
    · -- a nested transaction
      ihave #Hr' := Hr
      iunfold txn.txnRequestIs at Hr'
      icases Hr' with ⟨%Hrn, -⟩
      wp_auto
      simp only [Hrn, decide_false]
      wp_auto
      iunfold apply.txnPermT at IH
      wp_apply IH $$ %r %({ cmps := cs, thenOps := ts, elseOps := es } : TxnModel) [Hai Hrd] as %err ⟨Hai, Hrd, #HeI6, %Hof6, #Hcls6⟩
      · iframe; iframe #
      cases err with
      | nil =>
        wp_auto
        wp_for_post
        iframe
        iexists n + W64 1, p
        iframe
        isplitl []
        · ipureintro; constructor <;> word
        · have hsn : sint.nat (n + W64 1) = sint.nat n + 1 := by unfold sint.nat at *; word
          rw [hsn, List.take_add_one, show ops[sint.nat n]? = some op from hop, Option.toList_some]
          iapply apply.opsClass_snoc
          iframe Hcls
          rw [Hpo]
          iapply apply.opClass_txn
          ihave #Ht := Hcls6 $$ %rfl
          iexact Ht
      | ok e' =>
        wp_auto
        wp_for_post
        iapply HΦ; iframe Hai Hrd; isplitr; (first | iexact HeI9 | iexact HeI8 | iexact HeI7 | iexact HeI6 | iexact HeI5 | iexact HeI4 | iexact HeI3 | iexact HeI2 | iexact HeI1 | iapply authApplyErrIs_nil); isplitr; (ipureintro; first | assumption | (intro _; rfl)); (iintro %h; cases h)
  iapply HΦ; iframe Hai Hrd; isplitr; (first | iexact HeI9 | iexact HeI8 | iexact HeI7 | iexact HeI6 | iexact HeI5 | iexact HeI4 | iexact HeI3 | iexact HeI2 | iexact HeI1 | iapply authApplyErrIs_nil); isplitr; (ipureintro; first | assumption | (intro _; rfl))
  iintro %_
  ihave %Hpl := txn.requestOpsIs_length ps ops $$ Hops
  have hle : ops.length ≤ sint.nat n := by unfold sint.nat at *; word
  iExactEq Hcls
  rw [List.take_of_length_le hle]

theorem apply.checkTxnPermission_loeb
    (hPut : apply.checkPutAuth.spec (GF := GF) (hG := hG)) :
    apply.checkTxnPermission.spec (GF := GF) (hG := hG) := by
  intro st le γ P f RD on RW ai info dq rt t
  iloeb as IH generalizing %rt %t
  wp_start as ⟨#Hst, #Hle, Hai, Hrd, #Hrt⟩
  ihave #IHT : apply.txnPermT st le γ P f RD on RW ai info dq $$ []
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
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z csl.len⌝ ∗
      "#Hcc" ∷ apply.cmpsClass on info (t.cmps.take (sint.nat n))) $$ [i c]
  · iexists W64 0, _
    iframe i c
    isplitl []
    · ipureintro
      constructor
      · decide
      · have := Hsll.2; word
    · rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
      iapply apply.cmpsClass_nil
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
    icases Hp with ⟨%Hpn, %ksl, %esl, %e, %u, -, -, #HK, #Hk, #HE, #He, %Hce, -, -, -, %Hkb⟩
    wp_auto
    wp_apply HRange $$ %ai %info %dq %ksl %esl %cm.key %e %DFrac.discard %DFrac.discard [Hai Hrd] as %err ⟨Hai, -, -, Hrd, #HeI7, %Hof7, #Hv7⟩
    · iframe; iframe #; try (ipureintro; exact Hkb)
    cases err with
    | nil =>
      wp_auto
      wp_for_post
      iframe
      iexists n + W64 1, p
      iframe
      isplitl []
      · ipureintro; constructor <;> word
      · ihave %Hel := ownSlice_len _ _ _ $$ He
        have hsn : sint.nat (n + W64 1) = sint.nat n + 1 := by unfold sint.nat at *; word
        rw [hsn, List.take_add_one, show t.cmps[sint.nat n]? = some cm from hcm, Option.toList_some]
        iapply (apply.cmpsClass_snoc on info _ cm e (by rw [Hce]; exact apply.authEndOf_rangeEndOf esl e Hel.1))
        iframe Hcc
        iapply (apply.classRes_of_permVerdict on info cm.key e .read) $$ Hv7
    | ok e' =>
      wp_auto
      wp_for_post
      iapply HΦ; iframe Hai Hrd; isplitr; (first | iexact HeI9 | iexact HeI8 | iexact HeI7 | iexact HeI6 | iexact HeI5 | iexact HeI4 | iexact HeI3 | iexact HeI2 | iexact HeI1 | iapply authApplyErrIs_nil); isplitr; (ipureintro; first | assumption | (intro _; rfl)); (iintro %h; cases h)
  wp_apply (apply.checkTxnReqs_of hPut _ le γ P f RD on RW ai info dq ssl sps t.thenOps) $$ [$Hst $Hle $Hai $Hrd $Hssl $Hss $IHT] as %err ⟨Hai, Hrd, #HeI8, %Hof8, #Hcls8⟩
  cases err with
  | ok e' =>
    wp_auto
    iapply HΦ; iframe Hai Hrd; isplitr; (first | iexact HeI9 | iexact HeI8 | iexact HeI7 | iexact HeI6 | iexact HeI5 | iexact HeI4 | iexact HeI3 | iexact HeI2 | iexact HeI1 | iapply authApplyErrIs_nil); isplitr; (ipureintro; first | assumption | (intro _; rfl)); (iintro %h; cases h)
  | nil =>
  wp_auto
  wp_apply (apply.checkTxnReqs_of hPut _ le γ P f RD on RW ai info dq fsl fps t.elseOps) $$ [$Hst $Hle $Hai $Hrd $Hfsl $Hfs $IHT] as %err ⟨Hai, Hrd, #HeI9, %Hof9, #Hcls9⟩
  iapply HΦ; iframe Hai Hrd; isplitr; (first | iexact HeI9 | iexact HeI8 | iexact HeI7 | iexact HeI6 | iexact HeI5 | iexact HeI4 | iexact HeI3 | iexact HeI2 | iexact HeI1 | iapply authApplyErrIs_nil); isplitr; (ipureintro; first | assumption | (intro _; rfl))
  iintro %Herr
  try subst Herr
  unfold apply.txnClass
  have hle : t.cmps.length ≤ sint.nat n := by unfold sint.nat at *; word
  ihave #H8 := Hcls8 $$ %rfl
  ihave #H9 := Hcls9 $$ %rfl
  iframe H8 H9
  iExactEq Hcc
  rw [List.take_of_length_le hle]

end proof

end EtcdGrove
end Perennial
