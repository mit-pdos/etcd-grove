/-
**A read-only transaction's checks no older than a reader's lower bound** (the auth plan's E3m,
2026-10-27; `notes/decisions.md`, "E3m of the auth plan"). Lean-first (no Rocq counterpart).

The read path checks a read-only transaction with `CheckTxnAuth` (`v3_server.go`'s `Txn`: the
`doSerialize` check `apply2.CheckTxnAuth(s.authStore, ai, s.lessor, r)`), outside the apply
thread. A read-only transaction (`txn.IsTxnReadonly`: every operation of both branches a range)
makes only `IsRangePermitted` checks: its comparisons' reads, then its gets'. Each check reads the
store afresh, so for a reader holding a lower bound `n` of the published index (`authPubLbM`, E3g)
each check's verdict is `IsRangePermitted.specLb`'s (E3j), at states no older than `n`
(`auth.permVerdictFrom`), each check possibly at a different state: a pass is every checked
permission's verdict passed (`verdictsFrom`), a refusal one checkable permission's verdict refused.

No induction is needed (unlike E2s's latest-state proof, `AuthApplyLatestTxn.lean`): a read-only
transaction has no nested transaction (a nested transaction is not a range), and its puts' and
deletes' branches are dead.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthApplyLatestTxn
public import Proof.go_etcd_io.etcd.server.v3.auth.FreshWrap

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3 go_etcd_io.etcd.server.v3.etcdserver.apply
  go_etcd_io.etcd.api.v3

namespace apply

section pure
variable [GooseExts]

/-- A wire operation is a get (a range request). -/
def opW_isGet : txn.TxnOpW → Bool
  | .get _ => true
  | _ => false

/-- **A read-only wire transaction** (`txn.IsTxnReadonly`): every operation of both branches a
get. -/
def readonlyW (t : txn.TxnModelW) : Prop :=
  ∀ op ∈ t.thenOps ++ t.elseOps, opW_isGet op = true

theorem opIsGet_toOp (op : txn.TxnOpW) : txn.opIsGet op.toOp = opW_isGet op := by
  cases op with
  | get o => rfl
  | put o =>
    unfold txn.TxnOpW.toOp txn.putTxnOp
    by_cases h1 : o.ignoreValue = true <;> by_cases h2 : o.ignoreLease = true <;>
      simp [h1, h2, txn.opIsGet, opW_isGet]
  | delete o => rfl
  | txn cs ts es => rfl

/-- The model's read-only transaction (`txnReadonly`, what `IsTxnReadonly` computes) is a read-only
wire transaction. -/
theorem readonlyW_of_txnReadonly (t : txn.TxnModelW) (h : txn.txnReadonly t.toModel = true) :
    readonlyW t := by
  intro op hop
  unfold txn.txnReadonly txn.TxnModelW.toModel at h
  simp only [txn.TxnOpW.toOps_eq_map, List.all_eq_true, List.mem_append, List.mem_map] at h
  rw [← opIsGet_toOp]
  rcases List.mem_append.1 hop with hop | hop
  · exact h _ (Or.inl ⟨op, hop, rfl⟩)
  · exact h _ (Or.inr ⟨op, hop, rfl⟩)

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`permCheck3` no older than a lower bound**: the check's verdict at states no older than `n`
(`auth.permVerdictFrom`), for a caller with the reader resource `RD`. -/
def permCheck3Lb (ai : GoInterfaceOk) (m : GoString) (RD : IProp GF) (M : auth.AuthMode) (n : Nat)
    (op : auth.PermType) : IProp GF :=
  iprop(□ (∀ (a : Loc) (info : auth.AuthInfo) (dq : DFrac) (key re : GoSlice) (k e : List w8)
      (dk de : DFrac),
    {{ a ↦{dq} info ∗ key ↦*{dk} k ∗ re ↦*{de} e ∗ RD ∗ ⌜sint.Z key.len < 2 ^ 63 - 1⌝ }}
      (App (App (App (Val #(methods ai.ty m ai.v)) (Val #a)) (Val #key)) (Val #re))
    {{ (err : GoInterface), RET #err; a ↦{dq} info ∗ key ↦*{dk} k ∗ re ↦*{de} e ∗ RD ∗
        authApplyErrIs err ∗ auth.permVerdictFrom M n info k e op err }}))

/-- **The auth store's range check no older than a reader's lower bound `n`** (the read path's
store: `IsRangePermitted.specLb`). -/
def isAuthStoreRangeLb (st : GoInterface) (RD : IProp GF) (M : auth.AuthMode) (n : Nat) :
    IProp GF :=
  iprop(∃ ai : GoInterfaceOk, ⌜st = GoInterface.ok ai⌝ ∗
    permCheck3Lb ai go!"IsRangePermitted" RD M n .read)

instance isAuthStoreRangeLb_persistent (st : GoInterface) (RD : IProp GF) (M : auth.AuthMode)
    (n : Nat) : Persistent (isAuthStoreRangeLb st RD M n) := by
  unfold isAuthStoreRangeLb permCheck3Lb; infer_instance

/-- **Every permission's verdict passed no older than `n`** (each check at its own state). -/
def verdictsFrom (M : auth.AuthMode) (n : Nat) (info : auth.AuthInfo) (L : List Perm3) :
    IProp GF :=
  iprop([∗list] x ∈ L, auth.permVerdictFrom M n info x.1 x.2.1 x.2.2 GoInterface.nil)

instance verdictsFrom_persistent (M : auth.AuthMode) (n : Nat) (info : auth.AuthInfo)
    (L : List Perm3) : Persistent (verdictsFrom (GF := GF) M n info L) := by
  unfold verdictsFrom; infer_instance

theorem verdictsFrom_nil (M : auth.AuthMode) (n : Nat) (info : auth.AuthInfo) :
    ⊢ verdictsFrom (GF := GF) M n info [] := by
  unfold verdictsFrom
  iapply BigSepL.bigSepL_nil.2
  iempintro

theorem verdictsFrom_snoc (M : auth.AuthMode) (n : Nat) (info : auth.AuthInfo) (L : List Perm3)
    (k e : GoString) (op : auth.PermType) :
    verdictsFrom (GF := GF) M n info L ∗ auth.permVerdictFrom M n info k e op GoInterface.nil ⊢
      verdictsFrom M n info (L ++ [(k, e, op)]) := by
  unfold verdictsFrom
  iintro ⟨H1, H2⟩
  iapply BigSepL.bigSepL_snoc.2
  iframe H1 H2

theorem verdictsFrom_append (M : auth.AuthMode) (n : Nat) (info : auth.AuthInfo)
    (L1 L2 : List Perm3) :
    verdictsFrom (GF := GF) M n info L1 ∗ verdictsFrom M n info L2 ⊢
      verdictsFrom M n info (L1 ++ L2) := by
  unfold verdictsFrom
  iintro ⟨H1, H2⟩
  iapply BigSepL.bigSepL_append.2
  iframe H1 H2

/-- A check's verdict in the mode `off` is a pass. -/
theorem permVerdictFrom_isOn (M : auth.AuthMode) (n : Nat) (info : auth.AuthInfo)
    (k e : GoString) (op : auth.PermType) (err : GoInterface) :
    auth.permVerdictFrom (GF := GF) M n info k e op err ⊢ ⌜M.isOn = false → err = GoInterface.nil⌝ := by
  cases M with
  | off => unfold auth.permVerdictFrom; iintro %h; ipureintro; intro _; exact h
  | on γa => iintro -; ipureintro; intro h; cases h
  | any => iintro -; ipureintro; intro h; cases h

end defs

end apply

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **The real store's range check no older than a reader's lower bound** (E3j's
`IsRangePermitted.specLb`), with the reader resource `auth.authRd st R M`. -/
theorem apply.isAuthStoreRangeLb_of_authInv
    (hRange : auth.authStore.IsRangePermitted.specLb (GF := GF) (hG := hG))
    (st : Loc) (R : IProp GF) (M : auth.AuthMode) (n : Nat) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ auth.authInv st R M ∗
      auth.authPubLbM M n ⊢
      apply.isAuthStoreRangeLb (auth.authIface st) (auth.authRd st R M) M n := by
  iintro ⟨#Hpkg, #Hinv, #Hlb⟩
  iunfold apply.isAuthStoreRangeLb
  iexists (interface.mk (go.GoType.PointerType auth.authStore.ty) #st)
  isplitr
  · ipureintro; rfl
  iunfold apply.permCheck3Lb
  iintro !> %a %info %dq %key %re %k %e %dk %de %Φ !> ⟨Ha, Hk, He, Hrd, %Hlen⟩ HΦ
  iapply (hRange st R M n a info dq key re k e dk de) $$ [Ha Hk He Hrd]
  · iframe; iframe #; ipureintro; exact Hlen
  iintro !> %err ⟨Hrd, Ha, Hk, He, #Herr, #Hv⟩
  iapply HΦ
  iframe
  iframe #
  iapply apply.authErrIs_authApplyErrIs err $$ [$Hpkg $Herr]

/-- **`checkTxnReqsPermission` of a read-only branch no older than a lower bound**: every
operation a get, each get's read checked at states no older than `n`. -/
theorem apply.checkTxnReqs_lb :
  ∀ (st le : GoInterface) (RD : IProp GF) (on : auth.AuthMode) (n : Nat) (ai : Loc)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (dq : DFrac) (reqs : GoSlice)
    (ps : List Loc) (ops : List txn.TxnOpW),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.isAuthStoreRangeLb st RD on n ∗ ai ↦{dq} info ∗ RD ∗
      reqs ↦*□ ps ∗ txn.requestOpsIsW ps ops ∗ ⌜∀ op ∈ ops, apply.opW_isGet op = true⌝ }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.checkTxnReqsPermission))
      (Val #st)) (Val #ai)) (Val #le)) (Val #reqs))
  {{ (err : GoInterface), RET #err; ai ↦{dq} info ∗ RD ∗ authApplyErrIs err ∗
      ⌜on.isOn = false → err = GoInterface.nil⌝ ∗
      (∀ _ : err = GoInterface.nil, apply.opsClass on info (txn.TxnOpW.toOps ops)) ∗
      (∀ _ : err = GoInterface.nil, ∃ L, ⌜apply.opsChecked ops L⌝ ∗ apply.verdictsFrom on n info L) ∗
      (∀ _ : err ≠ GoInterface.nil, ∃ x : apply.Perm3, ⌜apply.opsMay ops x⌝ ∗
        auth.permVerdictFrom on n info x.1 x.2.1 x.2.2 err) }} := by
  intro st le RD on n ai info dq reqs ps ops
  wp_start as ⟨#Hst, Hai, Hrd, #Hreqs, #Hops, %Hro⟩
  ihave %Hsll := ownSlice_len _ _ _ $$ Hreqs
  ihave #Hst' := Hst
  iunfold apply.isAuthStoreRangeLb at Hst'
  icases Hst' with ⟨%sti, %Hsti, #HRange⟩
  iunfold apply.permCheck3Lb at HRange
  subst Hsti
  wp_auto
  irename «as» => Has
  ihave HI : iprop(∃ (m : w64) (q : Loc),
      "i" ∷ i_ptr ↦ m ∗ "requ" ∷ requ_ptr ↦ q ∗ "Hai" ∷ ai ↦{dq} info ∗ "Hrd" ∷ RD ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z m ∧ sint.Z m ≤ sint.Z reqs.len⌝ ∗
      "#Hcls" ∷ apply.opsClass on info (txn.TxnOpW.toOps (ops.take (sint.nat m))) ∗
      "#Hvs" ∷ (∃ L, ⌜apply.opsChecked (ops.take (sint.nat m)) L⌝ ∗ apply.verdictsFrom on n info L))
      $$ [i requ Hai Hrd]
  · iexists W64 0, _
    iframe i requ Hai Hrd
    isplitl []
    · ipureintro
      constructor
      · decide
      · have := Hsll.2; word
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
    simp only [txn.TxnOpW.toOps]
    isplitl []
    · iapply apply.opsClass_nil
    · iexists []
      isplitl []
      · ipureintro; rfl
      · iapply apply.verdictsFrom_nil
  wp_for HI
  wp_if_destruct
  · obtain ⟨p, hp⟩ : ∃ p, ps[(sint.Z m).toNat]? = some p :=
      ⟨_, List.getElem?_eq_getElem (by unfold sint.nat at Hsll; word)⟩
    have Hbnd : 0 ≤ sint.Z m ∧ sint.Z m < sint.Z reqs.len := ⟨Hn.1, Hif⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index reqs (sint.Z m) ps DFrac.discard p Hn.1 $$ [] as -
    · iframe Hreqs; ipureintro; exact hp
    ihave ⟨%op, %hop, #Hop⟩ := txn.requestOpsIsW_elem ps ops _ p hp $$ Hops
    have hsn : sint.nat (m + W64 1) = sint.nat m + 1 := by unfold sint.nat at *; word
    have hop' : ops[sint.nat m]? = some op := hop
    have hget : apply.opW_isGet op = true := Hro op (List.mem_of_getElem? hop')
    icases Hvs with ⟨%Lp, %hLp, #HLp⟩
    rcases op with o | o | o | ⟨cs, ts, es⟩
    · -- a range
      iunfold txn.requestOpIsW at Hop
      icases Hop with ⟨%Hpn, %w, %r, #HR, #Hw, #Hr⟩
      iunfold txn.rangeRequestIs at Hr
      icases Hr with ⟨%Hrn, %ksl, %esl, %k, %e, %x1, %x2, %x3, %x4, %x5, %x6, %x7, %x8, %x9, %x10,
        %x11, #HK, #Hk, #HE, #He, -, -, -, -, -, -, -, -, -, -, -, %Ho, %Hkb⟩
      ihave %Hel := ownSlice_len _ _ _ $$ He
      have hend : apply.authEndOf o.base.rangeEnd e := by
        rw [Ho]; simp only [txn.rangeOpOf.proj_base]; exact apply.authEndOf_rangeEndOf esl e Hel.1
      have hko : o.key = k := by rw [Ho]; simp only [txn.rangeOpOf.proj_key]
      have hmay : apply.opsMay ops (k, e, .read) :=
        apply.opsMay_of_getElem ops _ _ _ hop' (by rw [← hko]; exact ⟨e, hend, rfl⟩)
      wp_auto
      simp only [Hrn, decide_false]
      wp_auto
      wp_apply HRange $$ %ai %info %dq %ksl %esl %k %e %DFrac.discard %DFrac.discard [Hai Hrd]
        as %err ⟨Hai, -, -, Hrd, #HeI1, #Hpv1⟩
      · iframe; iframe #; ipureintro; exact Hkb
      ihave %Hoff := apply.permVerdictFrom_isOn on n info k e .read err $$ Hpv1
      cases err with
      | nil =>
        wp_auto
        wp_for_post
        iframe
        iexists m + W64 1, p
        iframe
        isplitl []
        · ipureintro; constructor <;> word
        rw [hsn, List.take_add_one, hop', Option.toList_some, txn.TxnOpW.toOps_append]
        simp only [txn.TxnOpW.toOps, txn.TxnOpW.toOp]
        isplitl []
        · iapply apply.opsClass_snoc
          iframe Hcls
          try simp only [txn.TxnOpW.toOps, txn.TxnOpW.toOp]
          iapply apply.opClass_get
          unfold apply.rangeClass
          iexists e
          isplitl []
          · ipureintro; exact hend
          · rw [hko]
            iapply (apply.classRes_of_permVerdict on info k e .read)
            iapply (auth.permVerdictFrom_verdict on n info k e .read GoInterface.nil) $$ Hpv1
        · iexists Lp ++ [(k, e, .read)]
          isplitl []
          · ipureintro
            exact apply.opsChecked_snoc _ _ _ _ hLp (by rw [← hko]; exact ⟨e, hend, rfl⟩)
          · iapply apply.verdictsFrom_snoc
            iframe HLp Hpv1
      | ok e' =>
        wp_auto
        wp_for_post
        iapply HΦ; iframe Hai Hrd HeI1
        isplitl []
        · ipureintro; exact Hoff
        isplitl []
        · iintro %h; cases h
        isplitl []
        · iintro %h; cases h
        iintro %_
        iexists (k, e, .read)
        iframe Hpv1
        ipureintro; exact hmay
    all_goals exact absurd hget (by simp [apply.opW_isGet])
  iapply HΦ; iframe Hai Hrd
  ihave %Hpl := txn.requestOpsIsW_length ps ops $$ Hops
  have hle : ops.length ≤ sint.nat m := by unfold sint.nat at *; word
  icases Hvs with ⟨%Lp, %hLp, #HLp⟩
  rw [List.take_of_length_le hle] at hLp
  isplitl []
  · iapply authApplyErrIs_nil
  isplitl []
  · ipureintro; intro _; rfl
  isplitl []
  · iintro %_
    iExactEq Hcls
    rw [List.take_of_length_le hle]
  isplitl []
  · iintro %_
    iexists Lp
    iframe HLp
    ipureintro; exact hLp
  · iintro %h; exact absurd rfl h

/-- **`checkTxnPermission` of a read-only transaction no older than a reader's lower bound** (the
read path's `CheckTxnAuth`, see the file header): a pass is each checked permission's verdict
passed at states no older than `n`; a refusal one checkable permission's verdict refused there. -/
abbrev apply.checkTxnPermission.specLb : Prop :=
  ∀ (st le : GoInterface) (RD : IProp GF) (on : auth.AuthMode) (n : Nat) (ai : Loc)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (dq : DFrac) (rt : Loc) (t : txn.TxnModelW),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.isAuthStoreRangeLb st RD on n ∗ ai ↦{dq} info ∗ RD ∗
      txn.txnRequestIsW rt t ∗ ⌜apply.readonlyW t⌝ }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.checkTxnPermission))
      (Val #st)) (Val #ai)) (Val #le)) (Val #rt))
  {{ (err : GoInterface), RET #err; ai ↦{dq} info ∗ RD ∗ authApplyErrIs err ∗
      ⌜on.isOn = false → err = GoInterface.nil⌝ ∗
      (∀ _ : err = GoInterface.nil, apply.txnClass on info t.toModel) ∗
      (∀ _ : err = GoInterface.nil, ∃ L, ⌜apply.txnChecked t L⌝ ∗ apply.verdictsFrom on n info L) ∗
      (∀ _ : err ≠ GoInterface.nil, ∃ x : apply.Perm3, ⌜apply.txnMay t x⌝ ∗
        auth.permVerdictFrom on n info x.1 x.2.1 x.2.2 err) }}

/-- **`CheckTxnAuth` of a read-only transaction no older than a reader's lower bound**
(`checkTxnPermission`'s). -/
abbrev apply.CheckTxnAuth.specLb : Prop :=
  ∀ (st le : GoInterface) (RD : IProp GF) (on : auth.AuthMode) (n : Nat) (ai : Loc)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (dq : DFrac) (rt : Loc) (t : txn.TxnModelW),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.isAuthStoreRangeLb st RD on n ∗ ai ↦{dq} info ∗ RD ∗
      txn.txnRequestIsW rt t ∗ ⌜apply.readonlyW t⌝ }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.CheckTxnAuth))
      (Val #st)) (Val #ai)) (Val #le)) (Val #rt))
  {{ (err : GoInterface), RET #err; ai ↦{dq} info ∗ RD ∗ authApplyErrIs err ∗
      ⌜on.isOn = false → err = GoInterface.nil⌝ ∗
      (∀ _ : err = GoInterface.nil, apply.txnClass on info t.toModel) ∗
      (∀ _ : err = GoInterface.nil, ∃ L, ⌜apply.txnChecked t L⌝ ∗ apply.verdictsFrom on n info L) ∗
      (∀ _ : err ≠ GoInterface.nil, ∃ x : apply.Perm3, ⌜apply.txnMay t x⌝ ∗
        auth.permVerdictFrom on n info x.1 x.2.1 x.2.2 err) }}

theorem apply.checkTxnPermission.wp_lb :
    apply.checkTxnPermission.specLb (GF := GF) (hG := hG) := by
  intro st le RD on n ai info dq rt t
  wp_start as ⟨#Hst, Hai, Hrd, #Hrt, %Hro⟩
  iunfold txn.txnRequestIsW at Hrt
  icases Hrt with ⟨%Hrtn, %csl, %ssl, %fsl, %cps, %sps, %fps, #Hc, #Hcsl, #Hcs, #Hs, #Hssl, #Hss,
    #Hf, #Hfsl, #Hfs⟩
  ihave %Hsll := ownSlice_len _ _ _ $$ Hcsl
  iunfold txn.comparesIs at Hcs
  icases Hcs with ⟨%Hcl, #Hcs⟩
  ihave #Hst' := Hst
  iunfold apply.isAuthStoreRangeLb at Hst'
  icases Hst' with ⟨%sti, %Hsti, #HRange⟩
  iunfold apply.permCheck3Lb at HRange
  subst Hsti
  wp_auto
  irename «as» => Has
  ihave HI : iprop(∃ (m : w64) (q : Loc),
      "i" ∷ i_ptr ↦ m ∗ "c" ∷ c_ptr ↦ q ∗ "Hai" ∷ ai ↦{dq} info ∗ "Hrd" ∷ RD ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z m ∧ sint.Z m ≤ sint.Z csl.len⌝ ∗
      "#Hcc" ∷ apply.cmpsClass on info (t.cmps.take (sint.nat m)) ∗
      "#Hvs" ∷ (∃ L, ⌜apply.cmpsChecked (t.cmps.take (sint.nat m)) L⌝ ∗
        apply.verdictsFrom on n info L)) $$ [i c Hai Hrd]
  · iexists W64 0, _
    iframe i c Hai Hrd
    isplitl []
    · ipureintro
      constructor
      · decide
      · have := Hsll.2; word
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
    isplitl []
    · iapply apply.cmpsClass_nil
    · iexists []
      isplitl []
      · ipureintro; rfl
      · iapply apply.verdictsFrom_nil
  wp_for HI
  wp_if_destruct
  · obtain ⟨p, hp⟩ : ∃ p, cps[(sint.Z m).toNat]? = some p :=
      ⟨_, List.getElem?_eq_getElem (by unfold sint.nat at Hsll; word)⟩
    obtain ⟨cm, hcm⟩ : ∃ cm, (t.cmps)[(sint.Z m).toNat]? = some cm :=
      ⟨_, List.getElem?_eq_getElem (by unfold sint.nat at Hsll; word)⟩
    have Hbnd : 0 ≤ sint.Z m ∧ sint.Z m < sint.Z csl.len := ⟨Hn.1, Hif⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index csl (sint.Z m) cps DFrac.discard p Hn.1 $$ [] as -
    · iframe Hcsl; ipureintro; exact hp
    ihave #Hp := Hcs $$ %_ %p %cm [] []
    · ipureintro; exact hp
    · ipureintro; exact hcm
    iunfold txn.compareIs at Hp
    icases Hp with ⟨%Hpn, %ksl, %esl, %e, %u, -, -, #HK, #Hk, #HE, #He, %Hce, -, -, -, %Hkb⟩
    ihave %Hel := ownSlice_len _ _ _ $$ He
    have hend : apply.authEndOf cm.rangeEnd e := by rw [Hce]; exact apply.authEndOf_rangeEndOf esl e Hel.1
    have hmay : apply.txnMay t (cm.key, e, .read) :=
      Or.inl (apply.cmpsMay_of_getElem _ _ cm e hcm hend)
    icases Hvs with ⟨%Lp, %hLp, #HLp⟩
    wp_auto
    wp_apply HRange $$ %ai %info %dq %ksl %esl %cm.key %e %DFrac.discard %DFrac.discard [Hai Hrd]
      as %err ⟨Hai, -, -, Hrd, #HeI7, #Hpv7⟩
    · iframe; iframe #; ipureintro; exact Hkb
    ihave %Hoff := apply.permVerdictFrom_isOn on n info cm.key e .read err $$ Hpv7
    cases err with
    | nil =>
      wp_auto
      wp_for_post
      iframe
      iexists m + W64 1, p
      iframe
      isplitl []
      · ipureintro; constructor <;> word
      have hsn : sint.nat (m + W64 1) = sint.nat m + 1 := by unfold sint.nat at *; word
      have hcm' : t.cmps[sint.nat m]? = some cm := hcm
      rw [hsn, List.take_add_one, hcm', Option.toList_some]
      isplitl []
      · iapply (apply.cmpsClass_snoc on info _ cm e hend)
        iframe Hcc
        iapply (apply.classRes_of_permVerdict on info cm.key e .read)
        iapply (auth.permVerdictFrom_verdict on n info cm.key e .read GoInterface.nil) $$ Hpv7
      · iexists Lp ++ [(cm.key, e, .read)]
        isplitl []
        · ipureintro; exact apply.cmpsChecked_snoc _ _ _ _ hLp hend
        · iapply apply.verdictsFrom_snoc
          iframe HLp Hpv7
    | ok e' =>
      wp_auto
      wp_for_post
      iapply HΦ; iframe Hai Hrd HeI7
      isplitl []
      · ipureintro; exact Hoff
      isplitl []
      · iintro %h; cases h
      isplitl []
      · iintro %h; cases h
      iintro %_
      iexists (cm.key, e, .read)
      iframe Hpv7
      ipureintro; exact hmay
  have hle : t.cmps.length ≤ sint.nat m := by unfold sint.nat at *; word
  icases Hvs with ⟨%L1, %hL1, #HL1⟩
  rw [List.take_of_length_le hle] at hL1
  have hrot : ∀ op ∈ t.thenOps, apply.opW_isGet op = true := fun op h =>
    Hro op (List.mem_append_left _ h)
  have hroe : ∀ op ∈ t.elseOps, apply.opW_isGet op = true := fun op h =>
    Hro op (List.mem_append_right _ h)
  wp_apply (apply.checkTxnReqs_lb _ le RD on n ai info dq ssl sps t.thenOps)
    $$ [$Hst $Hai $Hrd $Hssl $Hss] as %err ⟨Hai, Hrd, #HeI8, %Hof8, #Hcls8, #Hpass8, #Href8⟩
  · ipureintro; exact hrot
  cases err with
  | ok e' =>
    wp_auto
    iapply HΦ; iframe Hai Hrd HeI8
    isplitl []
    · ipureintro; exact Hof8
    isplitl []
    · iintro %h; cases h
    isplitl []
    · iintro %h; cases h
    iintro %_
    ihave ⟨%x, %hx, #Hx⟩ := Href8 $$ %(fun h => by cases h)
    iexists x
    iframe Hx
    ipureintro; exact Or.inr (Or.inl hx)
  | nil =>
  wp_auto
  wp_apply (apply.checkTxnReqs_lb _ le RD on n ai info dq fsl fps t.elseOps)
    $$ [$Hst $Hai $Hrd $Hfsl $Hfs] as %err ⟨Hai, Hrd, #HeI9, %Hof9, #Hcls9, #Hpass9, #Href9⟩
  · ipureintro; exact hroe
  iapply HΦ; iframe Hai Hrd HeI9
  isplitl []
  · ipureintro; exact Hof9
  isplitl []
  · iintro %Herr
    try subst Herr
    unfold apply.txnClass
    simp only [txn.TxnModelW.toModel]
    ihave #H8 := Hcls8 $$ %rfl
    ihave #H9 := Hcls9 $$ %rfl
    iframe H8 H9
    iExactEq Hcc
    rw [List.take_of_length_le hle]
  isplitl []
  · iintro %herr
    ihave ⟨%L2, %hL2, #HL2⟩ := Hpass8 $$ %rfl
    ihave ⟨%L3, %hL3, #HL3⟩ := Hpass9 $$ %herr
    iexists L1 ++ (L2 ++ L3)
    isplitl []
    · ipureintro; exact ⟨L1, L2, L3, hL1, hL2, hL3, rfl⟩
    · iapply apply.verdictsFrom_append
      iframe HL1
      iapply apply.verdictsFrom_append
      iframe HL2 HL3
  · iintro %herr
    ihave ⟨%x, %hx, #Hx⟩ := Href9 $$ %herr
    iexists x
    iframe Hx
    ipureintro; exact Or.inr (Or.inr hx)

theorem apply.CheckTxnAuth.wp_lb
    (hTxn : apply.checkTxnPermission.specLb (GF := GF) (hG := hG)) :
    apply.CheckTxnAuth.specLb (GF := GF) (hG := hG) := by
  intro st le RD on n ai info dq rt t
  wp_start as ⟨#Hst, Hai, Hrd, #Hrt, %Hro⟩
  wp_auto
  wp_apply (hTxn st le RD on n ai info dq rt t) $$ [$Hst $Hai $Hrd $Hrt] as %err Hai
  · ipureintro; exact Hro
  iapply HΦ; iexact Hai

end proof

end EtcdGrove
end Perennial
