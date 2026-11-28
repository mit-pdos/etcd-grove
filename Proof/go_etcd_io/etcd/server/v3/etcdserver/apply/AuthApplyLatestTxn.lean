/-
**The auth applier's `Txn` at the latest state** (the auth plan's E2s; see `AuthApplyLatest.lean`):
`checkTxnPermission` and `checkTxnReqsPermission` (mutually recursive, by Löb induction as
`AuthLemmas.lean`) with their checks' verdicts at the latest state, and `Txn`'s outcome decided
there.

The permissions a transaction's checks see (`txnChecked`), of its wire transaction (`TxnModelW`,
E3e: until then of its `TxnModel`, where a put's `PrevKv` read could only be "either"): its
comparisons' reads, then each operation's (`opChecked`): a get's read, a put's write and, with its
`PrevKv`, read (`putPerms`), a delete's `PrevKv` read then write, a nested transaction's
recursively; each range end as the check saw it (`authEndOf`). A pass is every checked permission
granted at the latest state; a refusal one that may be checked (`txnMay`) refused there.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthApplyLatestPut
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.authApplierV3__Txn
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.CheckTxnAuth

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

namespace apply

section pure
variable [GooseExts]

/-- The comparisons' reads as the check saw them. -/
def cmpsChecked : List CmpModel → List Perm3 → Prop
  | [], L => L = []
  | cm :: cs, L => ∃ e L', authEndOf cm.rangeEnd e ∧ cmpsChecked cs L' ∧ L = (cm.key, e, .read) :: L'

mutual
/-- **The permissions a wire operation's checks see**, in order (see the file header). -/
def opChecked : txn.TxnOpW → List Perm3 → Prop
  | .get o, L => ∃ e, authEndOf o.base.rangeEnd e ∧ L = [(o.key, e, .read)]
  | .put o, L => L = putPerms o
  | .delete o, L => ∃ e, authEndOf o.base.rangeEnd e ∧
      L = (if o.base.prevKV then [(o.key, e, .read)] else []) ++ [(o.key, e, .write)]
  | .txn cs ts es, L => ∃ L1 L2 L3, cmpsChecked cs L1 ∧ opsChecked ts L2 ∧ opsChecked es L3 ∧
      L = L1 ++ (L2 ++ L3)

/-- The permissions a list of wire operations' checks see, in order. -/
def opsChecked : List txn.TxnOpW → List Perm3 → Prop
  | [], L => L = []
  | op :: ops, L => ∃ L1 L2, opChecked op L1 ∧ opsChecked ops L2 ∧ L = L1 ++ L2
end

/-- **The permissions a transaction's checks see** (`checkTxnPermission`), of its wire
transaction. -/
def txnChecked (t : txn.TxnModelW) (L : List Perm3) : Prop :=
  ∃ L1 L2 L3, cmpsChecked t.cmps L1 ∧ opsChecked t.thenOps L2 ∧ opsChecked t.elseOps L3 ∧
    L = L1 ++ (L2 ++ L3)

/-- A comparison's read the check may see. -/
def cmpsMay (cs : List CmpModel) (x : Perm3) : Prop :=
  ∃ cm ∈ cs, ∃ e, authEndOf cm.rangeEnd e ∧ x = (cm.key, e, .read)

mutual
/-- **A permission a wire operation's checks may see** (a delete's read only with its `PrevKv`). -/
def opMay : txn.TxnOpW → Perm3 → Prop
  | .get o, x => ∃ e, authEndOf o.base.rangeEnd e ∧ x = (o.key, e, .read)
  | .put o, x => x ∈ putPerms o
  | .delete o, x => ∃ e, authEndOf o.base.rangeEnd e ∧
      (x = (o.key, e, .write) ∨ (o.base.prevKV = true ∧ x = (o.key, e, .read)))
  | .txn cs ts es, x => cmpsMay cs x ∨ opsMay ts x ∨ opsMay es x

/-- A permission a list of wire operations' checks may see. -/
def opsMay : List txn.TxnOpW → Perm3 → Prop
  | [], _ => False
  | op :: ops, x => opMay op x ∨ opsMay ops x
end

/-- **A permission a transaction's checks may see**, of its wire transaction. -/
def txnMay (t : txn.TxnModelW) (x : Perm3) : Prop :=
  cmpsMay t.cmps x ∨ opsMay t.thenOps x ∨ opsMay t.elseOps x

mutual
/-- **The puts of a wire operation** (auth-lease S2): a put's, a nested transaction's both branches'
(`checkTxnReqsPermission` checks each put's lease, `checkPutAuth`). -/
def opPutsW : txn.TxnOpW → List OpFull
  | .put o => [o]
  | .txn _ ts es => opsPutsW ts ++ opsPutsW es
  | _ => []

/-- The puts of a list of wire operations, in order. -/
def opsPutsW : List txn.TxnOpW → List OpFull
  | [] => []
  | op :: ops => opPutsW op ++ opsPutsW ops
end

/-- **The puts of a wire transaction**, both branches' (`checkTxnPermission`). -/
def txnPutsW (t : txn.TxnModelW) : List OpFull := opsPutsW t.thenOps ++ opsPutsW t.elseOps

theorem opsPutsW_append (l1 l2 : List txn.TxnOpW) :
    opsPutsW (l1 ++ l2) = opsPutsW l1 ++ opsPutsW l2 := by
  induction l1 with
  | nil => simp [opsPutsW]
  | cons op ops ih => simp [opsPutsW, ih, List.append_assoc]

theorem opsPutsW_singleton (op : txn.TxnOpW) : opsPutsW [op] = opPutsW op := by
  simp [opsPutsW]

theorem opsPutsW_of_getElem (ops : List txn.TxnOpW) (i : Nat) (op : txn.TxnOpW) (o : OpFull)
    (h : ops[i]? = some op) (ho : o ∈ opPutsW op) : o ∈ opsPutsW ops := by
  induction ops generalizing i with
  | nil => simp at h
  | cons op' ops ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp [opsPutsW, ho]
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      simp [opsPutsW, ih i h]

/-- **A checkable permission refused at the latest state.** -/
def refusedMay (M : auth.AuthMode) (hs : List auth.AuthState) (ai : auth.AuthInfoM)
    (May : Perm3 → Prop) : Prop :=
  latestOk M hs (fun stl => ∃ x, May x ∧ ¬ granted1 stl ai x)

/-- **A transaction's outcome decided at the latest state** (auth-lease S2): the auth layer's rejection
with a checkable permission or a put's lease refused, or the inner chain's outcome with the checked
permissions and every put's lease granted, at the owner's item map `I`. -/
def txnOutLL (M : auth.AuthMode) (hs : List auth.AuthState) (ai : auth.AuthInfoM) (c : Chain)
    (rq : IRRModel) (log : mvcc.Log) (tw : txn.TxnModelW)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (oc : Outcome) : Prop :=
  (oc = .rejected .auth ∧ (refusedMay M hs ai (txnMay tw) ∨
      ∃ o ∈ txnPutsW tw, leaseRefusedL M hs ai I o.leaseID)) ∨
    (chainStep backendStep c rq log oc ∧ (∃ L, txnChecked tw L ∧ passedL M hs ai L) ∧
      ∀ o ∈ txnPutsW tw, leasePassedL M hs ai I o.leaseID)

theorem refusedMay_of_one (M : auth.AuthMode) (hs : List auth.AuthState) (ai : auth.AuthInfoM)
    (May : Perm3 → Prop) (x : Perm3) (hx : May x) (h : refusedL M hs ai [x]) :
    refusedMay M hs ai May := by
  cases M with
  | on γa =>
    intro stl hl
    obtain ⟨y, hy, hn⟩ := h stl hl
    simp only [List.mem_singleton] at hy
    subst hy
    exact ⟨y, hx, hn⟩
  | off => trivial
  | any => trivial

theorem refusedMay_mono (M : auth.AuthMode) (hs : List auth.AuthState) (ai : auth.AuthInfoM)
    (May May' : Perm3 → Prop) (hm : ∀ x, May x → May' x) (h : refusedMay M hs ai May) :
    refusedMay M hs ai May' := by
  cases M with
  | on γa =>
    intro stl hl
    obtain ⟨y, hy, hn⟩ := h stl hl
    exact ⟨y, hm y hy, hn⟩
  | off => trivial
  | any => trivial

/-- A refused list's permission, each of which may be checked, is a checkable one refused. -/
theorem refusedMay_of_list (M : auth.AuthMode) (hs : List auth.AuthState) (ai : auth.AuthInfoM)
    (May : Perm3 → Prop) (L : List Perm3) (hL : ∀ x ∈ L, May x) (h : refusedL M hs ai L) :
    refusedMay M hs ai May := by
  cases M with
  | on γa =>
    intro stl hl
    obtain ⟨y, hy, hn⟩ := h stl hl
    exact ⟨y, hL y hy, hn⟩
  | off => trivial
  | any => trivial

theorem cmpsChecked_snoc (l : List CmpModel) (cm : CmpModel) (L : List Perm3) (e : GoString)
    (hl : cmpsChecked l L) (he : authEndOf cm.rangeEnd e) :
    cmpsChecked (l ++ [cm]) (L ++ [(cm.key, e, .read)]) := by
  induction l generalizing L with
  | nil =>
    simp only [cmpsChecked] at hl
    subst hl
    exact ⟨e, [], he, rfl, rfl⟩
  | cons c cs ih =>
    obtain ⟨e', L', he', hL', rfl⟩ := hl
    exact ⟨e', L' ++ [(cm.key, e, .read)], he', ih L' hL', rfl⟩

theorem opsChecked_snoc (l : List txn.TxnOpW) (op : txn.TxnOpW) (L L' : List Perm3)
    (hl : opsChecked l L) (hop : opChecked op L') : opsChecked (l ++ [op]) (L ++ L') := by
  induction l generalizing L with
  | nil =>
    simp only [opsChecked] at hl
    subst hl
    refine ⟨L', [], hop, rfl, ?_⟩
    simp
  | cons c cs ih =>
    obtain ⟨L1, L2, h1, h2, rfl⟩ := hl
    refine ⟨L1, L2 ++ L', h1, ih L2 h2, ?_⟩
    simp

theorem opsMay_of_getElem (ops : List txn.TxnOpW) (i : Nat) (op : txn.TxnOpW) (x : Perm3)
    (hi : ops[i]? = some op) (hx : opMay op x) : opsMay ops x := by
  induction ops generalizing i with
  | nil => simp at hi
  | cons c cs ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      exact Or.inl hx
    | succ j =>
      simp only [List.getElem?_cons_succ] at hi
      exact Or.inr (ih j hi)

theorem cmpsMay_of_getElem (cs : List CmpModel) (i : Nat) (cm : CmpModel) (e : GoString)
    (hi : cs[i]? = some cm) (he : authEndOf cm.rangeEnd e) : cmpsMay cs (cm.key, e, .read) :=
  ⟨cm, List.mem_of_getElem? hi, e, he, rfl⟩

end pure

end apply

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **`checkTxnPermission` on the apply thread**: `checkTxnPermission.spec`'s, the lessor finding
no lease, the verdict at the latest state: a pass is the transaction's checked permissions granted,
a refusal a checkable one refused. -/
abbrev apply.checkTxnPermission.specL : Prop :=
  ∀ (st le : GoInterface) (RD : IProp GF) (on : auth.AuthMode)
    (Lr : List auth.AuthState → IProp GF) (hs : List auth.AuthState) (γl : GName) (Lw : List w64)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (ai : Loc)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (dq : DFrac) (rt : Loc) (t : txn.TxnModelW)
    (w : Option lease.LWin),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.isAuthStoreL st RD on Lr ∗ txn.isTxnLessor le γl ∗ lease.lessorUserW γl Lw I w ∗
      ai ↦{dq} info ∗ RD ∗ Lr hs ∗ txn.txnRequestIsW rt t }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.checkTxnPermission))
      (Val #st)) (Val #ai)) (Val #le)) (Val #rt))
  {{ (err : GoInterface), RET #err; lease.lessorUserW γl Lw I w ∗ ai ↦{dq} info ∗ RD ∗ Lr hs ∗
      authApplyErrIs err ∗ ⌜on.isOn = false → err = GoInterface.nil⌝ ∗
      (∀ _ : err = GoInterface.nil,
        apply.txnClass on info t.toModel ∗ apply.txnLeaseClass on info I t.toModel) ∗
      ⌜(err = GoInterface.nil → (∃ L, apply.txnChecked t L ∧
            apply.passedL on hs (auth.authInfoM info) L) ∧
          ∀ o ∈ apply.txnPutsW t, apply.leasePassedL on hs (auth.authInfoM info) I o.leaseID) ∧
        (err ≠ GoInterface.nil → apply.refusedMay on hs (auth.authInfoM info) (apply.txnMay t) ∨
          ∃ o ∈ apply.txnPutsW t, apply.leaseRefusedL on hs (auth.authInfoM info) I o.leaseID)⌝ }}

/-- **`CheckTxnAuth` on the apply thread** (`checkTxnPermission`'s). -/
abbrev apply.CheckTxnAuth.specL : Prop :=
  ∀ (st le : GoInterface) (RD : IProp GF) (on : auth.AuthMode)
    (Lr : List auth.AuthState → IProp GF) (hs : List auth.AuthState) (γl : GName) (Lw : List w64)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (ai : Loc)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (dq : DFrac) (rt : Loc) (t : txn.TxnModelW)
    (w : Option lease.LWin),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.isAuthStoreL st RD on Lr ∗ txn.isTxnLessor le γl ∗ lease.lessorUserW γl Lw I w ∗
      ai ↦{dq} info ∗ RD ∗ Lr hs ∗ txn.txnRequestIsW rt t }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.CheckTxnAuth))
      (Val #st)) (Val #ai)) (Val #le)) (Val #rt))
  {{ (err : GoInterface), RET #err; lease.lessorUserW γl Lw I w ∗ ai ↦{dq} info ∗ RD ∗ Lr hs ∗
      authApplyErrIs err ∗ ⌜on.isOn = false → err = GoInterface.nil⌝ ∗
      (∀ _ : err = GoInterface.nil,
        apply.txnClass on info t.toModel ∗ apply.txnLeaseClass on info I t.toModel) ∗
      ⌜(err = GoInterface.nil → (∃ L, apply.txnChecked t L ∧
            apply.passedL on hs (auth.authInfoM info) L) ∧
          ∀ o ∈ apply.txnPutsW t, apply.leasePassedL on hs (auth.authInfoM info) I o.leaseID) ∧
        (err ≠ GoInterface.nil → apply.refusedMay on hs (auth.authInfoM info) (apply.txnMay t) ∨
          ∃ o ∈ apply.txnPutsW t, apply.leaseRefusedL on hs (auth.authInfoM info) I o.leaseID)⌝ }}

/-- **`Txn` on the apply thread**: `Txn.spec`'s, the request's wire transaction `tw` (its `PrevKv`s,
E3e), the outcome decided at the latest state (`txnOutLL`; auth-lease S2: until then the lessor finding no
lease, without the puts' leases): the auth layer's rejection with a checkable permission or a put's lease
refused, or the inner chain's outcome with the transaction's checked permissions and its puts' leases
granted. (Strict M1, 2026-11-06: as
`Put.specL`, the thread's token in and back, the floor `kvLogLb`.) -/
abbrev apply.authApplierV3.Txn.specL : Prop :=
  ∀ (E : apply.AEnv GF) (c : apply.Chain) (inner : GoInterface) (p r : Loc) (skip : Bool)
    (rq : IRRModel) (t : TxnModel) (tw : txn.TxnModelW) (log F : mvcc.Log) (Pre Q Post : IProp GF)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (Lr : List auth.AuthState → IProp GF) (hs : List auth.AuthState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.authIs E p inner ∗ apply.authIsL E p Lr ∗ apply.applierSpec E c inner ∗
      apply.txnPreW E (.auth E.authOn c) (interface.mkOk (go.GoType.PointerType authApplierV3.ty) #p) info r rq t log Pre Q Post
        (apply.txnOutLL E.authMode hs (auth.authInfoM info) c rq log tw
          (mvcc.leaseItemsOf (mvcc.stateAfter log))) ∗
      txn.txnRequestIsW r tw ∗ ⌜rq.txnW = some tw⌝ ∗
      srvApi.kvLogLb E.γs F ∗ Lr hs ∗ apply.applyTok E }}
    (App (App (Val (p @!! go.GoType.PointerType authApplierV3.ty @!! go!"Txn")) (Val #r)) (Val #skip))
  {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
      apply.kvPostFL E (.auth E.authOn c) (interface.mkOk (go.GoType.PointerType authApplierV3.ty) #p) info rq log F
        (apply.txnAnswerIs log t skip resp err) Pre Post
        (apply.txnOutLL E.authMode hs (auth.authInfoM info) c rq log tw
          (mvcc.leaseItemsOf (mvcc.stateAfter log))) ∗
      Lr hs ∗ apply.traceRes trace ∗ apply.applyTok E }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- `checkTxnPermission`'s latest triple, as a hypothesis (the Löb induction's). -/
def apply.txnPermTL (st le : GoInterface) (RD : IProp GF) (on : auth.AuthMode)
    (Lr : List auth.AuthState → IProp GF) (hs : List auth.AuthState) (γl : GName) (Lw : List w64)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (ai : Loc)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (dq : DFrac) (w : Option lease.LWin) : IProp GF :=
  iprop(□ ∀ (rt : Loc) (t : txn.TxnModelW) (Φ : val → IProp GF),
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.isAuthStoreL st RD on Lr ∗ txn.isTxnLessor le γl ∗ lease.lessorUserW γl Lw I w ∗
      ai ↦{dq} info ∗ RD ∗ Lr hs ∗ txn.txnRequestIsW rt t -∗
    (▷ ∀ err : GoInterface, lease.lessorUserW γl Lw I w ∗ ai ↦{dq} info ∗ RD ∗ Lr hs ∗
        authApplyErrIs err ∗ ⌜on.isOn = false → err = GoInterface.nil⌝ ∗
        (∀ _ : err = GoInterface.nil,
          apply.txnClass on info t.toModel ∗ apply.txnLeaseClass on info I t.toModel) ∗
        ⌜(err = GoInterface.nil → (∃ L, apply.txnChecked t L ∧
              apply.passedL on hs (auth.authInfoM info) L) ∧
            ∀ o ∈ apply.txnPutsW t, apply.leasePassedL on hs (auth.authInfoM info) I o.leaseID) ∧
          (err ≠ GoInterface.nil → apply.refusedMay on hs (auth.authInfoM info) (apply.txnMay t) ∨
            ∃ o ∈ apply.txnPutsW t, apply.leaseRefusedL on hs (auth.authInfoM info) I o.leaseID)⌝ -∗
        Φ #err) -∗
    WP (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.checkTxnPermission))
      (Val #st)) (Val #ai)) (Val #le)) (Val #rt)) {{ Φ }})

instance apply.txnPermTL_persistent (st le : GoInterface) (RD : IProp GF) (on : auth.AuthMode)
    (Lr : List auth.AuthState → IProp GF) (hs : List auth.AuthState) (γl : GName) (Lw : List w64)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (ai : Loc)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (dq : DFrac) (w : Option lease.LWin) :
    Persistent (apply.txnPermTL st le RD on Lr hs γl Lw I ai info dq w) := by
  unfold apply.txnPermTL; infer_instance

/-- **`checkTxnReqsPermission` on the apply thread**, over `checkTxnPermission`'s latest triple. -/
theorem apply.checkTxnReqs_latest
    (hPut : apply.checkPutAuth.specL (GF := GF) (hG := hG)) :
  ∀ (st le : GoInterface) (RD : IProp GF) (on : auth.AuthMode)
    (Lr : List auth.AuthState → IProp GF) (hs : List auth.AuthState) (γl : GName) (Lw : List w64)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (ai : Loc)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (dq : DFrac) (reqs : GoSlice)
    (ps : List Loc) (ops : List txn.TxnOpW) (w : Option lease.LWin),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.isAuthStoreL st RD on Lr ∗ txn.isTxnLessor le γl ∗ lease.lessorUserW γl Lw I w ∗
      ai ↦{dq} info ∗ RD ∗ Lr hs ∗
      reqs ↦*□ ps ∗ txn.requestOpsIsW ps ops ∗ apply.txnPermTL st le RD on Lr hs γl Lw I ai info dq w }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.checkTxnReqsPermission))
      (Val #st)) (Val #ai)) (Val #le)) (Val #reqs))
  {{ (err : GoInterface), RET #err; lease.lessorUserW γl Lw I w ∗ ai ↦{dq} info ∗ RD ∗ Lr hs ∗
      authApplyErrIs err ∗ ⌜on.isOn = false → err = GoInterface.nil⌝ ∗
      (∀ _ : err = GoInterface.nil, apply.opsClass on info (txn.TxnOpW.toOps ops) ∗
        apply.opsLeaseClass on info I (txn.TxnOpW.toOps ops)) ∗
      ⌜(err = GoInterface.nil → (∃ L, apply.opsChecked ops L ∧
            apply.passedL on hs (auth.authInfoM info) L) ∧
          ∀ o ∈ apply.opsPutsW ops, apply.leasePassedL on hs (auth.authInfoM info) I o.leaseID) ∧
        (err ≠ GoInterface.nil → apply.refusedMay on hs (auth.authInfoM info) (apply.opsMay ops) ∨
          ∃ o ∈ apply.opsPutsW ops, apply.leaseRefusedL on hs (auth.authInfoM info) I o.leaseID)⌝ }} := by
  intro st le RD on Lr hs γl Lw I ai info dq reqs ps ops wn
  wp_start as ⟨#Hst, #Htl, Hu, Hai, Hrd, HL, #Hreqs, #Hops, #IH⟩
  ihave %Hsll := ownSlice_len _ _ _ $$ Hreqs
  ihave #Hst' := Hst
  iunfold apply.isAuthStoreL at Hst'
  icases Hst' with ⟨%sti, %Hsti, -, #HRange, #HDel, -⟩
  iunfold apply.permCheck3L at HRange
  iunfold apply.permCheck3L at HDel
  subst Hsti
  wp_auto
  irename «as» => Has
  ihave HI : iprop(∃ (n : w64) (q : Loc),
      "i" ∷ i_ptr ↦ n ∗ "requ" ∷ requ_ptr ↦ q ∗ "Hai" ∷ ai ↦{dq} info ∗ "Hrd" ∷ RD ∗ "HL" ∷ Lr hs ∗
      "Hu" ∷ lease.lessorUserW γl Lw I wn ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z reqs.len⌝ ∗
      "#Hlcls" ∷ apply.opsLeaseClass on info I (txn.TxnOpW.toOps (ops.take (sint.nat n))) ∗
      "%Hlpass" ∷ ⌜∀ o ∈ apply.opsPutsW (ops.take (sint.nat n)),
        apply.leasePassedL on hs (auth.authInfoM info) I o.leaseID⌝ ∗
      "#Hcls" ∷ apply.opsClass on info (txn.TxnOpW.toOps (ops.take (sint.nat n))) ∗
      "%Hpass" ∷ ⌜∃ L, apply.opsChecked (ops.take (sint.nat n)) L ∧
        apply.passedL on hs (auth.authInfoM info) L⌝) $$ [i requ Hai Hrd HL Hu]
  · iexists W64 0, _
    iframe i requ Hai Hrd HL Hu
    isplitl []
    · ipureintro
      constructor
      · decide
      · have := Hsll.2; word
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
    simp only [txn.TxnOpW.toOps]
    isplitl []
    · iapply apply.opsLeaseClass_nil
    isplitl []
    · ipureintro; intro o ho; simp [apply.opsPutsW] at ho
    isplitl []
    · iapply apply.opsClass_nil
    · ipureintro; exact ⟨[], rfl, apply.passedL_nil _ _ _⟩
  wp_for HI
  wp_if_destruct
  · obtain ⟨p, hp⟩ : ∃ p, ps[(sint.Z n).toNat]? = some p :=
      ⟨_, List.getElem?_eq_getElem (by unfold sint.nat at Hsll; word)⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z reqs.len := ⟨Hn.1, Hif⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index reqs (sint.Z n) ps DFrac.discard p Hn.1 $$ [] as -
    · iframe Hreqs; ipureintro; exact hp
    ihave ⟨%op, %hop, #Hop⟩ := txn.requestOpsIsW_elem ps ops _ p hp $$ Hops
    have hsn : sint.nat (n + W64 1) = sint.nat n + 1 := by unfold sint.nat at *; word
    have hop' : ops[sint.nat n]? = some op := hop
    obtain ⟨Lp, hLp, hLpass⟩ := Hpass
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
      wp_apply HRange $$ %ai %info %dq %ksl %esl %k %e %DFrac.discard %DFrac.discard %hs [Hai Hrd HL]
        as %err ⟨Hai, -, -, Hrd, HL, #HeI1, %Hv1, #Hpv1⟩
      · iframe; iframe #; try (ipureintro; exact Hkb)
      have Hone := apply.verdictL_one _ _ _ _ _ _ _ Hv1
      have Hoff := apply.permVerdictL_isOn _ _ _ _ _ _ _ Hv1
      cases err with
      | nil =>
        wp_auto
        wp_for_post
        iframe
        iexists n + W64 1, p
        iframe
        isplitl []
        · ipureintro; constructor <;> word
        rw [hsn, List.take_add_one, hop', Option.toList_some, txn.TxnOpW.toOps_append]
        simp only [txn.TxnOpW.toOps, txn.TxnOpW.toOp]
        isplitl []
        · iapply apply.opsLeaseClass_snoc
          iframe Hlcls
          try simp only [txn.TxnOpW.toOps, txn.TxnOpW.toOp]
          iapply apply.opLeaseClass_get
        isplitl []
        · ipureintro
          rw [apply.opsPutsW_append, apply.opsPutsW_singleton]
          intro o' ho'
          rcases List.mem_append.1 ho' with h | h
          · exact Hlpass o' h
          · simp [apply.opPutsW] at h
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
            iapply (apply.classRes_of_permVerdict on info k e .read) $$ Hpv1
        · ipureintro
          refine ⟨Lp ++ [(k, e, .read)], apply.opsChecked_snoc _ _ _ _ hLp ?_,
            apply.passedL_append _ _ _ _ _ hLpass (Hone.1 rfl)⟩
          rw [← hko]; exact ⟨e, hend, rfl⟩
      | ok e' =>
        wp_auto
        wp_for_post
        iapply HΦ; iframe Hu Hai Hrd HL HeI1
        isplitl []
        · ipureintro; intro h; exact Hoff h
        isplitl []
        · iintro %h; cases h
        ipureintro
        exact ⟨(fun h => by cases h), fun _ =>
          Or.inl (apply.refusedMay_of_one _ _ _ _ _ hmay (Hone.2 (fun h => by cases h)))⟩
    · -- a put
      iunfold txn.requestOpIsW at Hop
      icases Hop with ⟨%Hpn, %w, %r, #HR, #Hw, #Hr⟩
      ihave #Hr' := Hr
      iunfold txn.putRequestIs at Hr'
      icases Hr' with ⟨%Hrn, -⟩
      have hmays : ∀ x ∈ apply.putPerms o, apply.opsMay ops x := fun x hx =>
        apply.opsMay_of_getElem ops _ _ _ hop' hx
      wp_auto
      simp only [Hrn, decide_false]
      wp_auto
      wp_apply (hPut _ le RD on Lr hs γl Lw I ai info dq r o wn)
        $$ [$Hst $Htl $Hu $Hai $Hrd $HL $Hr] as %err ⟨Hu, Hai, Hrd, HL, #HeI2, %Hof2, #Hcls2, %Hvd⟩
      cases err with
      | nil =>
        ihave ⟨#Hpc0, #Hlk0⟩ := Hcls2 $$ %rfl
        wp_auto
        wp_for_post
        iframe
        iexists n + W64 1, p
        iframe
        isplitl []
        · ipureintro; constructor <;> word
        rw [hsn, List.take_add_one, hop', Option.toList_some, txn.TxnOpW.toOps_append]
        simp only [txn.TxnOpW.toOps, txn.TxnOpW.toOp]
        isplitl []
        · iapply apply.opsLeaseClass_snoc
          iframe Hlcls
          try simp only [txn.TxnOpW.toOps, txn.TxnOpW.toOp]
          iapply apply.opLeaseClass_put; iexact Hlk0
        isplitl []
        · ipureintro
          rw [apply.opsPutsW_append, apply.opsPutsW_singleton]
          intro o' ho'
          rcases List.mem_append.1 ho' with h | h
          · exact Hlpass o' h
          · simp only [apply.opPutsW, List.mem_singleton] at h; subst h; exact (Hvd.1 rfl).2
        isplitl []
        · iapply apply.opsClass_snoc
          iframe Hcls
          try simp only [txn.TxnOpW.toOps, txn.TxnOpW.toOp]
          iapply apply.opClass_put_of_putClass
          iexact Hpc0
        · ipureintro
          refine ⟨Lp ++ apply.putPerms o, apply.opsChecked_snoc _ _ _ _ hLp ?_,
            apply.passedL_append _ _ _ _ _ hLpass (Hvd.1 rfl).1⟩
          rfl
      | ok e' =>
        wp_auto
        wp_for_post
        iapply HΦ; iframe Hu Hai Hrd HL HeI2
        isplitl []
        · ipureintro; exact Hof2
        isplitl []
        · iintro %h; cases h
        ipureintro
        refine ⟨(fun h => by cases h), fun _ => ?_⟩
        rcases Hvd.2 (fun h => by cases h) with h | h
        · exact Or.inl (apply.refusedMay_of_list _ _ _ _ _ hmays h)
        · exact Or.inr ⟨o, apply.opsPutsW_of_getElem ops _ _ o hop' (by simp [apply.opPutsW]), h⟩
    · -- a delete
      iunfold txn.requestOpIsW at Hop
      icases Hop with ⟨%Hpn, %w, %r, #HR, #Hw, #Hr⟩
      iunfold txn.deleteRangeRequestIs at Hr
      icases Hr with ⟨%Hrn, %ksl, %esl, %k, %e, %pk, #HK, #Hk, #HE, #He, #HPK, %Ho, %Hkb⟩
      ihave %Hel := ownSlice_len _ _ _ $$ He
      have hend : apply.authEndOf o.base.rangeEnd e := by
        rw [Ho]; simp only [txn.deleteOpOf.proj_base]; exact apply.authEndOf_rangeEndOf esl e Hel.1
      have hko : o.key = k := by rw [Ho]; simp only [txn.deleteOpOf.proj_key]
      have hpk : o.base.prevKV = pk := by rw [Ho]; simp only [txn.deleteOpOf.proj_base]
      have hmayw : apply.opsMay ops (k, e, .write) :=
        apply.opsMay_of_getElem ops _ _ _ hop' (by rw [← hko]; exact ⟨e, hend, Or.inl rfl⟩)
      have hmayr : pk = true → apply.opsMay ops (k, e, .read) := fun hp =>
        apply.opsMay_of_getElem ops _ _ _ hop' (by rw [← hko]; exact ⟨e, hend, Or.inr ⟨hpk.trans hp, rfl⟩⟩)
      wp_auto
      simp only [Hrn, decide_false]
      wp_auto
      cases pk
      · wp_auto
        wp_apply HDel $$ %ai %info %dq %ksl %esl %k %e %DFrac.discard %DFrac.discard %hs [Hai Hrd HL]
          as %err ⟨Hai, -, -, Hrd, HL, #HeI3, %Hv3, #Hpv3⟩
        · iframe; iframe #; try (ipureintro; exact Hkb)
        have Hone := apply.verdictL_one _ _ _ _ _ _ _ Hv3
        have Hoff := apply.permVerdictL_isOn _ _ _ _ _ _ _ Hv3
        cases err with
        | nil =>
          wp_auto
          wp_for_post
          iframe
          iexists n + W64 1, p
          iframe
          isplitl []
          · ipureintro; constructor <;> word
          rw [hsn, List.take_add_one, hop', Option.toList_some, txn.TxnOpW.toOps_append]
          simp only [txn.TxnOpW.toOps, txn.TxnOpW.toOp]
          isplitl []
          · iapply apply.opsLeaseClass_snoc
            iframe Hlcls
            try simp only [txn.TxnOpW.toOps, txn.TxnOpW.toOp]
            iapply apply.opLeaseClass_delete
          isplitl []
          · ipureintro
            rw [apply.opsPutsW_append, apply.opsPutsW_singleton]
            intro o' ho'
            rcases List.mem_append.1 ho' with h | h
            · exact Hlpass o' h
            · simp [apply.opPutsW] at h
          isplitl []
          · iapply apply.opsClass_snoc
            iframe Hcls
            try simp only [txn.TxnOpW.toOps, txn.TxnOpW.toOp]
            iapply apply.opClass_delete
            unfold apply.deleteClass
            iexists e
            isplitl []
            · ipureintro; exact hend
            · rw [hko, hpk]; simp only [Bool.false_eq_true, ↓reduceIte]
              iapply (apply.classRes_of_permVerdict on info k e .write) $$ Hpv3
          · ipureintro
            refine ⟨Lp ++ [(k, e, .write)], apply.opsChecked_snoc _ _ _ _ hLp ?_,
              apply.passedL_append _ _ _ _ _ hLpass (Hone.1 rfl)⟩
            rw [← hko]
            refine ⟨e, hend, ?_⟩
            rw [hpk]; simp
        | ok e' =>
          wp_auto
          wp_for_post
          iapply HΦ; iframe Hu Hai Hrd HL HeI3
          isplitl []
          · ipureintro; intro h; exact Hoff h
          isplitl []
          · iintro %h; cases h
          ipureintro
          exact ⟨(fun h => by cases h), fun _ =>
            Or.inl (apply.refusedMay_of_one _ _ _ _ _ hmayw (Hone.2 (fun h => by cases h)))⟩
      wp_auto
      wp_apply HRange $$ %ai %info %dq %ksl %esl %k %e %DFrac.discard %DFrac.discard %hs [Hai Hrd HL]
        as %err ⟨Hai, -, -, Hrd, HL, #HeI4, %Hv4, #Hpv4⟩
      · iframe; iframe #; try (ipureintro; exact Hkb)
      have Honer := apply.verdictL_one _ _ _ _ _ _ _ Hv4
      have Hoffr := apply.permVerdictL_isOn _ _ _ _ _ _ _ Hv4
      cases err with
      | ok e' =>
        wp_auto
        wp_for_post
        iapply HΦ; iframe Hu Hai Hrd HL HeI4
        isplitl []
        · ipureintro; intro h; exact Hoffr h
        isplitl []
        · iintro %h; cases h
        ipureintro
        exact ⟨(fun h => by cases h), fun _ =>
          Or.inl (apply.refusedMay_of_one _ _ _ _ _ (hmayr rfl) (Honer.2 (fun h => by cases h)))⟩
      | nil =>
      wp_auto
      wp_apply HDel $$ %ai %info %dq %ksl %esl %k %e %DFrac.discard %DFrac.discard %hs [Hai Hrd HL]
        as %err ⟨Hai, -, -, Hrd, HL, #HeI5, %Hv5, #Hpv5⟩
      · iframe; iframe #; try (ipureintro; exact Hkb)
      have Honew := apply.verdictL_one _ _ _ _ _ _ _ Hv5
      have Hoffw := apply.permVerdictL_isOn _ _ _ _ _ _ _ Hv5
      cases err with
      | nil =>
        wp_auto
        wp_for_post
        iframe
        iexists n + W64 1, p
        iframe
        isplitl []
        · ipureintro; constructor <;> word
        rw [hsn, List.take_add_one, hop', Option.toList_some, txn.TxnOpW.toOps_append]
        simp only [txn.TxnOpW.toOps, txn.TxnOpW.toOp]
        isplitl []
        · iapply apply.opsLeaseClass_snoc
          iframe Hlcls
          try simp only [txn.TxnOpW.toOps, txn.TxnOpW.toOp]
          iapply apply.opLeaseClass_delete
        isplitl []
        · ipureintro
          rw [apply.opsPutsW_append, apply.opsPutsW_singleton]
          intro o' ho'
          rcases List.mem_append.1 ho' with h | h
          · exact Hlpass o' h
          · simp [apply.opPutsW] at h
        isplitl []
        · iapply apply.opsClass_snoc
          iframe Hcls
          try simp only [txn.TxnOpW.toOps, txn.TxnOpW.toOp]
          iapply apply.opClass_delete
          unfold apply.deleteClass
          iexists e
          isplitl []
          · ipureintro; exact hend
          · rw [hko, hpk]; simp only [↓reduceIte]
            iapply apply.classRes_cons
            isplitl []
            · iapply (apply.classRes_of_permVerdict on info k e .write) $$ Hpv5
            · iapply (apply.classRes_of_permVerdict on info k e .read) $$ Hpv4
        · ipureintro
          refine ⟨Lp ++ ([(k, e, .read)] ++ [(k, e, .write)]), apply.opsChecked_snoc _ _ _ _ hLp ?_,
            apply.passedL_append _ _ _ _ _ hLpass
              (apply.passedL_append _ _ _ _ _ (Honer.1 rfl) (Honew.1 rfl))⟩
          rw [← hko]
          refine ⟨e, hend, ?_⟩
          rw [hpk]; simp
      | ok e' =>
        wp_auto
        wp_for_post
        iapply HΦ; iframe Hu Hai Hrd HL HeI5
        isplitl []
        · ipureintro; intro h; exact Hoffw h
        isplitl []
        · iintro %h; cases h
        ipureintro
        exact ⟨(fun h => by cases h), fun _ =>
          Or.inl (apply.refusedMay_of_one _ _ _ _ _ hmayw (Honew.2 (fun h => by cases h)))⟩
    · -- a nested transaction
      icases txn.requestOpIsW_txn p cs ts es $$ Hop with ⟨%Hpn, %w, %r, #HR, #Hw, #Hr⟩
      ihave #Hr' := Hr
      iunfold txn.txnRequestIsW at Hr'
      icases Hr' with ⟨%Hrn, -⟩
      have hmays : ∀ x, apply.txnMay ({ cmps := cs, thenOps := ts, elseOps := es } : txn.TxnModelW) x →
          apply.opsMay ops x := fun x hx =>
        apply.opsMay_of_getElem ops _ _ _ hop' hx
      wp_auto
      simp only [Hrn, decide_false]
      wp_auto
      iunfold apply.txnPermTL at IH
      wp_apply IH $$ %r %({ cmps := cs, thenOps := ts, elseOps := es } : txn.TxnModelW) [Hu Hai Hrd HL]
        as %err ⟨Hu, Hai, Hrd, HL, #HeI6, %Hof6, #Hcls6, %Hvd6⟩
      · iframe; iframe #
      cases err with
      | nil =>
        ihave ⟨#Ht0, #Hlt0⟩ := Hcls6 $$ %rfl
        wp_auto
        wp_for_post
        iframe
        iexists n + W64 1, p
        iframe
        isplitl []
        · ipureintro; constructor <;> word
        rw [hsn, List.take_add_one, hop', Option.toList_some, txn.TxnOpW.toOps_append]
        simp only [txn.TxnOpW.toOps, txn.TxnOpW.toOp]
        isplitl []
        · iapply apply.opsLeaseClass_snoc
          iframe Hlcls
          try simp only [txn.TxnOpW.toOps, txn.TxnOpW.toOp]
          iapply apply.opLeaseClass_txn; iExactEq Hlt0; rfl
        isplitl []
        · ipureintro
          rw [apply.opsPutsW_append, apply.opsPutsW_singleton]
          intro o' ho'
          rcases List.mem_append.1 ho' with h | h
          · exact Hlpass o' h
          · exact (Hvd6.1 rfl).2 o' h
        isplitl []
        · iapply apply.opsClass_snoc
          iframe Hcls
          try simp only [txn.TxnOpW.toOps, txn.TxnOpW.toOp]
          iapply apply.opClass_txn
          iExactEq Ht0
          rfl
        · ipureintro
          obtain ⟨⟨Lt, hLt, hLtp⟩, -⟩ := Hvd6.1 rfl
          refine ⟨Lp ++ Lt, apply.opsChecked_snoc _ _ _ _ hLp ?_,
            apply.passedL_append _ _ _ _ _ hLpass hLtp⟩
          exact hLt
      | ok e' =>
        wp_auto
        wp_for_post
        iapply HΦ; iframe Hu Hai Hrd HL HeI6
        isplitl []
        · ipureintro; exact Hof6
        isplitl []
        · iintro %h; cases h
        ipureintro
        refine ⟨(fun h => by cases h), fun _ => ?_⟩
        rcases Hvd6.2 (fun h => by cases h) with h | ⟨o, ho, h⟩
        · exact Or.inl (apply.refusedMay_mono _ _ _ _ _ hmays h)
        · exact Or.inr ⟨o, apply.opsPutsW_of_getElem ops _ _ o hop' ho, h⟩
  iapply HΦ; iframe Hu Hai Hrd HL
  ihave %Hpl := txn.requestOpsIsW_length ps ops $$ Hops
  have hle : ops.length ≤ sint.nat n := by unfold sint.nat at *; word
  rw [List.take_of_length_le hle] at Hpass Hlpass
  isplitl []
  · iapply authApplyErrIs_nil
  isplitl []
  · ipureintro; intro _; rfl
  isplitl []
  · iintro %_
    isplitl []
    · iExactEq Hcls
      rw [List.take_of_length_le hle]
    · iExactEq Hlcls
      rw [List.take_of_length_le hle]
  ipureintro
  exact ⟨fun _ => ⟨Hpass, Hlpass⟩, fun h => absurd rfl h⟩

theorem apply.checkTxnPermission.wp_latest
    (hPut : apply.checkPutAuth.specL (GF := GF) (hG := hG)) :
    apply.checkTxnPermission.specL (GF := GF) (hG := hG) := by
  intro st le RD on Lr hs γl Lw I ai info dq rt t wn
  iloeb as IH generalizing %rt %t
  wp_start as ⟨#Hst, #Htl, Hu, Hai, Hrd, HL, #Hrt⟩
  ihave #IHT : apply.txnPermTL st le RD on Lr hs γl Lw I ai info dq wn $$ []
  · iunfold apply.txnPermTL; iexact IH
  iclear IH
  iunfold txn.txnRequestIsW at Hrt
  icases Hrt with ⟨%Hrtn, %csl, %ssl, %fsl, %cps, %sps, %fps, #Hc, #Hcsl, #Hcs, #Hs, #Hssl, #Hss,
    #Hf, #Hfsl, #Hfs⟩
  ihave %Hsll := ownSlice_len _ _ _ $$ Hcsl
  iunfold txn.comparesIs at Hcs
  icases Hcs with ⟨%Hcl, #Hcs⟩
  ihave #Hst' := Hst
  iunfold apply.isAuthStoreL at Hst'
  icases Hst' with ⟨%sti, %Hsti, -, #HRange, -⟩
  iunfold apply.permCheck3L at HRange
  subst Hsti
  wp_auto
  irename «as» => Has
  ihave HI : iprop(∃ (n : w64) (q : Loc),
      "i" ∷ i_ptr ↦ n ∗ "c" ∷ c_ptr ↦ q ∗ "Hai" ∷ ai ↦{dq} info ∗ "Hrd" ∷ RD ∗ "HL" ∷ Lr hs ∗
      "Hu" ∷ lease.lessorUserW γl Lw I wn ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z csl.len⌝ ∗
      "#Hcc" ∷ apply.cmpsClass on info (t.cmps.take (sint.nat n)) ∗
      "%Hpass" ∷ ⌜∃ L, apply.cmpsChecked (t.cmps.take (sint.nat n)) L ∧
        apply.passedL on hs (auth.authInfoM info) L⌝) $$ [i c Hai Hrd HL Hu]
  · iexists W64 0, _
    iframe i c Hai Hrd HL Hu
    isplitl []
    · ipureintro
      constructor
      · decide
      · have := Hsll.2; word
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
    isplitl []
    · iapply apply.cmpsClass_nil
    · ipureintro; exact ⟨[], rfl, apply.passedL_nil _ _ _⟩
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
    ihave %Hel := ownSlice_len _ _ _ $$ He
    have hend : apply.authEndOf cm.rangeEnd e := by rw [Hce]; exact apply.authEndOf_rangeEndOf esl e Hel.1
    have hmay : apply.txnMay t (cm.key, e, .read) :=
      Or.inl (apply.cmpsMay_of_getElem _ _ cm e hcm hend)
    obtain ⟨Lp, hLp, hLpass⟩ := Hpass
    wp_auto
    wp_apply HRange $$ %ai %info %dq %ksl %esl %cm.key %e %DFrac.discard %DFrac.discard %hs [Hai Hrd HL]
      as %err ⟨Hai, -, -, Hrd, HL, #HeI7, %Hv7, #Hpv7⟩
    · iframe; iframe #; try (ipureintro; exact Hkb)
    have Hone := apply.verdictL_one _ _ _ _ _ _ _ Hv7
    have Hoff := apply.permVerdictL_isOn _ _ _ _ _ _ _ Hv7
    cases err with
    | nil =>
      wp_auto
      wp_for_post
      iframe
      iexists n + W64 1, p
      iframe
      isplitl []
      · ipureintro; constructor <;> word
      have hsn : sint.nat (n + W64 1) = sint.nat n + 1 := by unfold sint.nat at *; word
      have hcm' : t.cmps[sint.nat n]? = some cm := hcm
      rw [hsn, List.take_add_one, hcm', Option.toList_some]
      isplitl []
      · iapply (apply.cmpsClass_snoc on info _ cm e hend)
        iframe Hcc
        iapply (apply.classRes_of_permVerdict on info cm.key e .read) $$ Hpv7
      · ipureintro
        exact ⟨Lp ++ [(cm.key, e, .read)], apply.cmpsChecked_snoc _ _ _ _ hLp hend,
          apply.passedL_append _ _ _ _ _ hLpass (Hone.1 rfl)⟩
    | ok e' =>
      wp_auto
      wp_for_post
      iapply HΦ; iframe Hu Hai Hrd HL HeI7
      isplitl []
      · ipureintro; intro h; exact Hoff h
      isplitl []
      · iintro %h; cases h
      ipureintro
      exact ⟨(fun h => by cases h), fun _ =>
        Or.inl (apply.refusedMay_of_one _ _ _ _ _ hmay (Hone.2 (fun h => by cases h)))⟩
  have hle : t.cmps.length ≤ sint.nat n := by unfold sint.nat at *; word
  rw [List.take_of_length_le hle] at Hpass
  wp_apply (apply.checkTxnReqs_latest hPut _ le RD on Lr hs γl Lw I ai info dq ssl sps t.thenOps wn)
    $$ [$Hst $Htl $Hu $Hai $Hrd $HL $Hssl $Hss $IHT] as %err ⟨Hu, Hai, Hrd, HL, #HeI8, %Hof8, #Hcls8, %Hvd8⟩
  cases err with
  | ok e' =>
    wp_auto
    iapply HΦ; iframe Hu Hai Hrd HL HeI8
    isplitl []
    · ipureintro; exact Hof8
    isplitl []
    · iintro %h; cases h
    ipureintro
    refine ⟨(fun h => by cases h), fun _ => ?_⟩
    rcases Hvd8.2 (fun h => by cases h) with h | ⟨o, ho, h⟩
    · exact Or.inl (apply.refusedMay_mono _ _ _ _ _ (fun x hx => Or.inr (Or.inl hx)) h)
    · exact Or.inr ⟨o, List.mem_append_left _ ho, h⟩
  | nil =>
  wp_auto
  wp_apply (apply.checkTxnReqs_latest hPut _ le RD on Lr hs γl Lw I ai info dq fsl fps t.elseOps wn)
    $$ [$Hst $Htl $Hu $Hai $Hrd $HL $Hfsl $Hfs $IHT] as %err ⟨Hu, Hai, Hrd, HL, #HeI9, %Hof9, #Hcls9, %Hvd9⟩
  iapply HΦ; iframe Hu Hai Hrd HL HeI9
  isplitl []
  · ipureintro; exact Hof9
  isplitl []
  · iintro %Herr
    try subst Herr
    ihave ⟨#H8, #HL8⟩ := Hcls8 $$ %rfl
    ihave ⟨#H9, #HL9⟩ := Hcls9 $$ %rfl
    isplitl []
    · unfold apply.txnClass
      simp only [txn.TxnModelW.toModel]
      iframe H8 H9
      iExactEq Hcc
      rw [List.take_of_length_le hle]
    · unfold apply.txnLeaseClass
      simp only [txn.TxnModelW.toModel]
      iframe HL8 HL9
  ipureintro
  constructor
  · intro herr
    obtain ⟨L1, hL1, hp1⟩ := Hpass
    obtain ⟨⟨L2, hL2, hp2⟩, hl2⟩ := Hvd8.1 rfl
    obtain ⟨⟨L3, hL3, hp3⟩, hl3⟩ := Hvd9.1 herr
    refine ⟨⟨L1 ++ (L2 ++ L3), ⟨L1, L2, L3, hL1, hL2, hL3, rfl⟩,
      apply.passedL_append _ _ _ _ _ hp1 (apply.passedL_append _ _ _ _ _ hp2 hp3)⟩, ?_⟩
    intro o ho
    rcases List.mem_append.1 ho with h | h
    · exact hl2 o h
    · exact hl3 o h
  · intro herr
    rcases Hvd9.2 herr with h | ⟨o, ho, h⟩
    · exact Or.inl (apply.refusedMay_mono _ _ _ _ _ (fun x hx => Or.inr (Or.inr hx)) h)
    · exact Or.inr ⟨o, List.mem_append_right _ ho, h⟩

theorem apply.CheckTxnAuth.wp_latest
    (hTxn : apply.checkTxnPermission.specL (GF := GF) (hG := hG)) :
    apply.CheckTxnAuth.specL (GF := GF) (hG := hG) := by
  intro st le RD on Lr hs γl Lw I ai info dq rt t wn
  wp_start as ⟨#Hst, #Htl, Hu, Hai, Hrd, HL, #Hrt⟩
  wp_auto
  wp_apply (hTxn st le RD on Lr hs γl Lw I ai info dq rt t wn) $$ [$Hst $Htl $Hu $Hai $Hrd $HL $Hrt] as %err Hai
  iapply HΦ; iexact Hai

theorem apply.authApplierV3.Txn.wp_latest
    (hTxn : apply.CheckTxnAuth.specL (GF := GF) (hG := hG)) :
    apply.authApplierV3.Txn.specL (GF := GF) (hG := hG) := by
  intro E c inner p r skip rq t tw log F Pre Q Post info Lr hs
  wp_start as ⟨#Hauth, #HauthL, #Hinner, Hpre, #Hrw, %Htw, #HF, HL, Htt⟩
  iunfold apply.authIs at Hauth
  icases Hauth with ⟨#Happ, -, ⟨%le, #Hlef, #Hle⟩, -⟩
  iunfold apply.isApplyLessor at Hle
  icases Hle with ⟨#Htl, -⟩
  iunfold apply.authIsL at HauthL
  icases HauthL with ⟨%st, #Hasf, #Hst⟩
  iunfold apply.txnPreW at Hpre
  icases Hpre with ⟨%Hk, #Hr, %Lw, %Hwn, #Hcp, Hm⟩
  icases apply.mPreAt_split_chain _ _ _ _ _ _ _ _ _ $$ Hm with ⟨Hm, Hres⟩
  ihave ⟨Hard, Hu, Hkv⟩ := apply.mPreRestAt_lend E log Lw Pre Q Post $$ Hm
  ihave ⟨Hinfo, Hres⟩ := apply.chainRes_auth_out c p inner info $$ Happ Hres
  ihave #Hin := Hinner
  iunfold apply.applierSpec at Hin
  icases Hin with ⟨%bi, %Hbi, #Ht⟩
  subst Hbi
  iunfold apply.applierTriples at Ht
  icases Ht with ⟨-, -, -, #HI, -⟩
  have hk : apply.authChecks (dispatchKind rq) = true := by rw [Hk.2.1]; rfl
  wp_auto
  have htt : t = tw.toModel := by
    have h1 : rq.txn = some tw.toModel := by rw [← apply.IRRModel.txnW_map, Htw]; rfl
    rw [Hk.1] at h1; exact Option.some.inj h1
  wp_apply (hTxn st le E.RD E.authMode Lr hs (mvcc.api.mvccLeases E.γ) Lw
      (mvcc.leaseItemsOf (mvcc.stateAfter log)) _ info (DFrac.own 1) r tw E.win)
    $$ [$Hst $Htl $Hu $Hinfo $Hard $HL $Hrw] as %err ⟨Hu, Hinfo, Hard, HL, #HeI, %Hoff, #Hcls, %Hvd⟩
  ihave Hkv := Hkv $$ Hard Hu
  cases err with
  | ok e' =>
    wp_auto
    iapply HΦ
    iframe HL Htt
    isplitl
    rotate_left
    · iapply apply.traceRes_null
    ihave Hkv := apply.mPreRest_of_at _ _ _ _ _ _ $$ Hkv
    icases apply.mPreRest_reject_cs _ _ _ _ _ $$ Hkv with ⟨Hkv, %B, Hcs⟩
    iapply apply.auth_reject_kvPostFL E E.authOn c p (.ok bi) info rq log F _ _ Pre Q Post _ hk
      (Or.inl (by cases h : E.authOn <;> first | rfl | cases Hoff h))
      (Or.inl ⟨rfl, Hvd.2 (fun h => by cases h)⟩) $$ Happ [] Hkv Hinfo Hres Hcs
    simp only [apply.txnAnswerIs, apply.txnOutcomeIs, apply.rejErrIs]
    isplitr
    · ipureintro; trivial
    · iframe HeI; ipureintro; simp
  | nil =>
  wp_auto
  ihave ⟨#Hcls, #Hlcls⟩ := Hcls $$ %rfl
  ihave #Hcls' : apply.txnClass E.authMode info t $$ []
  · rw [htt]; iexact Hcls
  ihave #Hlcls' : apply.txnLeaseClass E.authMode info (mvcc.leaseItemsOf (mvcc.stateAfter log)) t $$ []
  · rw [htt]; iexact Hlcls
  ihave #Hrc := apply.reqClass_txn E.authMode info rq t Hk.1 Hk.2.1 $$ Hcls'
  ihave #Hrl := apply.reqLeaseClass_txn E.authMode info _ rq t Hk.1 Hk.2.1 $$ Hlcls'
  ihave #Hcp := apply.certPreW_innerT E E.authOn c rq log Lw
    (apply.txnOutLL E.authMode hs (auth.authInfoM info) c rq log tw
          (mvcc.leaseItemsOf (mvcc.stateAfter log)))
    (fun oc hoc => Or.inr ⟨hoc, Hvd.1 rfl⟩) $$ Hcp
  have Hwn' := And.intro (Hwn.1 (apply.pass_exists c rq log _ (apply.backendStep_exists_txn rq log t Hk.1 Hk.2.1)
    (fun oc hoc => Or.inr ⟨hoc, Hvd.1 rfl⟩))) Hwn.2
  iunfold apply.chainResAny at Hres
  icases Hres with ⟨%info', Hres⟩
  wp_apply HI $$ %r %skip %rq %t %log %F %Pre %Q %Post %info' [Htt Hkv Hres] as %resp %trace %err ⟨Hpost, Htrc, Htt⟩
  · iframe Htt
    iunfold apply.txnPre
    iframe #
    isplitr
    · ipureintro; exact Hk
    isplitr
    · ipureintro; exact Hwn'
    iapply apply.mPreAt_of_rest
    iframe
  iapply HΦ
  iframe HL Htt
  isplitr [Htrc]
  rotate_left
  · iexact Htrc
  iapply apply.auth_pass_kvPostFL E E.authOn c p (.ok bi) info info' rq log F _ Pre Post
    (apply.txnOutLL E.authMode hs (auth.authInfoM info) c rq log tw
          (mvcc.leaseItemsOf (mvcc.stateAfter log)))
    (fun oc hoc => Or.inr ⟨hoc, Hvd.1 rfl⟩) $$ Happ Hpost Hinfo Hrc Hrl

end proof

end EtcdGrove
end Perennial
