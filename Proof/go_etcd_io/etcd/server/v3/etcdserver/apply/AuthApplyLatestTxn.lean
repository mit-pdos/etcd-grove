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
variable [ext : FfiSyntax]

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

/-- **The checkable permissions are of the cache's shape whenever auth is enabled** at the latest
state. -/
def shapedMay (M : auth.AuthMode) (hs : List auth.AuthState) (May : Perm3 → Prop) : Prop :=
  latestOk M hs (fun stl => stl.enabled = true → ∀ x, May x → auth.reqShape x.1 x.2.1)

/-- **A checkable permission refused at the latest state.** -/
def refusedMay (M : auth.AuthMode) (hs : List auth.AuthState) (ai : auth.AuthInfoM)
    (May : Perm3 → Prop) : Prop :=
  latestOk M hs (fun stl => ∃ x, May x ∧ ¬ granted1 stl ai x)

theorem shapedMay_one (M : auth.AuthMode) (hs : List auth.AuthState) (May : Perm3 → Prop)
    (x : Perm3) (h : shapedMay M hs May) (hx : May x) : shapedL M hs [x] := by
  cases M with
  | on γa =>
    intro stl hl hen y hy
    simp only [List.mem_singleton] at hy
    subst hy
    exact h stl hl hen y hx
  | off => trivial
  | any => trivial

theorem shapedMay_mono (M : auth.AuthMode) (hs : List auth.AuthState) (May May' : Perm3 → Prop)
    (hm : ∀ x, May' x → May x) (h : shapedMay M hs May) : shapedMay M hs May' := by
  cases M with
  | on γa => intro stl hl hen x hx; exact h stl hl hen x (hm x hx)
  | off => trivial
  | any => trivial

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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **`checkTxnPermission` on the apply thread**: `checkTxnPermission.spec`'s, the lessor finding
no lease, the verdict at the latest state: a pass is the transaction's checked permissions granted,
a refusal a checkable one refused. -/
abbrev apply.checkTxnPermission.specL : Prop :=
  ∀ (st le : GoInterface) (RD : IProp GF) (on : auth.AuthMode)
    (Lr : List auth.AuthState → IProp GF) (hs : List auth.AuthState) (ai : Loc)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (dq : DFrac) (rt : Loc) (t : txn.TxnModelW),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.isAuthStoreL st RD on Lr ∗ apply.lookupNil le ∗ ai ↦{dq} info ∗ RD ∗ Lr hs ∗
      txn.txnRequestIsW rt t ∗ ⌜apply.shapedMay on hs (apply.txnMay t)⌝ }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.checkTxnPermission))
      (Val #st)) (Val #ai)) (Val #le)) (Val #rt))
  {{ (err : GoInterface), RET #err; ai ↦{dq} info ∗ RD ∗ Lr hs ∗ applyErrIs err ∗
      ⌜on.isOn = false → err = GoInterface.nil⌝ ∗
      (∀ _ : err = GoInterface.nil, apply.txnClass on info t.toModel) ∗
      ⌜(err = GoInterface.nil → ∃ L, apply.txnChecked t L ∧
          apply.passedL on hs (auth.authInfoM info) L) ∧
        (err ≠ GoInterface.nil → apply.refusedMay on hs (auth.authInfoM info) (apply.txnMay t))⌝ }}

/-- **`CheckTxnAuth` on the apply thread** (`checkTxnPermission`'s). -/
abbrev apply.CheckTxnAuth.specL : Prop :=
  ∀ (st le : GoInterface) (RD : IProp GF) (on : auth.AuthMode)
    (Lr : List auth.AuthState → IProp GF) (hs : List auth.AuthState) (ai : Loc)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (dq : DFrac) (rt : Loc) (t : txn.TxnModelW),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.isAuthStoreL st RD on Lr ∗ apply.lookupNil le ∗ ai ↦{dq} info ∗ RD ∗ Lr hs ∗
      txn.txnRequestIsW rt t ∗ ⌜apply.shapedMay on hs (apply.txnMay t)⌝ }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.CheckTxnAuth))
      (Val #st)) (Val #ai)) (Val #le)) (Val #rt))
  {{ (err : GoInterface), RET #err; ai ↦{dq} info ∗ RD ∗ Lr hs ∗ applyErrIs err ∗
      ⌜on.isOn = false → err = GoInterface.nil⌝ ∗
      (∀ _ : err = GoInterface.nil, apply.txnClass on info t.toModel) ∗
      ⌜(err = GoInterface.nil → ∃ L, apply.txnChecked t L ∧
          apply.passedL on hs (auth.authInfoM info) L) ∧
        (err ≠ GoInterface.nil → apply.refusedMay on hs (auth.authInfoM info) (apply.txnMay t))⌝ }}

/-- **`Txn` on the apply thread**: `Txn.spec`'s, the lessor finding no lease, the request's wire
transaction `tw` (its `PrevKv`s, E3e), the outcome decided at the latest state: the auth layer's rejection with a checkable permission refused, or the inner
chain's outcome with the transaction's checked permissions granted. -/
abbrev apply.authApplierV3.Txn.specL : Prop :=
  ∀ (E : apply.AEnv GF) (c : apply.Chain) (inner : GoInterface) (p r : Loc) (skip : Bool)
    (rq : IRRModel) (t : TxnModel) (tw : txn.TxnModelW) (log F : mvcc.Log) (Pre Q Post : IProp GF)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (Lr : List auth.AuthState → IProp GF) (hs : List auth.AuthState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.authIs E p inner ∗ apply.authIsL E p Lr ∗ apply.lessorNil p ∗ apply.applierSpec E c inner ∗
      apply.txnPre E (.auth E.authOn c) (interface.mkOk (go.GoType.PointerType authApplierV3.ty) #p) info r rq t log Pre Q Post ∗
      txn.txnRequestIsW r tw ∗ ⌜rq.txnW = some tw⌝ ∗
      mvcc.idxCert E.γ.idx F ∗ Lr hs ∗ ⌜apply.shapedMay E.authMode hs (apply.txnMay tw)⌝ }}
    (App (App (Val (p @!! go.GoType.PointerType authApplierV3.ty @!! go!"Txn")) (Val #r)) (Val #skip))
  {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
      apply.kvPostFL E (.auth E.authOn c) (interface.mkOk (go.GoType.PointerType authApplierV3.ty) #p) info rq log F
        (apply.txnAnswerIs log t skip resp err) Pre Post
        (fun oc => (oc = .rejected .auth ∧
            apply.refusedMay E.authMode hs (auth.authInfoM info) (apply.txnMay tw)) ∨
          (apply.chainStep apply.backendStep c rq log oc ∧
            ∃ L, apply.txnChecked tw L ∧ apply.passedL E.authMode hs (auth.authInfoM info) L)) ∗
      Lr hs ∗ apply.traceRes trace }}

end spec

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- `checkTxnPermission`'s latest triple, as a hypothesis (the Löb induction's). -/
def apply.txnPermTL (st le : GoInterface) (RD : IProp GF) (on : auth.AuthMode)
    (Lr : List auth.AuthState → IProp GF) (hs : List auth.AuthState) (ai : Loc)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (dq : DFrac) : IProp GF :=
  iprop(□ ∀ (rt : Loc) (t : txn.TxnModelW) (Φ : val → IProp GF),
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.isAuthStoreL st RD on Lr ∗ apply.lookupNil le ∗ ai ↦{dq} info ∗ RD ∗ Lr hs ∗
      txn.txnRequestIsW rt t ∗ ⌜apply.shapedMay on hs (apply.txnMay t)⌝ -∗
    (▷ ∀ err : GoInterface, ai ↦{dq} info ∗ RD ∗ Lr hs ∗ applyErrIs err ∗
        ⌜on.isOn = false → err = GoInterface.nil⌝ ∗
        (∀ _ : err = GoInterface.nil, apply.txnClass on info t.toModel) ∗
        ⌜(err = GoInterface.nil → ∃ L, apply.txnChecked t L ∧
            apply.passedL on hs (auth.authInfoM info) L) ∧
          (err ≠ GoInterface.nil → apply.refusedMay on hs (auth.authInfoM info) (apply.txnMay t))⌝ -∗
        Φ #err) -∗
    WP (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.checkTxnPermission))
      (Val #st)) (Val #ai)) (Val #le)) (Val #rt)) {{ Φ }})

instance apply.txnPermTL_persistent (st le : GoInterface) (RD : IProp GF) (on : auth.AuthMode)
    (Lr : List auth.AuthState → IProp GF) (hs : List auth.AuthState) (ai : Loc)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (dq : DFrac) :
    Persistent (apply.txnPermTL st le RD on Lr hs ai info dq) := by
  unfold apply.txnPermTL; infer_instance

/-- **`checkTxnReqsPermission` on the apply thread**, over `checkTxnPermission`'s latest triple. -/
theorem apply.checkTxnReqs_latest
    (hPut : apply.checkPutAuth.specL (GF := GF) (hG := hG)) :
  ∀ (st le : GoInterface) (RD : IProp GF) (on : auth.AuthMode)
    (Lr : List auth.AuthState → IProp GF) (hs : List auth.AuthState) (ai : Loc)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (dq : DFrac) (reqs : GoSlice)
    (ps : List Loc) (ops : List txn.TxnOpW),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.isAuthStoreL st RD on Lr ∗ apply.lookupNil le ∗ ai ↦{dq} info ∗ RD ∗ Lr hs ∗
      reqs ↦*□ ps ∗ txn.requestOpsIsW ps ops ∗ apply.txnPermTL st le RD on Lr hs ai info dq ∗
      ⌜apply.shapedMay on hs (apply.opsMay ops)⌝ }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.checkTxnReqsPermission))
      (Val #st)) (Val #ai)) (Val #le)) (Val #reqs))
  {{ (err : GoInterface), RET #err; ai ↦{dq} info ∗ RD ∗ Lr hs ∗ applyErrIs err ∗
      ⌜on.isOn = false → err = GoInterface.nil⌝ ∗
      (∀ _ : err = GoInterface.nil, apply.opsClass on info (txn.TxnOpW.toOps ops)) ∗
      ⌜(err = GoInterface.nil → ∃ L, apply.opsChecked ops L ∧
          apply.passedL on hs (auth.authInfoM info) L) ∧
        (err ≠ GoInterface.nil → apply.refusedMay on hs (auth.authInfoM info) (apply.opsMay ops))⌝ }} := by
  intro st le RD on Lr hs ai info dq reqs ps ops
  wp_start as ⟨#Hst, #Hnil, Hai, Hrd, HL, #Hreqs, #Hops, #IH, %Hsh⟩
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
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z reqs.len⌝ ∗
      "#Hcls" ∷ apply.opsClass on info (txn.TxnOpW.toOps (ops.take (sint.nat n))) ∗
      "%Hpass" ∷ ⌜∃ L, apply.opsChecked (ops.take (sint.nat n)) L ∧
        apply.passedL on hs (auth.authInfoM info) L⌝) $$ [i requ Hai Hrd HL]
  · iexists W64 0, _
    iframe i requ Hai Hrd HL
    isplitl []
    · ipureintro
      constructor
      · decide
      · have := Hsll.2; word
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
    simp only [txn.TxnOpW.toOps]
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
      have hsh1 := apply.shapedMay_one _ _ _ _ Hsh hmay
      wp_auto
      simp only [Hrn, decide_false]
      wp_auto
      wp_apply HRange $$ %ai %info %dq %ksl %esl %k %e %DFrac.discard %DFrac.discard %hs [Hai Hrd HL]
        as %err ⟨Hai, -, -, Hrd, HL, #HeI1, %Hv1, #Hpv1⟩
      · iframe; iframe #; try (ipureintro; exact Hkb)
      have Hone := apply.verdictL_one _ _ _ _ _ _ _ Hv1 hsh1
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
        iapply HΦ; iframe Hai Hrd HL HeI1
        isplitl []
        · ipureintro; intro h; exact Hoff h
        isplitl []
        · iintro %h; cases h
        ipureintro
        exact ⟨(fun h => by cases h), fun _ =>
          apply.refusedMay_of_one _ _ _ _ _ hmay (Hone.2 (fun h => by cases h))⟩
    · -- a put
      iunfold txn.requestOpIsW at Hop
      icases Hop with ⟨%Hpn, %w, %r, #HR, #Hw, #Hr⟩
      ihave #Hr' := Hr
      iunfold txn.putRequestIs at Hr'
      icases Hr' with ⟨%Hrn, -⟩
      have hmays : ∀ x ∈ apply.putPerms o, apply.opsMay ops x := fun x hx =>
        apply.opsMay_of_getElem ops _ _ _ hop' hx
      have hshp : apply.shapedL on hs (apply.putPerms o) := by
        cases on with
        | on γa =>
          intro stl hl hen x hx
          exact Hsh stl hl hen x (hmays x hx)
        | off => trivial
        | any => trivial
      wp_auto
      simp only [Hrn, decide_false]
      wp_auto
      wp_apply (hPut _ le RD on Lr hs ai info dq r o)
        $$ [$Hst $Hnil $Hai $Hrd $HL $Hr] as %err ⟨Hai, Hrd, HL, #HeI2, %Hof2, #Hcls2, %Hvd⟩
      · ipureintro; exact hshp
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
        · iapply apply.opsClass_snoc
          iframe Hcls
          try simp only [txn.TxnOpW.toOps, txn.TxnOpW.toOp]
          iapply apply.opClass_put_of_putClass
          ihave #Hpc := Hcls2 $$ %rfl
          iexact Hpc
        · ipureintro
          refine ⟨Lp ++ apply.putPerms o, apply.opsChecked_snoc _ _ _ _ hLp ?_,
            apply.passedL_append _ _ _ _ _ hLpass (Hvd.1 rfl)⟩
          rfl
      | ok e' =>
        wp_auto
        wp_for_post
        iapply HΦ; iframe Hai Hrd HL HeI2
        isplitl []
        · ipureintro; exact Hof2
        isplitl []
        · iintro %h; cases h
        ipureintro
        exact ⟨(fun h => by cases h), fun _ =>
          apply.refusedMay_of_list _ _ _ _ _ hmays (Hvd.2 (fun h => by cases h))⟩
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
      have hshw := apply.shapedMay_one _ _ _ _ Hsh hmayw
      have hshr := fun hp => apply.shapedMay_one _ _ _ _ Hsh (hmayr hp)
      wp_auto
      simp only [Hrn, decide_false]
      wp_auto
      cases pk
      · wp_auto
        wp_apply HDel $$ %ai %info %dq %ksl %esl %k %e %DFrac.discard %DFrac.discard %hs [Hai Hrd HL]
          as %err ⟨Hai, -, -, Hrd, HL, #HeI3, %Hv3, #Hpv3⟩
        · iframe; iframe #; try (ipureintro; exact Hkb)
        have Hone := apply.verdictL_one _ _ _ _ _ _ _ Hv3 hshw
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
          iapply HΦ; iframe Hai Hrd HL HeI3
          isplitl []
          · ipureintro; intro h; exact Hoff h
          isplitl []
          · iintro %h; cases h
          ipureintro
          exact ⟨(fun h => by cases h), fun _ =>
            apply.refusedMay_of_one _ _ _ _ _ hmayw (Hone.2 (fun h => by cases h))⟩
      wp_auto
      wp_apply HRange $$ %ai %info %dq %ksl %esl %k %e %DFrac.discard %DFrac.discard %hs [Hai Hrd HL]
        as %err ⟨Hai, -, -, Hrd, HL, #HeI4, %Hv4, #Hpv4⟩
      · iframe; iframe #; try (ipureintro; exact Hkb)
      have Honer := apply.verdictL_one _ _ _ _ _ _ _ Hv4 (hshr rfl)
      have Hoffr := apply.permVerdictL_isOn _ _ _ _ _ _ _ Hv4
      cases err with
      | ok e' =>
        wp_auto
        wp_for_post
        iapply HΦ; iframe Hai Hrd HL HeI4
        isplitl []
        · ipureintro; intro h; exact Hoffr h
        isplitl []
        · iintro %h; cases h
        ipureintro
        exact ⟨(fun h => by cases h), fun _ =>
          apply.refusedMay_of_one _ _ _ _ _ (hmayr rfl) (Honer.2 (fun h => by cases h))⟩
      | nil =>
      wp_auto
      wp_apply HDel $$ %ai %info %dq %ksl %esl %k %e %DFrac.discard %DFrac.discard %hs [Hai Hrd HL]
        as %err ⟨Hai, -, -, Hrd, HL, #HeI5, %Hv5, #Hpv5⟩
      · iframe; iframe #; try (ipureintro; exact Hkb)
      have Honew := apply.verdictL_one _ _ _ _ _ _ _ Hv5 hshw
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
        iapply HΦ; iframe Hai Hrd HL HeI5
        isplitl []
        · ipureintro; intro h; exact Hoffw h
        isplitl []
        · iintro %h; cases h
        ipureintro
        exact ⟨(fun h => by cases h), fun _ =>
          apply.refusedMay_of_one _ _ _ _ _ hmayw (Honew.2 (fun h => by cases h))⟩
    · -- a nested transaction
      icases txn.requestOpIsW_txn p cs ts es $$ Hop with ⟨%Hpn, %w, %r, #HR, #Hw, #Hr⟩
      ihave #Hr' := Hr
      iunfold txn.txnRequestIsW at Hr'
      icases Hr' with ⟨%Hrn, -⟩
      have hmays : ∀ x, apply.txnMay ({ cmps := cs, thenOps := ts, elseOps := es } : txn.TxnModelW) x →
          apply.opsMay ops x := fun x hx =>
        apply.opsMay_of_getElem ops _ _ _ hop' hx
      have hshn : apply.shapedMay on hs
          (apply.txnMay ({ cmps := cs, thenOps := ts, elseOps := es } : txn.TxnModelW)) :=
        apply.shapedMay_mono _ _ _ _ hmays Hsh
      wp_auto
      simp only [Hrn, decide_false]
      wp_auto
      iunfold apply.txnPermTL at IH
      wp_apply IH $$ %r %({ cmps := cs, thenOps := ts, elseOps := es } : txn.TxnModelW) [Hai Hrd HL]
        as %err ⟨Hai, Hrd, HL, #HeI6, %Hof6, #Hcls6, %Hvd6⟩
      · iframe; iframe #; ipureintro; exact hshn
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
        · iapply apply.opsClass_snoc
          iframe Hcls
          try simp only [txn.TxnOpW.toOps, txn.TxnOpW.toOp]
          iapply apply.opClass_txn
          ihave #Ht := Hcls6 $$ %rfl
          iExactEq Ht
          rfl
        · ipureintro
          obtain ⟨Lt, hLt, hLtp⟩ := Hvd6.1 rfl
          refine ⟨Lp ++ Lt, apply.opsChecked_snoc _ _ _ _ hLp ?_,
            apply.passedL_append _ _ _ _ _ hLpass hLtp⟩
          exact hLt
      | ok e' =>
        wp_auto
        wp_for_post
        iapply HΦ; iframe Hai Hrd HL HeI6
        isplitl []
        · ipureintro; exact Hof6
        isplitl []
        · iintro %h; cases h
        ipureintro
        exact ⟨(fun h => by cases h), fun _ =>
          apply.refusedMay_mono _ _ _ _ _ hmays (Hvd6.2 (fun h => by cases h))⟩
  iapply HΦ; iframe Hai Hrd HL
  ihave %Hpl := txn.requestOpsIsW_length ps ops $$ Hops
  have hle : ops.length ≤ sint.nat n := by unfold sint.nat at *; word
  rw [List.take_of_length_le hle] at Hpass
  isplitl []
  · iapply applyErrIs_nil
  isplitl []
  · ipureintro; intro _; rfl
  isplitl []
  · iintro %_
    iExactEq Hcls
    rw [List.take_of_length_le hle]
  ipureintro
  exact ⟨fun _ => Hpass, fun h => absurd rfl h⟩

theorem apply.checkTxnPermission.wp_latest
    (hPut : apply.checkPutAuth.specL (GF := GF) (hG := hG)) :
    apply.checkTxnPermission.specL (GF := GF) (hG := hG) := by
  intro st le RD on Lr hs ai info dq rt t
  iloeb as IH generalizing %rt %t
  wp_start as ⟨#Hst, #Hnil, Hai, Hrd, HL, #Hrt, %Hsh⟩
  ihave #IHT : apply.txnPermTL st le RD on Lr hs ai info dq $$ []
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
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z csl.len⌝ ∗
      "#Hcc" ∷ apply.cmpsClass on info (t.cmps.take (sint.nat n)) ∗
      "%Hpass" ∷ ⌜∃ L, apply.cmpsChecked (t.cmps.take (sint.nat n)) L ∧
        apply.passedL on hs (auth.authInfoM info) L⌝) $$ [i c Hai Hrd HL]
  · iexists W64 0, _
    iframe i c Hai Hrd HL
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
    have hsh1 := apply.shapedMay_one _ _ _ _ Hsh hmay
    obtain ⟨Lp, hLp, hLpass⟩ := Hpass
    wp_auto
    wp_apply HRange $$ %ai %info %dq %ksl %esl %cm.key %e %DFrac.discard %DFrac.discard %hs [Hai Hrd HL]
      as %err ⟨Hai, -, -, Hrd, HL, #HeI7, %Hv7, #Hpv7⟩
    · iframe; iframe #; try (ipureintro; exact Hkb)
    have Hone := apply.verdictL_one _ _ _ _ _ _ _ Hv7 hsh1
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
      iapply HΦ; iframe Hai Hrd HL HeI7
      isplitl []
      · ipureintro; intro h; exact Hoff h
      isplitl []
      · iintro %h; cases h
      ipureintro
      exact ⟨(fun h => by cases h), fun _ =>
        apply.refusedMay_of_one _ _ _ _ _ hmay (Hone.2 (fun h => by cases h))⟩
  have hle : t.cmps.length ≤ sint.nat n := by unfold sint.nat at *; word
  rw [List.take_of_length_le hle] at Hpass
  have hsht : apply.shapedMay on hs (apply.opsMay t.thenOps) :=
    apply.shapedMay_mono _ _ _ _ (fun x hx => Or.inr (Or.inl hx)) Hsh
  have hshe : apply.shapedMay on hs (apply.opsMay t.elseOps) :=
    apply.shapedMay_mono _ _ _ _ (fun x hx => Or.inr (Or.inr hx)) Hsh
  wp_apply (apply.checkTxnReqs_latest hPut _ le RD on Lr hs ai info dq ssl sps t.thenOps)
    $$ [$Hst $Hnil $Hai $Hrd $HL $Hssl $Hss $IHT] as %err ⟨Hai, Hrd, HL, #HeI8, %Hof8, #Hcls8, %Hvd8⟩
  · ipureintro; exact hsht
  cases err with
  | ok e' =>
    wp_auto
    iapply HΦ; iframe Hai Hrd HL HeI8
    isplitl []
    · ipureintro; exact Hof8
    isplitl []
    · iintro %h; cases h
    ipureintro
    exact ⟨(fun h => by cases h), fun _ =>
      apply.refusedMay_mono _ _ _ _ _ (fun x hx => Or.inr (Or.inl hx)) (Hvd8.2 (fun h => by cases h))⟩
  | nil =>
  wp_auto
  wp_apply (apply.checkTxnReqs_latest hPut _ le RD on Lr hs ai info dq fsl fps t.elseOps)
    $$ [$Hst $Hnil $Hai $Hrd $HL $Hfsl $Hfs $IHT] as %err ⟨Hai, Hrd, HL, #HeI9, %Hof9, #Hcls9, %Hvd9⟩
  · ipureintro; exact hshe
  iapply HΦ; iframe Hai Hrd HL HeI9
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
  ipureintro
  constructor
  · intro herr
    obtain ⟨L1, hL1, hp1⟩ := Hpass
    obtain ⟨L2, hL2, hp2⟩ := Hvd8.1 rfl
    obtain ⟨L3, hL3, hp3⟩ := Hvd9.1 herr
    exact ⟨L1 ++ (L2 ++ L3), ⟨L1, L2, L3, hL1, hL2, hL3, rfl⟩,
      apply.passedL_append _ _ _ _ _ hp1 (apply.passedL_append _ _ _ _ _ hp2 hp3)⟩
  · intro herr
    exact apply.refusedMay_mono _ _ _ _ _ (fun x hx => Or.inr (Or.inr hx)) (Hvd9.2 herr)

theorem apply.CheckTxnAuth.wp_latest
    (hTxn : apply.checkTxnPermission.specL (GF := GF) (hG := hG)) :
    apply.CheckTxnAuth.specL (GF := GF) (hG := hG) := by
  intro st le RD on Lr hs ai info dq rt t
  wp_start as ⟨#Hst, #Hnil, Hai, Hrd, HL, #Hrt, %Hsh⟩
  wp_auto
  wp_apply (hTxn st le RD on Lr hs ai info dq rt t) $$ [$Hst $Hnil $Hai $Hrd $HL $Hrt] as %err Hai
  · ipureintro; exact Hsh
  iapply HΦ; iexact Hai

theorem apply.authApplierV3.Txn.wp_latest
    (hTxn : apply.CheckTxnAuth.specL (GF := GF) (hG := hG)) :
    apply.authApplierV3.Txn.specL (GF := GF) (hG := hG) := by
  intro E c inner p r skip rq t tw log F Pre Q Post info Lr hs
  wp_start as ⟨#Hauth, #HauthL, #Hlnil, #Hinner, Hpre, #Hrw, %Htw, #HF, HL, %Hsh⟩
  iunfold apply.authIs at Hauth
  icases Hauth with ⟨#Happ, -, -, -⟩
  iunfold apply.authIsL at HauthL
  icases HauthL with ⟨%st, #Hasf, #Hst⟩
  iunfold apply.lessorNil at Hlnil
  icases Hlnil with ⟨%le, #Hlef, #Hnil⟩
  iunfold apply.txnPre at Hpre
  icases Hpre with ⟨%Hk, #Hcp, #Hr, Hwt, Hm⟩
  ihave #Hcp := apply.certPre_auth E E.authOn c rq log $$ Hcp
  iunfold apply.mPre at Hm
  icases Hm with ⟨Hkv, Hres, Hcs⟩
  ihave ⟨Hard, Hkv⟩ := apply.kvOwn_rd E log $$ Hkv
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
  wp_apply (hTxn st le E.RD E.authMode Lr hs _ info (DFrac.own 1) r tw)
    $$ [$Hst $Hnil $Hinfo $Hard $HL $Hrw] as %err ⟨Hinfo, Hard, HL, #HeI, %Hoff, #Hcls, %Hvd⟩
  · ipureintro; exact Hsh
  ihave Hkv := Hkv $$ Hard
  cases err with
  | ok e' =>
    wp_auto
    iapply HΦ
    iframe HL
    isplitl
    rotate_left
    · iapply apply.traceRes_null
    iapply apply.auth_reject_kvPostFL E E.authOn c p (.ok bi) info rq log F _ Pre Q Post _ hk
      (Or.inl (by cases h : E.authOn <;> first | rfl | cases Hoff h))
      (Or.inl ⟨rfl, Hvd.2 (fun h => by cases h)⟩) $$ Happ [] Hkv Hinfo Hres Hcs
    simp only [apply.txnAnswerIs, apply.txnOutcomeIs, apply.rejErrIs]
    isplitr
    · ipureintro; trivial
    · iframe HeI; ipureintro; simp
  | nil =>
  wp_auto
  ihave #Hcls := Hcls $$ %rfl
  ihave #Hcls' : apply.txnClass E.authMode info t $$ []
  · rw [htt]; iexact Hcls
  ihave #Hrc := apply.reqClass_txn E.authMode info rq t Hk.1 Hk.2.1 $$ Hcls'
  iunfold apply.chainResAny at Hres
  icases Hres with ⟨%info', Hres⟩
  wp_apply HI $$ %r %skip %rq %t %log %F %Pre %Q %Post %info' [Hwt Hkv Hres Hcs] as %resp %trace %err ⟨Hpost, Htrc⟩
  · iunfold apply.txnPre
    iunfold apply.mPre
    iframe
    iframe #
    ipureintro; exact Hk
  iapply HΦ
  iframe HL
  isplitr [Htrc]
  rotate_left
  · iexact Htrc
  iapply apply.auth_pass_kvPostFL E E.authOn c p (.ok bi) info info' rq log F _ Pre Post
    (fun oc => (oc = .rejected .auth ∧
        apply.refusedMay E.authMode hs (auth.authInfoM info) (apply.txnMay tw)) ∨
      (apply.chainStep apply.backendStep c rq log oc ∧
        ∃ L, apply.txnChecked tw L ∧ apply.passedL E.authMode hs (auth.authInfoM info) L))
    (fun oc hoc => Or.inr ⟨hoc, Hvd.1 rfl⟩) $$ Happ Hpost Hinfo Hrc

end proof

end EtcdGrove
end Perennial
