/-
**`dispatch` on a KV request with the verdict at the latest state** (the auth plan's E2y,
2026-10-26; `notes/decisions.md`, "E2y of the auth plan"). Lean-first (no Rocq counterpart).

A second triple of `apply.uberApplier.dispatch` (`uber_applier.go`), beside its spec
(`Spec/.../apply/uberApplier__dispatch.lean`) and the admin one (`DispatchAdmin.lean`), for the KV
requests (`isKVKind`: `Range`, `Put`, `DeleteRange`, `Txn`) on the apply thread, which holds the
latest-state resource `L hs` of the store's checks (E2s). Besides `dispatch.spec`'s
postcondition, the outcome is decided at the latest state (`kvOutL`): the auth applier's methods
at the latest state (`authApplierV3.X.specL`, `AuthApplyLatest*.lean`), packaged as the current
applier's persistent KV triples (`applierKVL`, of the auth applier `applierKVL_auth`, over its
store at the latest state and the premise that the lessor finds no lease, `lessorNil`). The proof
walks the same code as the spec's: every other request kind is ruled out by `isKVKind` at its
branch.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.uberApplier__dispatch
public import Spec.errors.Is
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.ApplySecObserve
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.WarnOfExpensiveRequest
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.WarnOfFailedRequest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.DispatchLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthApplyLatestTxn

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

/-- **A KV request's outcome `oc` decided at the latest state of `hs`** for the principal `ai`
(the inner chain `ci` of the auth applier): the verdict of the auth applier's method for the
request's operation (`authApplierV3.X.specL`), the checked permissions as the checks saw them. -/
def kvOutL (M : auth.AuthMode) (hs : List auth.AuthState) (ai : auth.AuthInfoM) (ci : Chain)
    (rq : IRRModel) (log : mvcc.Log) (oc : Outcome) : Prop :=
  match dispatchKind rq with
  | .range => ∃ o, rq.range = some o ∧ ∃ e, authEndOf o.base.rangeEnd e ∧
      authOutL M hs ai ci rq log [(o.key, e, .read)] oc
  | .put => ∃ o, rq.put = some o ∧ authOutL M hs ai ci rq log (putPerms o) oc
  | .deleteRange => ∃ o, rq.deleteRange = some o ∧ ∃ e, authEndOf o.base.rangeEnd e ∧
      authOutL M hs ai ci rq log
        ((o.key, e, .write) :: if o.base.prevKV then [(o.key, e, .read)] else []) oc
  | .txn => ∃ t, rq.txn = some t ∧
      ((oc = .rejected .auth ∧ refusedMay M hs ai (txnMay t)) ∨
        (chainStep backendStep ci rq log oc ∧ ∃ L, txnChecked t L ∧ passedL M hs ai L))
  | _ => False

/-- **The KV request's checked permissions are of the cache's shape** at the latest state whenever
auth is enabled (the model's `kvDet`): what the methods' exact verdicts take. -/
def kvShapedL (M : auth.AuthMode) (hs : List auth.AuthState) (rq : IRRModel) : Prop :=
  match dispatchKind rq with
  | .range => ∀ o, rq.range = some o → shapedL M hs (rangePermsM o)
  | .put => ∀ o, rq.put = some o → shapedL M hs (putPerms o)
  | .deleteRange => ∀ o, rq.deleteRange = some o → shapedL M hs (deletePermsM o)
  | .txn => ∀ t, rq.txn = some t → shapedMay M hs (txnMay t)
  | _ => True

end pure

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The applier `a` of the chain `c`'s KV triples at the latest state** (persistent;
`applierTriples`' KV clauses with the latest-state resource family `L` and the verdict at its
history, `authOutL` of the auth applier's inner chain `ci`). -/
def applierKVL (E : AEnv GF) (c ci : Chain) (a : GoInterface)
    (L : List auth.AuthState → IProp GF) : IProp GF :=
  iprop(∃ ai : GoInterfaceOk, ⌜a = GoInterface.ok ai⌝ ∗
    □ (∀ (r : Loc) (rq : IRRModel) (o : OpFull) (log F : mvcc.Log) (Pre Q Post : IProp GF)
        (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (hs : List auth.AuthState),
      {{ putPre E c (.ok ai) info r rq o log Pre Q Post ∗ mvcc.idxCert E.γ.idx F ∗ L hs ∗
          ⌜shapedL E.authMode hs (putPerms o)⌝ }}
        (App (Val #(methods ai.ty go!"Put" ai.v)) (Val #r))
      {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
          kvPostFL E c (.ok ai) info rq log F (putAnswerIs log o resp err) Pre Post
            (authOutL E.authMode hs (auth.authInfoM info) ci rq log (putPerms o)) ∗
          L hs ∗ traceRes trace }}) ∗
    □ (∀ (r : Loc) (rq : IRRModel) (o : OpFull) (log F : mvcc.Log) (Pre Q Post : IProp GF)
        (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (hs : List auth.AuthState),
      {{ deletePre E c (.ok ai) info r rq o log Pre Q Post ∗ mvcc.idxCert E.γ.idx F ∗ L hs ∗
          ⌜shapedL E.authMode hs (deletePermsM o)⌝ }}
        (App (Val #(methods ai.ty go!"DeleteRange" ai.v)) (Val #r))
      {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
          kvPostFL E c (.ok ai) info rq log F (deleteAnswerIs log o resp err) Pre Post
            (fun oc => ∃ e, authEndOf o.base.rangeEnd e ∧
              authOutL E.authMode hs (auth.authInfoM info) ci rq log
                ((o.key, e, .write) :: if o.base.prevKV then [(o.key, e, .read)] else []) oc) ∗
          L hs ∗ traceRes trace }}) ∗
    □ (∀ (r : Loc) (rq : IRRModel) (o : OpFull) (log : mvcc.Log)
        (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (hs : List auth.AuthState),
      {{ rangePre E c (.ok ai) info r rq o log ∗ L hs ∗ ⌜shapedL E.authMode hs (rangePermsM o)⌝ }}
        (App (Val #(methods ai.ty go!"Range" ai.v)) (Val #r))
      {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
          rangePostL E c (.ok ai) info rq o log resp err
            (fun oc => ∃ e, authEndOf o.base.rangeEnd e ∧
              authOutL E.authMode hs (auth.authInfoM info) ci rq log [(o.key, e, .read)] oc) ∗
          L hs ∗ traceRes trace }}) ∗
    □ (∀ (r : Loc) (skip : Bool) (rq : IRRModel) (t : TxnModel) (log F : mvcc.Log)
        (Pre Q Post : IProp GF) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
        (hs : List auth.AuthState),
      {{ txnPre E c (.ok ai) info r rq t log Pre Q Post ∗ mvcc.idxCert E.γ.idx F ∗ L hs ∗
          ⌜shapedMay E.authMode hs (txnMay t)⌝ }}
        (App (App (Val #(methods ai.ty go!"Txn" ai.v)) (Val #r)) (Val #skip))
      {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
          kvPostFL E c (.ok ai) info rq log F (txnAnswerIs log t skip resp err) Pre Post
            (fun oc => (oc = .rejected .auth ∧
                refusedMay E.authMode hs (auth.authInfoM info) (txnMay t)) ∨
              (chainStep backendStep ci rq log oc ∧
                ∃ L, txnChecked t L ∧ passedL E.authMode hs (auth.authInfoM info) L)) ∗
          L hs ∗ traceRes trace }}))

instance applierKVL_persistent (E : AEnv GF) (c ci : Chain) (a : GoInterface)
    (L : List auth.AuthState → IProp GF) : Persistent (applierKVL E c ci a L) := by
  unfold applierKVL; infer_instance

end defs

end apply

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **`a.dispatch(r, shouldApplyV3)` on a KV request, the verdict at the latest state** (see the
file header): `dispatch.spec`'s triple for a KV request (`isKVKind`) with the current applier's
KV triples at the latest state (`applierKVL`), the latest-state resource `L hs` and the checked
permissions' shape (`kvShapedL`); besides `dispatch.spec`'s postcondition, `L hs` back and, when
applied, the outcome decided at the latest state (`kvOutL`). -/
abbrev apply.uberApplier.dispatch.kvSpecL : Prop :=
  ∀ (E : apply.AEnv GF) (p : Loc) (opts : ApplierOptions) (c : apply.Chain) (a : GoInterface)
    (r : Loc) (rq : IRRModel) (skip v3 : Bool) (log F : mvcc.Log) (Pre Q Post : IProp GF)
    (rs : apply.RestM) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (ci : apply.Chain)
    (L : List auth.AuthState → IProp GF) (hs : List auth.AuthState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.uberIs E p opts ∗
      apply.irrWrapperIs r rq skip ∗ apply.chainRes c a info ∗
      structFieldRef uberApplier go!"applyV3" p ↦ a ∗ apply.applierSpec E c a ∗
      apply.kvOwn E log ∗ apply.certPreV v3 E c rq log ∗ mvcc.storeWT E.γ ∗ apply.cPre v3 E.P E.f Pre Q Post ∗
      ⌜apply.rqOk log rq ∧ apply.dispatchOk E.authOn rq⌝ ∗ ⌜c.authOn = E.authOn⌝ ∗ mvcc.idxCert E.γ.idx F ∗
      E.FS ∗ (if v3 then apply.ciSplit E Pre else iprop(True)) ∗ E.RO rs ∗
      apply.applierKVL E c ci a L ∗ L hs ∗
      ⌜apply.isKVKind (apply.dispatchKind rq) = true ∧ apply.kvShapedL E.authMode hs rq⌝ }}
    (App (App (Val (p @!! go.GoType.PointerType uberApplier.ty @!! go!"dispatch")) (Val #r)) (Val #v3))
  {{ (ar : Loc), RET #ar; apply.chainResAny c a ∗ E.FS ∗ E.RO (apply.restAfter rq v3 rs) ∗
      ∃ (a' : GoInterface) (c' : apply.Chain) (o : apply.Outcome),
        structFieldRef uberApplier go!"applyV3" p ↦ a' ∗ apply.applierSpec E c' a' ∗
        apply.kvOwn E (o.logAfter log) ∗ apply.cPost v3 Pre Post ∗
        ⌜apply.dispatchStep c rq v3 log o ∧ apply.chainAfter rq v3 c c' ∧
          apply.kvFloorOk rq v3 F log o ∧ a' = a ∧ c' = c⌝ ∗
        (∀ _ : v3 = true, apply.chainClass E.authMode info c rq o) ∗
        apply.resTrace ar ∗ L hs ∗
        ⌜v3 = true → apply.kvOutL E.authMode hs (auth.authInfoM info) ci rq log o⌝ ∗
        apply.dispatchResult rq v3 log skip ar o }}

end spec

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **The auth applier's KV triples at the latest state** (`applierKVL`), from its methods'
latest-state specs (E2s), over its store at the latest state (`authIsL`) and the lessor finding no
lease (`lessorNil`). -/
theorem apply.applierKVL_auth
    (hRange : apply.authApplierV3.Range.specL (GF := GF) (hG := hG))
    (hDel : apply.authApplierV3.DeleteRange.specL (GF := GF) (hG := hG))
    (hPut : apply.authApplierV3.Put.specL (GF := GF) (hG := hG))
    (hTxn : apply.authApplierV3.Txn.specL (GF := GF) (hG := hG))
    (E : apply.AEnv GF) (ci : apply.Chain) (inner : GoInterface) (p : Loc)
    (L : List auth.AuthState → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.authIs E p inner ∗ apply.authIsL E p L ∗ apply.lessorNil p ∗ apply.applierSpec E ci inner ⊢
      apply.applierKVL E (.auth E.authOn ci) ci
        (interface.mkOk (go.GoType.PointerType authApplierV3.ty) #p) L := by
  iintro ⟨#Hpkg, #Ha, #HaL, #Hln, #Hin⟩
  iunfold apply.applierKVL
  iexists ⟨go.GoType.PointerType authApplierV3.ty, #p⟩
  isplitr
  · ipureintro; rfl
  isplitr
  · -- Put
    imodintro
    iintro %r %rq %o %log %F %Pre %Q %Post %info %hs
    imodintro
    iintro %Φ' ⟨Hpre, #HF, HL, %Hsh⟩ HΦ'
    iapply (hPut E ci inner p r rq o log F Pre Q Post info L hs) $$ [Hpre HL] HΦ'
    iframe Hpre HL
    iframe #
    ipureintro; exact Hsh
  isplitr
  · -- DeleteRange
    imodintro
    iintro %r %rq %o %log %F %Pre %Q %Post %info %hs
    imodintro
    iintro %Φ' ⟨Hpre, #HF, HL, %Hsh⟩ HΦ'
    iapply (hDel E ci inner p r rq o log F Pre Q Post info L hs) $$ [Hpre HL] HΦ'
    iframe Hpre HL
    iframe #
    ipureintro; exact Hsh
  isplitr
  · -- Range
    imodintro
    iintro %r %rq %o %log %info %hs
    imodintro
    iintro %Φ' ⟨Hpre, HL, %Hsh⟩ HΦ'
    iapply (hRange E ci inner p r rq o log info L hs) $$ [Hpre HL] HΦ'
    iframe Hpre HL
    iframe #
    ipureintro; exact Hsh
  · -- Txn
    imodintro
    iintro %r %skip %rq %t %log %F %Pre %Q %Post %info %hs
    imodintro
    iintro %Φ' ⟨Hpre, #HF, HL, %Hsh⟩ HΦ'
    iapply (hTxn E ci inner p r skip rq t log F Pre Q Post info L hs) $$ [Hpre HL] HΦ'
    iframe Hpre HL
    iframe #
    ipureintro; exact Hsh

set_option hygiene false in
/-- Persist the result struct `ar` (all stores done) and split it into its fields (read-only
from now on: the deferred metrics read `Resp` and `Err`). -/
local macro "persist_ar" : tactic => `(tactic| (
  ihave ⟨H0, %hn⟩ := typedPointsto_not_null_dup _ _ _ $$ «$r0»
  ipersist H0
  ihave #H0' := H0
  iStructNamed H0'))

set_option hygiene false in
/-- The deferred metrics with `success` (`ar.Err == nil`). -/
local macro "ok_path" : tactic => `(tactic| (
  wp_apply time.wp_Since as %d -
  wp_apply hASO
  wp_alloc s1 as Hs1
  wp_auto
  wp_apply hWER $$ [Hs1]
  · isplitr
    · ipureintro; exact HlgN
    iexists s1, _
    iframe Hs1
    ipureintro; exact ⟨rfl, Hipn⟩))

set_option hygiene false in
/-- The failure's warning (`WarnOfFailedRequest`), with a fresh stringer of the request. -/
local macro "wfr_step" : tactic => `(tactic| (
  wp_alloc s2 as Hs2
  wp_auto
  wp_apply hWFR $$ [Hs2]
  · isplitr
    · ipureintro; exact HlgN
    iexists s2, _
    iframe Hs2
    ipureintro; exact ⟨rfl, Hipn⟩))

set_option hygiene false in
/-- The deferred metrics with `ar.Err` not nil: `errors.Is(ar.Err, ErrCompacted)`, then the
warnings (the failure's if not `success`). -/
local macro "err_path" : tactic => `(tactic| (
  ihave #HeIu := applyErrIs_tree _ $$ HeI
  ihave ⟨%S, %M, #Htree, %HS⟩ := HeIu $$ %(GoInterface.ok ec)
  wp_apply (hIs S M _ (GoInterface.ok ec) (fun tii h => by cases h; exact Hecl.1)
    (HS.2 (fun tii h => by cases h; exact Hecl.1)))
    $$ [] as %b -
  · iframe Htree; ipureintro; exact HS.1
  wp_apply time.wp_Since as %d -
  wp_apply hASO
  wp_alloc s1 as Hs1
  wp_auto
  wp_apply hWER $$ [Hs1]
  · isplitr
    · ipureintro; exact HlgN
    iexists s1, _
    iframe Hs1
    ipureintro; exact ⟨rfl, Hipn⟩
  cases b <;> (try wp_auto) <;> (try wfr_step)))

set_option hygiene false in
/-- The deferred metrics, whatever `ar.Err`. -/
local macro "dtail" : tactic => `(tactic| (
  cases err <;> (try wp_auto) <;> first | ok_path | err_path))

set_option hygiene false in
/-- The postcondition for a request that leaves the KV and the chain as they are. -/
local macro "fin_same" : tactic => `(tactic| (
  (try ihave Hres := apply.chainResAny_of _ _ _ $$ Hres)
  iframe Hres
  iexists (GoInterface.ok ai), c, (Outcome.applied log false)
  simp only [apply.Outcome.logAfter]
  iframe Ha Hs Hkv
  isplitl [HPP]
  · simp only [apply.cPost, ↓reduceIte]; iexact HPP
  isplitr
  · ipureintro; simp [apply.kvFloorOk, apply.isFloorKind, apply.dispatchStep, apply.chainAfter, hk, apply.preV3Kind, apply.storeKind, apply.Outcome.logAfter]
  isplitl []
  · iintro %_; iapply (apply.chainClass_nonKV _ _ _ _ _ (by rw [hk]; rfl))
  first | isplitl [Htrc] | isplitl []
  · iapply apply.resTrace_of $$ H0
    first | iexact Htrc | iapply apply.traceRes_null
  simp only [apply.dispatchResult, hk, apply.preV3Kind, _root_.true_or, _root_.or_true, ↓reduceIte]
  iframe %hn
  iexists _
  iframe H0
  isplitl; rotate_left
  · first | iexact HeI | iapply applyErrIs_nil
  simp only [apply.dispatchAnswer, hk]))

set_option hygiene false in
/-- The postcondition for a request whose outcome `oc` is the chain's (`Hst`). -/
local macro "fin_kv" : tactic => `(tactic| (
  (try ihave Hres := apply.chainResAny_of _ _ _ $$ Hres)
  iframe Hres
  iexists (GoInterface.ok ai), c, oc
  iframe Ha Hs Hkv
  isplitl [HPP]
  · simp only [apply.cPost, ↓reduceIte]; iexact HPP
  isplitr
  · ipureintro
    refine ⟨?_, Or.inl rfl, ?_, rfl, rfl⟩
    · simp only [apply.dispatchStep, hk, apply.preV3Kind, apply.storeKind,
        Bool.false_eq_true, _root_.or_self, ↓reduceIte]
      first | exact Hst.1 | exact Hst
    · first | exact fun _ _ => Hst.2 | simp [apply.kvFloorOk, apply.isFloorKind, hk]
  isplitl []
  · iintro %_; iexact Hcls
  first | isplitl [Htrc] | isplitl []
  · iapply apply.resTrace_of $$ H0
    first | iexact Htrc | iapply apply.traceRes_null
  simp only [apply.dispatchResult, hk, apply.preV3Kind, _root_.or_true, ↓reduceIte]
  iframe %hn
  iexists _
  iframe H0
  isplitl; rotate_left
  · first | iexact HeI | iapply applyErrIs_nil
  simp only [apply.dispatchAnswer, hk]))

set_option hygiene false in
/-- The postcondition for a request whose outcome `oc` is the chain's (`Hst`). -/
local macro "fin_kvL" : tactic => `(tactic| (
  (try ihave Hres := apply.chainResAny_of _ _ _ $$ Hres)
  iframe Hres
  iexists (GoInterface.ok ai), c, oc
  iframe Ha Hs Hkv
  isplitl [HPP]
  · simp only [apply.cPost, ↓reduceIte]; iexact HPP
  isplitr
  · ipureintro
    refine ⟨?_, Or.inl rfl, ?_, rfl, rfl⟩
    · simp only [apply.dispatchStep, hk, apply.preV3Kind, apply.storeKind,
        Bool.false_eq_true, _root_.or_self, ↓reduceIte]
      first | exact Hst.1 | exact Hst
    · first | exact fun _ _ => Hst.2 | simp [apply.kvFloorOk, apply.isFloorKind, hk]
  isplitl []
  · iintro %_; iexact Hcls
  first | isplitl [Htrc] | isplitl []
  · iapply apply.resTrace_of $$ H0
    first | iexact Htrc | iapply apply.traceRes_null
  isplitl [HL]
  · iexact HL
  isplitr
  · ipureintro; intro _; exact HXo
  simp only [apply.dispatchResult, hk, apply.preV3Kind, _root_.or_true, ↓reduceIte]
  iframe %hn
  iexists _
  iframe H0
  isplitl; rotate_left
  · first | iexact HeI | iapply applyErrIs_nil
  simp only [apply.dispatchAnswer, hk]))

set_option hygiene false in
/-- A case of the second `switch` at the join point (`R` of the `wp_join` below): `ar` (made
read-only) and `op` as computed, then the postcondition of `dispatch` at `ar`. -/
local macro "join_ar" : tactic => `(tactic| (
  wp_join_done
  persist_ar
  imodintro
  iexists _, _, _, _, _
  iframe a r ar op H0 HeI))


set_option linter.unusedVariables false in
set_option maxHeartbeats 10000000 in
/-- **`dispatch` on a KV request, the verdict at the latest state** (see the file header). -/
theorem apply.uberApplier.dispatch.wp_kvL
    (hIs : errors.Is.spec (GF := GF) (hG := hG))
    (hASO : txn.ApplySecObserve.spec (GF := GF) (hG := hG))
    (hWER : txn.WarnOfExpensiveRequest.spec (GF := GF) (hG := hG))
    (hWFR : txn.WarnOfFailedRequest.spec (GF := GF) (hG := hG)) :
    apply.uberApplier.dispatch.kvSpecL (GF := GF) (hG := hG) := by
  intro E p opts c a r rq skip v3 log F Pre Q Post rs info ci L hh
  wp_start as ⟨#Hu, #Hw, Hres, Ha, #Hs, Hkv, #Hcp, Hwt, Hc, %Hok, %HcE, #HF, HFS, HSp, HRO, #HKV, HL, %Hx⟩
  obtain ⟨Hkk, Hsh⟩ := Hx
  ihave #Hu' := Hu
  iunfold apply.uberIs at Hu'
  icases Hu' with ⟨%Hpn, #Hopts, #Hlg, #Has, #Hwad, %base, #Hbase, #Hbs, -⟩
  ihave #Hopts' := Hopts
  iunfold apply.backendOptsOk at Hopts'
  icases Hopts' with ⟨%HlgN, -⟩
  ihave #Hw' := Hw
  iunfold apply.irrWrapperIs at Hw'
  icases Hw' with ⟨%Hrn, %ip, #Hip, #Hirr, #Hskip⟩
  ihave #Hirr' := Hirr
  iunfold apply.internalRaftRequestIs at Hirr'
  icases Hirr' with ⟨%Hipn, #FID, ⟨%lHd, #FHd, #HHd⟩, ⟨%lRa, #FRa, #HRa⟩, ⟨%lPu, #FPu, #HPu⟩,
    ⟨%lDe, #FDe, #HDe⟩, ⟨%lTx, #FTx, #HTx⟩, ⟨%lCo, #FCo, #HCo⟩, ⟨%lLG, #FLG, #HLG⟩,
    ⟨%lLR, #FLR, #HLR⟩, ⟨%lAl, #FAl, #HAl⟩, ⟨%lLC, #FLC, #HLC⟩, ⟨%lAE, #FAE, #HAE⟩,
    ⟨%lAD, #FAD, #HAD⟩, ⟨%lAS, #FAS, #HAS⟩, ⟨%lAu, #FAu, #HAu⟩, ⟨%lUA, #FUA, #HUA⟩,
    ⟨%lUD, #FUD, #HUD⟩, ⟨%lUG, #FUG, #HUG⟩, ⟨%lUC, #FUC, #HUC⟩, ⟨%lUGR, #FUGR, #HUGR⟩,
    ⟨%lURR, #FURR, #HURR⟩, ⟨%lUL, #FUL, #HUL⟩, ⟨%lRL, #FRL, #HRL⟩, ⟨%lRA, #FRA, #HRA⟩,
    ⟨%lRD, #FRD, #HRD⟩, ⟨%lRG, #FRG, #HRG⟩, ⟨%lRGP, #FRGP, #HRGP⟩, ⟨%lRRP, #FRRP, #HRRP⟩,
    ⟨%lCV, #FCV, #HCV⟩, ⟨%lCM, #FCM, #HCM⟩, ⟨%lDI, #FDI, #HDI⟩, ⟨%lDT, #FDT, #HDT⟩⟩
  ihave %nRa := apply.optReqIs_null _ _ _ (apply.rangeIs_nn lRa) $$ HRa
  ihave %nPu := apply.optReqIs_null _ _ _ (apply.putIs_nn lPu) $$ HPu
  ihave %nDe := apply.optReqIs_null _ _ _ (apply.deleteIs_nn lDe) $$ HDe
  ihave #HTx := apply.optReqIs_txnW lTx rq $$ HTx
  ihave %nTx := apply.optReqIs_null _ _ _ (apply.txnIs_nn lTx) $$ HTx
  ihave %nCo := apply.optReqIs_null _ _ _ (apply.compactionIs_nn lCo) $$ HCo
  ihave %nLG := apply.optReqIs_null _ _ _ (apply.leaseGrantIs_nn lLG) $$ HLG
  ihave %nLR := apply.optReqIs_null _ _ _ (apply.leaseRevokeIs_nn lLR) $$ HLR
  ihave %nAl := apply.optReqIs_null _ _ _ (apply.alarmRequestIs_nn lAl) $$ HAl
  ihave %nLC := apply.optReqIs_null _ _ _ (apply.leaseCheckpointIs_nn lLC) $$ HLC
  ihave %nAu := apply.optReqIs_null _ _ _ (apply.authenticateIs_nn lAu) $$ HAu
  ihave %nUG := apply.optReqIs_null _ _ _ (apply.authUserGetIs_nn lUG) $$ HUG
  ihave %nRG := apply.optReqIs_null _ _ _ (apply.authRoleGetIs_nn lRG) $$ HRG
  ihave %nCV := apply.optReqIs_null _ _ _ (apply.clusterVersionSetIs_nn lCV) $$ HCV
  ihave %nCM := apply.optReqIs_null _ _ _ (apply.memberAttrSetIs_nn lCM) $$ HCM
  ihave %nDI := apply.optReqIs_null _ _ _ (apply.downgradeInfoSetIs_nn lDI) $$ HDI
  ihave %nAE := apply.presentIs_null _ _ $$ HAE
  ihave %nAD := apply.presentIs_null _ _ $$ HAD
  ihave %nAS := apply.presentIs_null _ _ $$ HAS
  ihave %nUA := apply.optReqIs_null _ _ _ (apply.authUserAddIs_nn lUA) $$ HUA
  ihave %nUD := apply.presentIs_null _ _ $$ HUD
  ihave %nUC := apply.presentIs_null _ _ $$ HUC
  ihave %nUGR := apply.optReqIs_null _ _ _ (apply.authUserGrantRoleIs_nn lUGR) $$ HUGR
  ihave %nURR := apply.presentIs_null _ _ $$ HURR
  ihave %nUL := apply.presentIs_null _ _ $$ HUL
  ihave %nRL := apply.presentIs_null _ _ $$ HRL
  ihave %nRA := apply.optReqIs_null _ _ _ (apply.authRoleAddIs_nn lRA) $$ HRA
  ihave %nRD := apply.presentIs_null _ _ $$ HRD
  ihave %nRGP := apply.optReqIs_null _ _ _ (apply.authRoleGrantPermissionIs_nn lRGP) $$ HRGP
  ihave %nRRP := apply.presentIs_null _ _ $$ HRRP
  ihave %nDT := apply.presentIs_null _ _ $$ HDT
  ihave #Hsp := Hs
  iunfold apply.applierSpec at Hsp
  icases Hsp with ⟨%ai, %Hai, #Ht⟩
  subst Hai
  iunfold apply.applierTriples at Ht
  icases Ht with ⟨#HPut, #HDel, #HRange, #HTxn, #HRev, #HResp, #HResp0, #HStatus, #HCluster, -⟩
  iunfold apply.applierKVL at HKV
  icases HKV with ⟨%ai', %Hai', #HPutL, #HDelL, #HRangeL, #HTxnL⟩
  injection Hai' with Hai'
  subst Hai'
  ihave #Hmp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  ihave Hinit : (go_etcd_io.etcd.server.v3.storage.mvcc.mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hmp
  iclear Hinit
  ihave Hai : (go_etcd_io.etcd.server.v3.etcdserver.apply.applyInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hai with ⟨-, -, #Hev⟩
  ihave #Hev' := Hev
  icases Hev' with ⟨-, -, -, -, -, #HCpl, -⟩
  iunfold errVarLeaf at HCpl
  icases HCpl with ⟨%ec, #Hcomp, %Hecl, -⟩
  ihave #Perr : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  ihave #Ptxn : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  wp_apply time.wp_Now as %start -
  wp_if_destruct
  · -- ClusterVersionSet
    have hl : lCV ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nCV.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HCV
    have hk : dispatchKind rq = .clusterVersionSet := by simp [dispatchKind, hs]
    exact absurd Hkk (by simp [apply.isKVKind, hk])
  have zClusterVersionSet : rq.clusterVersionSet = none := nCV.1 (by simpa using Hif)
  wp_if_destruct
  · -- ClusterMemberAttrSet
    have hl : lCM ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nCM.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HCM
    have hk : dispatchKind rq = .clusterMemberAttrSet := by simp [dispatchKind, zClusterVersionSet, hs]
    exact absurd Hkk (by simp [apply.isKVKind, hk])
  have zClusterMemberAttrSet : rq.clusterMemberAttrSet = none := nCM.1 (by simpa using Hif)
  -- (D22, 2026-10-23) no other request changes the rest buckets
  ihave HRO : iprop(E.RO (apply.restAfter rq v3 rs)) $$ [HRO]
  · rw [apply.restAfter_other rq v3 rs zClusterVersionSet zClusterMemberAttrSet]; iexact HRO
  wp_if_destruct
  · -- DowngradeInfoSet (D22, 2026-10-23: not admitted, `rqOk`)
    have hl : lDI ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nDI.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HDI
    have hk : dispatchKind rq = .downgradeInfoSet := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, hs]
    exact absurd Hkk (by simp [apply.isKVKind, hk])
  have zDowngradeInfoSet : rq.downgradeInfoSet = none := nDI.1 (by simpa using Hif)
  wp_if_destruct
  · -- DowngradeVersionTest: nothing
    have hl : lDT ≠ null := by simpa using Hif
    have hs : rq.downgradeVersionTest = true := by
      cases h : rq.downgradeVersionTest
      · exact absurd (nDT.2 h) hl
      · rfl
    have hk : dispatchKind rq = .downgradeVersionTest := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, hs]
    exact absurd Hkk (by simp [apply.isKVKind, hk])
  have zDowngradeVersionTest : rq.downgradeVersionTest = false := nDT.1 (by simpa using Hif)
  have hpre : apply.preV3Kind (dispatchKind rq) = false :=
    apply.preV3Kind_dispatchKind rq zClusterVersionSet zClusterMemberAttrSet zDowngradeInfoSet zDowngradeVersionTest
  cases v3
  · -- not `shouldApplyV3`: nil
    (try wp_auto)
    ok_path
    iapply HΦ
    iframe HFS HRO
    ihave Hres := apply.chainResAny_of _ _ _ $$ Hres
    iframe Hres
    iexists (GoInterface.ok ai), c, (Outcome.applied log false)
    simp only [apply.Outcome.logAfter]
    iframe Ha Hs Hkv
    isplitl [Hc]
    · simp only [apply.cPost, apply.cPre, Bool.false_eq_true, ↓reduceIte]; iexact Hc
    isplitr
    · ipureintro; simp [apply.kvFloorOk, apply.dispatchStep, apply.chainAfter, hpre]
    isplitl []
    · iintro %h; cases h
    isplitl []
    · iapply apply.resTrace_null
    iframe HL
    isplitr
    · ipureintro; intro h; cases h
    simp only [apply.dispatchResult, hpre, Bool.false_eq_true, or_self, ↓reduceIte]
    ipureintro; trivial
  (try wp_auto)
  ihave Hc : iprop(mvcc.csContract E.P E.f Pre Q Post) $$ [Hc]
  · simp only [apply.cPre, ↓reduceIte]; iexact Hc
  ihave #HSp : apply.ciSplit E Pre $$ [HSp]
  · simp only [↓reduceIte]; iexact HSp
  ihave #Hcp := apply.certPreV_true E c rq log $$ Hcp
  -- the second `switch`: each case computes `ar` and `op` and establishes the postcondition
  -- at `ar`; the `return` and the deferred metrics, after the join, are verified once (not
  -- once per request kind)
  wp_join iprop(|==> ∃ (resp : google_golang_org.protobuf.reflect.protoreflect.ProtoMessage)
      (err : GoError) (physc : GoChan) (trace : Loc) (opS : GoString),
      a_ptr ↦ p ∗ r_ptr ↦ r ∗ ar_ptr ↦ «$r0_ptr» ∗ op_ptr ↦ opS ∗
      «$r0_ptr» ↦□ Result.mk resp err physc trace ∗ applyErrIs err ∗
      (apply.chainResAny c (GoInterface.ok ai) ∗
        ∃ (a' : GoInterface) (c' : apply.Chain) (o : apply.Outcome),
          structFieldRef uberApplier go!"applyV3" p ↦ a' ∗ apply.applierSpec E c' a' ∗
          apply.kvOwn E (o.logAfter log) ∗ apply.cPost true Pre Post ∗
          ⌜apply.dispatchStep c rq true log o ∧ apply.chainAfter rq true c c' ∧
            apply.kvFloorOk rq true F log o ∧ a' = GoInterface.ok ai ∧ c' = c⌝ ∗
          (∀ _ : true = true, apply.chainClass E.authMode info c rq o) ∗
          apply.resTrace «$r0_ptr» ∗ L hh ∗
          ⌜true = true → apply.kvOutL E.authMode hh (auth.authInfoM info) ci rq log o⌝ ∗
          apply.dispatchResult rq true log skip «$r0_ptr» o))
    with [a r ar op «$r0» Hc Hres Ha Hkv Hwt HL]
  · -- Range
    have hl : lRa ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nRa.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HRa
    have hk : dispatchKind rq = .range := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, hs]
    have hok := Hok.1
    simp only [rqOk, hk] at hok
    have hsh : apply.shapedL E.authMode hh (apply.rangePermsM x) := by
      have h := Hsh; simp only [apply.kvShapedL, hk] at h; exact h x hs
    wp_apply HRangeL $$ %lRa %rq %x %log %info %hh [Hkv Hres HL] as %resp %trace %err ⟨Hpost, HL, Htrc⟩
    · isplitl [Hkv Hres]
      · iunfold apply.rangePre
        isplitr
        · ipureintro; exact ⟨hs, hk, hok x hs⟩
        iframe HR
        iframe
      iframe HL; ipureintro; exact hsh
    iunfold apply.rangePostL at Hpost
    icases Hpost with ⟨%oc, %Hst0, Hans, Hkv, Hres, #Hcls⟩
    have Hst := Hst0.1
    have HXo : apply.kvOutL E.authMode hh (auth.authInfoM info) ci rq log oc := by
      simp only [apply.kvOutL, hk]; exact ⟨x, hs, Hst0.2⟩
    ihave ⟨Hans, #HeI⟩ := apply.keep_errIs (apply.rangeOutcomeIs_errIs _ _ _ _ _) $$ [$Hev $Hans]
    join_ar
    ihave HPP : iprop(Post ∨ Pre) $$ [Hc]
    · iright; iapply apply.csContract_pre; iexact Hc
    fin_kvL
    iexists x, resp; iframe Hans; ipureintro; exact ⟨hs, rfl⟩
  have zRange : rq.range = none := nRa.1 (by simpa using Hif)
  wp_if_destruct
  · -- Put
    have hl : lPu ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nPu.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HPu
    have hk : dispatchKind rq = .put := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, hs]
    have hok := Hok.1
    simp only [rqOk, hk] at hok
    have hsh : apply.shapedL E.authMode hh (apply.putPerms x) := by
      have h := Hsh; simp only [apply.kvShapedL, hk] at h; exact h x hs
    wp_apply HPutL $$ %lPu %rq %x %log %F %Pre %Q %Post %info %hh [Hkv Hwt Hres Hc HL] as %resp %trace %err ⟨Hpost, HL, Htrc⟩
    · iframe HF HL
      isplitl [Hkv Hwt Hres Hc]
      · iunfold apply.putPre
        isplitr
        · ipureintro; exact ⟨hs, hk, hok⟩
        iframe HR Hcp
        iunfold apply.mPre
        iframe
      ipureintro; exact hsh
    iunfold apply.kvPostFL at Hpost
    icases Hpost with ⟨%oc, %Hst0, Hans, Hkv, Hres, HPP, #Hcls⟩
    have Hst := And.intro Hst0.1 Hst0.2.1
    have HXo : apply.kvOutL E.authMode hh (auth.authInfoM info) ci rq log oc := by
      simp only [apply.kvOutL, hk]; exact ⟨x, hs, Hst0.2.2⟩
    ihave ⟨Hans, #HeI⟩ := apply.keep_errIs (apply.putAnswerIs_errIs _ _ _ _ _) $$ [$Hev $Hans]
    join_ar
    fin_kvL
    iexists x, resp; iframe Hans; ipureintro; exact ⟨hs, rfl⟩
  have zPut : rq.put = none := nPu.1 (by simpa using Hif)
  wp_if_destruct
  · -- DeleteRange
    have hl : lDe ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nDe.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HDe
    have hk : dispatchKind rq = .deleteRange := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, hs]
    have hok := Hok.1
    simp only [rqOk, hk] at hok
    have hsh : apply.shapedL E.authMode hh (apply.deletePermsM x) := by
      have h := Hsh; simp only [apply.kvShapedL, hk] at h; exact h x hs
    wp_apply HDelL $$ %lDe %rq %x %log %F %Pre %Q %Post %info %hh [Hkv Hwt Hres Hc HL] as %resp %trace %err ⟨Hpost, HL, Htrc⟩
    · iframe HF HL
      isplitl [Hkv Hwt Hres Hc]
      · iunfold apply.deletePre
        isplitr
        · ipureintro; exact ⟨hs, hk, hok x hs⟩
        iframe HR Hcp
        iunfold apply.mPre
        iframe
      ipureintro; exact hsh
    iunfold apply.kvPostFL at Hpost
    icases Hpost with ⟨%oc, %Hst0, Hans, Hkv, Hres, HPP, #Hcls⟩
    have Hst := And.intro Hst0.1 Hst0.2.1
    have HXo : apply.kvOutL E.authMode hh (auth.authInfoM info) ci rq log oc := by
      simp only [apply.kvOutL, hk]; exact ⟨x, hs, Hst0.2.2⟩
    ihave ⟨Hans, #HeI⟩ := apply.keep_errIs (apply.deleteAnswerIs_errIs _ _ _ _ _) $$ [$Hev $Hans]
    join_ar
    fin_kvL
    iexists x, resp; iframe Hans; ipureintro; exact ⟨hs, rfl⟩
  have zDeleteRange : rq.deleteRange = none := nDe.1 (by simpa using Hif)
  wp_if_destruct
  · -- Txn
    have hl : lTx ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nTx.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HTx
    have hk : dispatchKind rq = .txn := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, hs]
    have hok := Hok.1
    simp only [rqOk, hk] at hok
    have hsh : apply.shapedMay E.authMode hh (apply.txnMay x) := by
      have h := Hsh; simp only [apply.kvShapedL, hk] at h; exact h x hs
    wp_apply HTxnL $$ %lTx %skip %rq %x %log %F %Pre %Q %Post %info %hh [Hkv Hwt Hres Hc HL] as %resp %trace %err ⟨Hpost, HL, Htrc⟩
    · iframe HF HL
      isplitl [Hkv Hwt Hres Hc]
      · iunfold apply.txnPre
        isplitr
        · ipureintro; exact ⟨hs, hk, hok x hs⟩
        iframe HR Hcp
        iunfold apply.mPre
        iframe
      ipureintro; exact hsh
    iunfold apply.kvPostFL at Hpost
    icases Hpost with ⟨%oc, %Hst0, Hans, Hkv, Hres, HPP, #Hcls⟩
    have Hst := And.intro Hst0.1 Hst0.2.1
    have HXo : apply.kvOutL E.authMode hh (auth.authInfoM info) ci rq log oc := by
      simp only [apply.kvOutL, hk]; exact ⟨x, hs, Hst0.2.2⟩
    ihave ⟨Hans, #HeI⟩ := apply.keep_errIs (apply.txnAnswerIs_errIs _ _ _ _ _ _) $$ [$Hev $Hans]
    join_ar
    fin_kvL
    iexists x, resp; iframe Hans; ipureintro; exact ⟨hs, rfl⟩
  have zTxn : rq.txn = none := nTx.1 (by simpa using Hif)
  wp_if_destruct
  · -- Compaction: out of the model (the premise `dispatchOk`)
    have hl : lCo ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nCo.2 h))
    have hk : dispatchKind rq = .compaction := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, hs]
    exact absurd Hkk (by simp [apply.isKVKind, hk])
  have zCompaction : rq.compaction = none := nCo.1 (by simpa using Hif)
  wp_if_destruct
  · -- LeaseGrant
    have hl : lLG ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nLG.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HLG
    have hk : dispatchKind rq = .leaseGrant := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, hs]
    exact absurd Hkk (by simp [apply.isKVKind, hk])
  have zLeaseGrant : rq.leaseGrant = none := nLG.1 (by simpa using Hif)
  wp_if_destruct
  · -- LeaseRevoke
    have hl : lLR ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nLR.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HLR
    have hk : dispatchKind rq = .leaseRevoke := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, hs]
    exact absurd Hkk (by simp [apply.isKVKind, hk])
  have zLeaseRevoke : rq.leaseRevoke = none := nLR.1 (by simpa using Hif)
  wp_if_destruct
  · -- LeaseCheckpoint
    have hl : lLC ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nLC.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HLC
    have hk : dispatchKind rq = .leaseCheckpoint := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, hs]
    exact absurd Hkk (by simp [apply.isKVKind, hk])
  have zLeaseCheckpoint : rq.leaseCheckpoint = none := nLC.1 (by simpa using Hif)
  wp_if_destruct
  · -- Alarm: not admitted (`rqOk`; D22, 2026-10-23: its writer takes `AEnv.RW`)
    have hl : lAl ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nAl.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HAl
    have hk : dispatchKind rq = .alarm := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, hs]
    exact absurd Hkk (by simp [apply.isKVKind, hk])
  have zAlarm : rq.alarm = none := nAl.1 (by simpa using Hif)
  wp_if_destruct
  · -- Authenticate (D22, 2026-10-23: not admitted, `rqOk`)
    have hl : lAu ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nAu.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HAu
    have hk : dispatchKind rq = .authenticate := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, hs]
    exact absurd Hkk (by simp [apply.isKVKind, hk])
  have zAuthenticate : rq.authenticate = none := nAu.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthEnable (D22, 2026-10-23: not admitted, `rqOk`)
    have hl : lAE ≠ null := by simpa using Hif
    have hs : rq.authEnable = true := by
      cases h : rq.authEnable
      · exact absurd (nAE.2 h) hl
      · rfl
    have hk : dispatchKind rq = .authEnable := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, hs]
    exact absurd Hkk (by simp [apply.isKVKind, hk])
  have zAuthEnable : rq.authEnable = false := nAE.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthDisable (D22, 2026-10-23: not admitted, `rqOk`)
    have hl : lAD ≠ null := by simpa using Hif
    have hs : rq.authDisable = true := by
      cases h : rq.authDisable
      · exact absurd (nAD.2 h) hl
      · rfl
    have hk : dispatchKind rq = .authDisable := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, hs]
    exact absurd Hkk (by simp [apply.isKVKind, hk])
  have zAuthDisable : rq.authDisable = false := nAD.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthStatus
    have hl : lAS ≠ null := by simpa using Hif
    have hs : rq.authStatus = true := by
      cases h : rq.authStatus
      · exact absurd (nAS.2 h) hl
      · rfl
    have hk : dispatchKind rq = .authStatus := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, hs]
    exact absurd Hkk (by simp [apply.isKVKind, hk])
  have zAuthStatus : rq.authStatus = false := nAS.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthUserAdd (D22, 2026-10-23: not admitted, `rqOk`)
    have hl : lUA ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nUA.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HUA
    have hk : dispatchKind rq = .authUserAdd := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, zAuthStatus, hs]
    exact absurd Hkk (by simp [apply.isKVKind, hk])
  have zAuthUserAdd : rq.authUserAdd = none := nUA.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthUserDelete (D22, 2026-10-23: not admitted, `rqOk`)
    have hl : lUD ≠ null := by simpa using Hif
    have hs : rq.authUserDelete = true := by
      cases h : rq.authUserDelete
      · exact absurd (nUD.2 h) hl
      · rfl
    have hk : dispatchKind rq = .authUserDelete := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, zAuthStatus, zAuthUserAdd, hs]
    exact absurd Hkk (by simp [apply.isKVKind, hk])
  have zAuthUserDelete : rq.authUserDelete = false := nUD.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthUserChangePassword (D22, 2026-10-23: not admitted, `rqOk`)
    have hl : lUC ≠ null := by simpa using Hif
    have hs : rq.authUserChangePassword = true := by
      cases h : rq.authUserChangePassword
      · exact absurd (nUC.2 h) hl
      · rfl
    have hk : dispatchKind rq = .authUserChangePassword := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, zAuthStatus, zAuthUserAdd, zAuthUserDelete, hs]
    exact absurd Hkk (by simp [apply.isKVKind, hk])
  have zAuthUserChangePassword : rq.authUserChangePassword = false := nUC.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthUserGrantRole (D22, 2026-10-23: not admitted, `rqOk`)
    have hl : lUGR ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nUGR.2 h))
    have hk : dispatchKind rq = .authUserGrantRole := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, zAuthStatus, zAuthUserAdd, zAuthUserDelete, zAuthUserChangePassword, hs]
    exact absurd Hkk (by simp [apply.isKVKind, hk])
  have zAuthUserGrantRole : rq.authUserGrantRole = none := nUGR.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthUserGet (D22, 2026-10-23: not admitted, `rqOk`)
    have hl : lUG ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nUG.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HUG
    have hk : dispatchKind rq = .authUserGet := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, zAuthStatus, zAuthUserAdd, zAuthUserDelete, zAuthUserChangePassword, zAuthUserGrantRole, hs]
    exact absurd Hkk (by simp [apply.isKVKind, hk])
  have zAuthUserGet : rq.authUserGet = none := nUG.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthUserRevokeRole (D22, 2026-10-23: not admitted, `rqOk`)
    have hl : lURR ≠ null := by simpa using Hif
    have hs : rq.authUserRevokeRole = true := by
      cases h : rq.authUserRevokeRole
      · exact absurd (nURR.2 h) hl
      · rfl
    have hk : dispatchKind rq = .authUserRevokeRole := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, zAuthStatus, zAuthUserAdd, zAuthUserDelete, zAuthUserChangePassword, zAuthUserGrantRole, zAuthUserGet, hs]
    exact absurd Hkk (by simp [apply.isKVKind, hk])
  have zAuthUserRevokeRole : rq.authUserRevokeRole = false := nURR.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthRoleAdd (D22, 2026-10-23: not admitted, `rqOk`)
    have hl : lRA ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nRA.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HRA
    have hk : dispatchKind rq = .authRoleAdd := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, zAuthStatus, zAuthUserAdd, zAuthUserDelete, zAuthUserChangePassword, zAuthUserGrantRole, zAuthUserGet, zAuthUserRevokeRole, hs]
    exact absurd Hkk (by simp [apply.isKVKind, hk])
  have zAuthRoleAdd : rq.authRoleAdd = none := nRA.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthRoleGrantPermission (D22, 2026-10-23: not admitted, `rqOk`)
    have hl : lRGP ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nRGP.2 h))
    have hk : dispatchKind rq = .authRoleGrantPermission := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, zAuthStatus, zAuthUserAdd, zAuthUserDelete, zAuthUserChangePassword, zAuthUserGrantRole, zAuthUserGet, zAuthUserRevokeRole, zAuthRoleAdd, hs]
    exact absurd Hkk (by simp [apply.isKVKind, hk])
  have zAuthRoleGrantPermission : rq.authRoleGrantPermission = none := nRGP.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthRoleGet (D22, 2026-10-23: not admitted, `rqOk`)
    have hl : lRG ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nRG.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HRG
    have hk : dispatchKind rq = .authRoleGet := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, zAuthStatus, zAuthUserAdd, zAuthUserDelete, zAuthUserChangePassword, zAuthUserGrantRole, zAuthUserGet, zAuthUserRevokeRole, zAuthRoleAdd, zAuthRoleGrantPermission, hs]
    exact absurd Hkk (by simp [apply.isKVKind, hk])
  have zAuthRoleGet : rq.authRoleGet = none := nRG.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthRoleRevokePermission (D22, 2026-10-23: not admitted, `rqOk`)
    have hl : lRRP ≠ null := by simpa using Hif
    have hs : rq.authRoleRevokePermission = true := by
      cases h : rq.authRoleRevokePermission
      · exact absurd (nRRP.2 h) hl
      · rfl
    have hk : dispatchKind rq = .authRoleRevokePermission := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, zAuthStatus, zAuthUserAdd, zAuthUserDelete, zAuthUserChangePassword, zAuthUserGrantRole, zAuthUserGet, zAuthUserRevokeRole, zAuthRoleAdd, zAuthRoleGrantPermission, zAuthRoleGet, hs]
    exact absurd Hkk (by simp [apply.isKVKind, hk])
  have zAuthRoleRevokePermission : rq.authRoleRevokePermission = false := nRRP.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthRoleDelete (D22, 2026-10-23: not admitted, `rqOk`)
    have hl : lRD ≠ null := by simpa using Hif
    have hs : rq.authRoleDelete = true := by
      cases h : rq.authRoleDelete
      · exact absurd (nRD.2 h) hl
      · rfl
    have hk : dispatchKind rq = .authRoleDelete := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, zAuthStatus, zAuthUserAdd, zAuthUserDelete, zAuthUserChangePassword, zAuthUserGrantRole, zAuthUserGet, zAuthUserRevokeRole, zAuthRoleAdd, zAuthRoleGrantPermission, zAuthRoleGet, zAuthRoleRevokePermission, hs]
    exact absurd Hkk (by simp [apply.isKVKind, hk])
  have zAuthRoleDelete : rq.authRoleDelete = false := nRD.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthUserList (D22, 2026-10-23: not admitted, `rqOk`)
    have hl : lUL ≠ null := by simpa using Hif
    have hs : rq.authUserList = true := by
      cases h : rq.authUserList
      · exact absurd (nUL.2 h) hl
      · rfl
    have hk : dispatchKind rq = .authUserList := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, zAuthStatus, zAuthUserAdd, zAuthUserDelete, zAuthUserChangePassword, zAuthUserGrantRole, zAuthUserGet, zAuthUserRevokeRole, zAuthRoleAdd, zAuthRoleGrantPermission, zAuthRoleGet, zAuthRoleRevokePermission, zAuthRoleDelete, hs]
    exact absurd Hkk (by simp [apply.isKVKind, hk])
  have zAuthUserList : rq.authUserList = false := nUL.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthRoleList (D22, 2026-10-23: not admitted, `rqOk`)
    have hl : lRL ≠ null := by simpa using Hif
    have hs : rq.authRoleList = true := by
      cases h : rq.authRoleList
      · exact absurd (nRL.2 h) hl
      · rfl
    have hk : dispatchKind rq = .authRoleList := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, zAuthStatus, zAuthUserAdd, zAuthUserDelete, zAuthUserChangePassword, zAuthUserGrantRole, zAuthUserGet, zAuthUserRevokeRole, zAuthRoleAdd, zAuthRoleGrantPermission, zAuthRoleGet, zAuthRoleRevokePermission, zAuthRoleDelete, zAuthUserList, hs]
    exact absurd Hkk (by simp [apply.isKVKind, hk])
  have zAuthRoleList : rq.authRoleList = false := nRL.1 (by simpa using Hif)
  -- `default`: `lg.Panic`: no field set, ruled out by the premise `dispatchOk`
  exfalso
  exact Hok.2.2.1 (by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, zAuthStatus, zAuthUserAdd, zAuthUserDelete, zAuthUserChangePassword, zAuthUserGrantRole, zAuthUserGet, zAuthUserRevokeRole, zAuthRoleAdd, zAuthRoleGrantPermission, zAuthRoleGet, zAuthRoleRevokePermission, zAuthRoleDelete, zAuthUserList, zAuthRoleList])
  -- after the join: `return ar` and the deferred metrics
  iintro Hj
  imod Hj with ⟨%resp, %err, %physc, %trace, %opS, a, r, ar, op, #H0, #HeI, Hpost⟩
  ihave #H0' := H0
  iStructNamed H0'
  dtail
  all_goals
    iapply HΦ
    iframe HFS HRO
    iexact Hpost


end proof

end EtcdGrove
end Perennial
