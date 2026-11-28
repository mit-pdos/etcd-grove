/-
**The auth applier's KV methods at the latest state** (the auth plan's E2s, 2026-10-26;
`notes/decisions.md`, "E2s of the auth plan"). The auth applier's `Range`, `DeleteRange`, `Put`
(and `Txn`, `AuthApplyLatestTxn.lean`) on the apply thread, which holds the latest-state resource
`L hs` of the store's checks (`isAuthStoreL`, `AuthLatest.lean`): besides the methods' posts
(`kvPostF`, `rangePost`), the outcome is decided at the latest state of `hs` (`authOutL`): the
auth layer's rejection, with one of the checked permissions refused there (`refusedL`), or the
inner chain's outcome, with every checked permission granted there (`passedL`), each in
`granted1`'s form (`kvGranted`'s, E2q's `etcdserver/KVAuthModel.lean`).

The checked permissions are the model's with the range end as the check saw it (`authEndOf`:
equal unless the request's `RangeEnd` is a non-`nil` empty slice). A `Put`'s lease check
(`checkLeasePuts`) is decided at the latest state over the lease owner's resource (auth-lease S2;
until then ruled out by a premise "the lessor finds no lease", `lookupNil`, deleted in S3c).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthLatest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.WriteLemmas
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.authApplierV3__Range
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.authApplierV3__DeleteRange
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.authApplierV3__Put
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.checkLeasePuts

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

/-- **The outcome `oc` decided at the latest state** for the checked permissions `perms`: the
auth layer's rejection with one of them refused, or the inner chain `c`'s outcome with all of them
granted. -/
def authOutL (M : auth.AuthMode) (hs : List auth.AuthState) (ai : auth.AuthInfoM) (c : Chain)
    (rq : IRRModel) (log : mvcc.Log) (perms : List Perm3) (oc : Outcome) : Prop :=
  (oc = .rejected .auth ∧ refusedL M hs ai perms) ∨
    (chainStep backendStep c rq log oc ∧ passedL M hs ai perms)

/-- **The outcome `oc` decided at the latest state for the checked permissions `perms` and the leases
`ids`** (auth-lease S2: `authOutL` with `checkLeasePuts`' part, at the owner's item map `I`): the auth
layer's rejection with a permission or a lease refused, or the inner chain `c`'s outcome with all of them
granted. -/
def authOutLL (M : auth.AuthMode) (hs : List auth.AuthState) (ai : auth.AuthInfoM) (c : Chain)
    (rq : IRRModel) (log : mvcc.Log) (perms : List Perm3)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (ids : List w64) (oc : Outcome) : Prop :=
  (oc = .rejected .auth ∧ (refusedL M hs ai perms ∨ ∃ id ∈ ids, leaseRefusedL M hs ai I id)) ∨
    (chainStep backendStep c rq log oc ∧ passedL M hs ai perms ∧
      ∀ id ∈ ids, leasePassedL M hs ai I id)

/-- `authOutL` is `authOutLL` with no lease. -/
theorem authOutL_iff (M : auth.AuthMode) (hs : List auth.AuthState) (ai : auth.AuthInfoM) (c : Chain)
    (rq : IRRModel) (log : mvcc.Log) (perms : List Perm3)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (oc : Outcome) :
    authOutL M hs ai c rq log perms oc ↔ authOutLL M hs ai c rq log perms I [] oc := by
  unfold authOutL authOutLL
  simp

/-! ### An outcome past the auth layer (auth-lease S4 item 7b, 2026-11-17)

Where the auth layer passes a request, some outcome of the inner chain is not the auth layer's rejection: what
discharges the latest-state methods' window premise (`putPreW`, ...), asked only then. -/

/-- The backend never answers with the auth layer's rejection. -/
theorem backendStep_ne_auth (rq : IRRModel) (log : mvcc.Log) (oc : Outcome) (h : backendStep rq log oc) :
    oc ≠ .rejected .auth := by
  rintro rfl
  unfold backendStep at h
  split at h <;> simp_all

/-- Some outcome of the chain `c` other than the auth layer's rejection, given one of `B`'s. -/
theorem chainStep_exists_ne_auth (B : IRRModel → mvcc.Log → Outcome → Prop) (rq : IRRModel) (log : mvcc.Log)
    (hB : ∃ oc, B rq log oc ∧ oc ≠ .rejected .auth) :
    ∀ c : Chain, ∃ oc, chainStep B c rq log oc ∧ oc ≠ .rejected .auth
  | .backend => hB
  | .auth on c => by
    obtain ⟨oc, h, hne⟩ := chainStep_exists_ne_auth B rq log hB c
    refine ⟨oc, ?_, hne⟩
    simp only [chainStep]; split
    · exact Or.inr h
    · exact h
  | .quota c => chainStep_exists_ne_auth B rq log hB c
  | .capped c => by
    obtain ⟨oc, h, hne⟩ := chainStep_exists_ne_auth B rq log hB c
    simp only [chainStep]
    split
    · exact ⟨.rejected .noSpace, rfl, by simp⟩
    · split
      · exact ⟨oc, Or.inr h, hne⟩
      · exact ⟨oc, h, hne⟩
  | .corrupt c => by
    obtain ⟨oc, h, hne⟩ := chainStep_exists_ne_auth B rq log hB c
    simp only [chainStep]
    split
    · exact ⟨.rejected .corrupt, rfl, by simp⟩
    · exact ⟨oc, h, hne⟩

/-- A put has a backend outcome. -/
theorem backendStep_exists_put (rq : IRRModel) (log : mvcc.Log) (o : OpFull) (ho : rq.put = some o)
    (hk : dispatchKind rq = .put) : ∃ oc, backendStep rq log oc := by
  unfold backendStep; rw [hk]
  by_cases h1 : o.leaseID ≠ W64 0
  · exact ⟨_, o, ho, Or.inl ⟨h1, rfl⟩⟩
  by_cases h2 : txn.needsPrev o = true ∧ mvcc.findKey o.key (mvcc.stateAfter log) = none
  · exact ⟨_, o, ho, Or.inr (Or.inl ⟨h2.1, h2.2, rfl⟩)⟩
  refine ⟨_, o, ho, Or.inr (Or.inr ⟨fun hn => ?_, rfl⟩)⟩
  cases hf : mvcc.findKey o.key (mvcc.stateAfter log) with
  | none => exact absurd ⟨hn, hf⟩ h2
  | some _ => rfl

/-- A delete has a backend outcome. -/
theorem backendStep_exists_delete (rq : IRRModel) (log : mvcc.Log) (o : OpFull) (ho : rq.deleteRange = some o)
    (hk : dispatchKind rq = .deleteRange) : ∃ oc, backendStep rq log oc := by
  unfold backendStep; rw [hk]; exact ⟨_, o, ho, rfl⟩

/-- A revocation has a backend outcome. -/
theorem backendStep_exists_revoke (rq : IRRModel) (log : mvcc.Log) (id : w64) (ho : rq.leaseRevoke = some id)
    (hk : dispatchKind rq = .leaseRevoke) : ∃ oc, backendStep rq log oc := by
  unfold backendStep; rw [hk]; exact ⟨_, id, ho, rfl⟩

/-- A transaction has a backend outcome: `checkTxn`'s error, or (a plain transaction whose puts all find what they
need) its run, which for a read-only transaction changes nothing (`txn.srvOps_gets_nil`). -/
theorem backendStep_exists_txn (rq : IRRModel) (log : mvcc.Log) (t : TxnModel) (ho : rq.txn = some t)
    (hk : dispatchKind rq = .txn) : ∃ oc, backendStep rq log oc := by
  unfold backendStep; rw [hk]
  by_cases hc : txn.txnPlain t → ¬ txn.PathsIgnOk (mvcc.stateAfter log)
      (t.branch (txn.txnOk (mvcc.stateAfter log) t))
  · exact ⟨_, t, ho, Or.inl ⟨rfl, hc⟩⟩
  have hp : txn.PathsIgnOk (mvcc.stateAfter log) (t.branch (txn.txnOk (mvcc.stateAfter log) t)) :=
    Classical.byContradiction fun h => hc fun _ => h
  refine ⟨_, t, ho, Or.inr ⟨rfl, fun hro => ?_, hp⟩⟩
  exact txn.srvOps_gets_nil _ _ _ _ (txn.readonly_branch t hro _)

/-- **An outcome the verdict `X` admits past the auth layer**: where every outcome of the inner chain `c` is one
`X` admits (the auth layer passed), and the backend has an outcome. -/
theorem pass_exists (c : Chain) (rq : IRRModel) (log : mvcc.Log) (X : Outcome → Prop)
    (hB : ∃ oc, backendStep rq log oc) (hX : ∀ oc, chainStep backendStep c rq log oc → X oc) :
    ∃ oc, X oc ∧ oc ≠ .rejected .auth := by
  obtain ⟨oc0, h0⟩ := hB
  obtain ⟨oc, h, hne⟩ := chainStep_exists_ne_auth backendStep rq log ⟨oc0, h0, backendStep_ne_auth _ _ _ h0⟩ c
  exact ⟨oc, hX oc h, hne⟩

/-- A check's verdict in the mode `off` is a pass (`isAuthStore`'s `M.isOn = false → err = nil`). -/
theorem permVerdictL_isOn (M : auth.AuthMode) (hs : List auth.AuthState) (ai : auth.AuthInfoM)
    (k e : GoString) (op : auth.PermType) (err : GoInterface)
    (h : auth.permVerdictL M hs ai k e op err) : M.isOn = false → err = GoInterface.nil := by
  cases M with
  | off => intro _; exact h
  | on γa => intro h'; cases h'
  | any => intro h'; cases h'

/-- The permissions a range `o` needs, at the model's range end. -/
def rangePermsM (o : OpFull) : List Perm3 := [(o.key, o.base.rangeEnd, .read)]

/-- The permissions a delete `o` needs, at the model's range end, in the order checked. -/
def deletePermsM (o : OpFull) : List Perm3 :=
  (o.key, o.base.rangeEnd, .write) :: if o.base.prevKV then [(o.key, o.base.rangeEnd, .read)] else []

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The auth applier's store at the latest state**: its `as` field holds a store meeting
`isAuthStoreL` with the server's reader resource and the resource family `L`. -/
def authIsL (E : AEnv GF) (p : Loc) (L : List auth.AuthState → IProp GF) : IProp GF :=
  iprop(∃ st : GoInterface, structFieldRef authApplierV3 go!"as" p ↦□ st ∗
    isAuthStoreL st E.RD E.authMode L)

instance authIsL_persistent (E : AEnv GF) (p : Loc) (L : List auth.AuthState → IProp GF) :
    Persistent (authIsL E p L) := by
  unfold authIsL; infer_instance

/-- `kvPostF` with the outcome's property `X` (`authOutL` for the auth applier's methods); (auth-lease
S2, Q5) with `kvPostF`'s lease class at the owner's item map of the state before the request; (S3a,
Draft rev 5 §3a) with `kvPostF`'s lease exactness at the live set of `kvOwnAt`. -/
def kvPostFL (E : AEnv GF) (c : Chain) (a : GoInterface) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (rq : IRRModel) (log F : mvcc.Log) (R : Outcome → IProp GF) (Pre Post : IProp GF)
    (X : Outcome → Prop) : IProp GF :=
  iprop(∃ oc : Outcome, ⌜chainStep backendStep c rq log oc ∧ floorOkO F log oc ∧ X oc⌝ ∗ R oc ∗
    (∃ L : List w64, ⌜leaseExactL L rq log oc⌝ ∗ kvOwnAt E (oc.logAfter log) L) ∗
    chainRes c a info ∗ (Post ∨ Pre) ∗ chainClass E.authMode info c rq oc ∗
    chainLeaseClass E.authMode info (mvcc.leaseItemsOf (mvcc.stateAfter log)) c rq oc)

/-- `rangePost` with the outcome's property `X`. -/
def rangePostL (E : AEnv GF) (c : Chain) (a : GoInterface) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (rq : IRRModel) (o : OpFull) (log : mvcc.Log) (resp : Loc) (err : GoInterface)
    (X : Outcome → Prop) : IProp GF :=
  iprop(∃ oc : Outcome, ⌜chainStep backendStep c rq log oc ∧ X oc⌝ ∗ rangeOutcomeIs log o resp err oc ∗
    kvOwn E (oc.logAfter log) ∗ chainRes c a info ∗ chainClass E.authMode info c rq oc)

/-- **The certificates of the outcomes `X` admits** (`certPre`'s, for the outcomes of `c` meeting
`X` only; the auth plan's E3f): with the verdict at the latest state, a KV request the auth layer
refuses there never reaches the store, so only the outcomes that verdict lets through need their
log's certificate. In the mode `on` the apply thread can certify no more: a write the model
refuses is the model's log of no committed prefix. -/
def certPreW (E : AEnv GF) (c : Chain) (rq : IRRModel) (log : mvcc.Log) (X : Outcome → Prop) :
    IProp GF :=
  iprop(□ ∀ oc : Outcome, ⌜chainStep backendStep c rq log oc ∧ X oc⌝ -∗
    E.Nx (oc.logAfter log))

instance certPreW_persistent (E : AEnv GF) (c : Chain) (rq : IRRModel) (log : mvcc.Log)
    (X : Outcome → Prop) : Persistent (certPreW E c rq log X) := by
  unfold certPreW; infer_instance

/-- `certPreW` with `v3` (`certPreV`'s). -/
def certPreVW (v3 : Bool) (E : AEnv GF) (c : Chain) (rq : IRRModel) (log : mvcc.Log)
    (X : Outcome → Prop) : IProp GF :=
  if v3 then certPreW E c rq log X else iprop(True)

instance certPreVW_persistent (v3 : Bool) (E : AEnv GF) (c : Chain) (rq : IRRModel)
    (log : mvcc.Log) (X : Outcome → Prop) : Persistent (certPreVW v3 E c rq log X) := by
  unfold certPreVW; split <;> infer_instance

/-- `putPre` with the certificates of the outcomes `X` admits (`certPreW`); (auth-lease S3a2, Draft §3) at the
live set `T` of the method's resources, the outcomes also lease-exact at `T`. -/
def putPreW (E : AEnv GF) (c : Chain) (a : GoInterface) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (r : Loc) (rq : IRRModel) (o : OpFull) (log : mvcc.Log) (Pre Q Post : IProp GF)
    (X : Outcome → Prop) : IProp GF :=
  iprop(⌜rq.put = some o ∧ dispatchKind rq = .put ∧ putOk log ∧
      o.key.length ≤ etcdKeyMax ∧ o.val.length ≤ etcdKeyMax⌝ ∗ txn.putRequestIs r o ∗
    ∃ T : List w64, ⌜(∃ oc, X oc ∧ oc ≠ .rejected .auth) → winTgt E.win rq log T⌝ ∗
      certPreW E c rq log (fun oc => X oc ∧ leaseExactL T rq log oc) ∗ mPreAt E c a info log T Pre Q Post)

/-- `deletePre` with the certificates of the outcomes `X` admits (`certPreW`). -/
def deletePreW (E : AEnv GF) (c : Chain) (a : GoInterface) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (r : Loc) (rq : IRRModel) (o : OpFull) (log : mvcc.Log) (Pre Q Post : IProp GF)
    (X : Outcome → Prop) : IProp GF :=
  iprop(⌜rq.deleteRange = some o ∧ dispatchKind rq = .deleteRange ∧ delOk log o⌝ ∗
    certPreW E c rq log X ∗ txn.deleteRangeRequestIs r o ∗ mPre E c a info log Pre Q Post ∗
    ∃ T : List w64, ⌜(∃ oc, X oc ∧ oc ≠ .rejected .auth) → winTgt E.win rq log T⌝)

/-- `txnPre` with the certificates of the outcomes `X` admits (`certPreW`), at the live set (as `putPreW`). -/
def txnPreW (E : AEnv GF) (c : Chain) (a : GoInterface) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (r : Loc) (rq : IRRModel) (t : TxnModel) (log : mvcc.Log) (Pre Q Post : IProp GF)
    (X : Outcome → Prop) : IProp GF :=
  iprop(⌜rq.txn = some t ∧ dispatchKind rq = .txn ∧ txn.TxnPreA log t ∧ putOk log ∧
      t.putsLe etcdKeyMax⌝ ∗
    txn.txnRequestIs r t ∗ ∃ T : List w64, ⌜((∃ oc, X oc ∧ oc ≠ .rejected .auth) → winTgt E.win rq log T) ∧
      txn.txnKeysNodup t⌝ ∗
      certPreW E c rq log (fun oc => X oc ∧ leaseExactL T rq log oc) ∗ mPreAt E c a info log T Pre Q Post)

end defs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- `certPre` gives the certificates of any outcomes. -/
theorem certPreW_of_certPre (E : AEnv GF) (c : Chain) (rq : IRRModel) (log : mvcc.Log)
    (X : Outcome → Prop) : certPre E c rq log ⊢ certPreW E c rq log X := by
  iintro #H
  iunfold certPre at H
  iunfold certPreW
  iintro !> %oc %h
  iapply H $$ %oc %h.1

/-- `certPreW` for fewer outcomes. -/
theorem certPreW_mono (E : AEnv GF) (c : Chain) (rq : IRRModel) (log : mvcc.Log)
    (X Y : Outcome → Prop) (h : ∀ oc, Y oc → X oc) :
    certPreW E c rq log X ⊢ certPreW E c rq log Y := by
  iintro #H
  iunfold certPreW at H
  iunfold certPreW
  iintro !> %oc %hy
  iapply H $$ %oc %(⟨hy.1, h oc hy.2⟩)

theorem certPreVW_true (E : AEnv GF) (c : Chain) (rq : IRRModel) (log : mvcc.Log)
    (X : Outcome → Prop) : certPreVW true E c rq log X ⊢ certPreW E c rq log X := by
  simp only [certPreVW, ↓reduceIte]; exact .rfl

theorem certPreVW_of_certPreV (v3 : Bool) (E : AEnv GF) (c : Chain) (rq : IRRModel)
    (log : mvcc.Log) (X : Outcome → Prop) : certPreV v3 E c rq log ⊢ certPreVW v3 E c rq log X := by
  cases v3
  · simp only [certPreV, certPreVW, Bool.false_eq_true, ↓reduceIte]; iintro -; itrivial
  · simp only [certPreV, certPreVW, ↓reduceIte]; exact certPreW_of_certPre E c rq log X

/-- **Past the auth layer's check**: when every outcome of the inner chain `c` is one `X` admits
(the check passed at the latest state), the auth chain's `certPreW` is the inner chain's
`certPre`. -/
theorem certPreW_inner (E : AEnv GF) (on : Bool) (c : Chain) (rq : IRRModel) (log : mvcc.Log)
    (X : Outcome → Prop) (h : ∀ oc, chainStep backendStep c rq log oc → X oc) :
    certPreW E (.auth on c) rq log X ⊢ certPre E c rq log := by
  iintro #H
  iunfold certPreW at H
  iunfold certPre
  iintro !> %oc %hs
  iapply H $$ %oc %(⟨by simp only [chainStep]; split <;> simp [hs], h oc hs⟩)

/-- **Past the auth layer's check, at the live set `T`** (auth-lease S3a2, Draft §3): the latest certificate of
the outcomes meeting `X` and lease-exact at `T` is the inner chain's `certPreT` at `T`, when every inner outcome
meets `X`. -/
theorem certPreW_innerT (E : AEnv GF) (on : Bool) (c : Chain) (rq : IRRModel) (log : mvcc.Log)
    (T : List w64) (X : Outcome → Prop) (h : ∀ oc, chainStep backendStep c rq log oc → X oc) :
    certPreW E (.auth on c) rq log (fun oc => X oc ∧ leaseExactL T rq log oc) ⊢
      certPreT E c rq log T := by
  iintro #H
  iunfold certPreW at H
  iunfold certPreT
  iintro !> %oc %hs
  iapply H $$ %oc %(⟨by simp only [chainStep]; split <;> simp [hs.1], h oc hs.1, hs.2⟩)

/-- **The dispatch's tie** (auth-lease S3a2, Draft §3): a certificate whose lease-exactness at `T` is guarded by
`E.lg` is one at the live set `L` of the method's resources, when the two agree in a cluster that grants
leases. -/
theorem certPreW_tie (E : AEnv GF) (c : Chain) (rq : IRRModel) (log : mvcc.Log)
    (L T : List w64) (X : Outcome → Prop) (hLT : E.lg = true → L = T) :
    certPreW E c rq log (fun oc => X oc ∧ (E.lg = true → leaseExactL T rq log oc)) ⊢
      certPreW E c rq log (fun oc => X oc ∧ leaseExactL L rq log oc) := by
  iapply certPreW_mono
  intro oc ⟨hx, hl⟩
  exact ⟨hx, fun hg => hLT hg ▸ hl⟩

theorem rangePostL_rangePost (E : AEnv GF) (c : Chain) (a : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (rq : IRRModel) (o : OpFull) (log : mvcc.Log)
    (resp : Loc) (err : GoInterface) (X : Outcome → Prop) :
    rangePostL E c a info rq o log resp err X ⊢ rangePost E c a info rq o log resp err := by
  unfold rangePostL rangePost
  iintro ⟨%oc, %H, HR⟩
  iexists oc; iframe HR; ipureintro; exact H.1

/-- `auth_reject_kvPostF` with the outcome's property. -/
theorem auth_reject_kvPostFL (E : AEnv GF) (on : Bool) (c : Chain) (p : Loc)
    (inner : GoInterface) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (rq : IRRModel)
    (log F : mvcc.Log) (R : Outcome → IProp GF)
    (P Pre Q Post : IProp GF) (X : Outcome → Prop) (hk : authChecks (dispatchKind rq) = true)
    (hm : authMayReject on rq) (hX : X (.rejected .auth)) :
    structFieldRef authApplierV3 go!"applierV3" p ↦□ inner ⊢
      R (.rejected .auth) -∗ kvOwn E log -∗
      structFieldRef authApplierV3 go!"authInfo" p ↦ info -∗
      chainResAny c inner -∗ srvApi.csContractA P E.f Pre Q Post -∗
      kvPostFL E (.auth on c) (interface.mkOk (go.GoType.PointerType authApplierV3.ty) #p) info rq
        log F R Pre Post X := by
  iintro #Happ HR Hkv Hinfo Hres Hcs
  ihave HPre := csContract_pre _ _ _ _ _ $$ Hcs
  ihave Hkv := kvOwn_rejected E log rq .auth (by decide) $$ Hkv
  iunfold kvPostFL
  iexists (.rejected .auth)
  isplitr
  · ipureintro
    exact ⟨by simp [chainStep, hk, hm], (fun _ _ h => by cases h), hX⟩
  simp only [Outcome.logAfter]
  iframe HR Hkv
  isplitl [Hinfo Hres]
  · iapply chainRes_auth_in c p inner info $$ Happ Hinfo Hres
  isplitl [HPre]
  · iright; iexact HPre
  isplitl []
  · iapply chainClass_auth_rejected
  · iapply chainLeaseClass_auth_rejected

/-- `auth_pass_kvPostF` with the outcome's property, of every inner outcome. -/
theorem auth_pass_kvPostFL (E : AEnv GF) (on : Bool) (c : Chain) (p : Loc)
    (inner : GoInterface) (info info' : go_etcd_io.etcd.server.v3.auth.AuthInfo) (rq : IRRModel)
    (log F : mvcc.Log) (R : Outcome → IProp GF) (Pre Post : IProp GF) (X : Outcome → Prop)
    (hX : ∀ oc, chainStep backendStep c rq log oc → X oc) :
    structFieldRef authApplierV3 go!"applierV3" p ↦□ inner ⊢
      kvPostF E c inner info' rq log F R Pre Post -∗
      structFieldRef authApplierV3 go!"authInfo" p ↦ info -∗ reqClass E.authMode info rq -∗
      reqLeaseClass E.authMode info (mvcc.leaseItemsOf (mvcc.stateAfter log)) rq -∗
      kvPostFL E (.auth on c) (interface.mkOk (go.GoType.PointerType authApplierV3.ty) #p) info rq
        log F R Pre Post X := by
  iintro #Happ Hpost Hinfo #Hcls #Hlc
  iunfold kvPostF at Hpost
  iunfold kvPostFL
  icases Hpost with ⟨%oc, %Hst, HR, Hkv, Hres, HPP, -, -⟩
  iexists oc
  iframe HR Hkv HPP
  isplitr
  · ipureintro
    refine ⟨?_, Hst.2, hX oc Hst.1⟩
    simp only [chainStep]
    split <;> simp [Hst.1]
  ihave Hres := chainResAny_of c inner info' $$ Hres
  isplitl [Hinfo Hres]
  · iapply chainRes_auth_in c p inner info $$ Happ Hinfo Hres
  isplitl []
  · iapply chainClass_auth_pass $$ Hcls
  · iapply chainLeaseClass_auth_pass $$ Hlc

end proof

end apply

/-! ## The specs -/

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **`Range` on the apply thread**: `Range.spec`'s, the outcome decided at the latest state
(`authOutL`) for the read as the check saw it. -/
abbrev apply.authApplierV3.Range.specL : Prop :=
  ∀ (E : apply.AEnv GF) (c : apply.Chain) (inner : GoInterface) (p r : Loc) (rq : IRRModel)
    (o : OpFull) (log : mvcc.Log) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (L : List auth.AuthState → IProp GF) (hs : List auth.AuthState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.authIs E p inner ∗ apply.authIsL E p L ∗ apply.applierSpec E c inner ∗
      apply.rangePre E (.auth E.authOn c) (interface.mkOk (go.GoType.PointerType authApplierV3.ty) #p) info r rq o log ∗
      L hs ∗ apply.applyTok E }}
    (App (Val (p @!! go.GoType.PointerType authApplierV3.ty @!! go!"Range")) (Val #r))
  {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
      apply.rangePostL E (.auth E.authOn c) (interface.mkOk (go.GoType.PointerType authApplierV3.ty) #p) info rq o log resp err
        (fun oc => ∃ e, apply.authEndOf o.base.rangeEnd e ∧
          apply.authOutL E.authMode hs (auth.authInfoM info) c rq log [(o.key, e, .read)] oc) ∗
      L hs ∗ apply.traceRes trace ∗ apply.applyTok E }}

/-- **`DeleteRange` on the apply thread**: `DeleteRange.spec`'s, the outcome decided at the
latest state for the write (and with `PrevKv` the read) as the checks saw them; the certificates
asked only of the outcomes that verdict admits (`deletePreW`, E3f). -/
abbrev apply.authApplierV3.DeleteRange.specL : Prop :=
  ∀ (E : apply.AEnv GF) (c : apply.Chain) (inner : GoInterface) (p r : Loc) (rq : IRRModel)
    (o : OpFull) (log F : mvcc.Log) (Pre Q Post : IProp GF)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (L : List auth.AuthState → IProp GF) (hs : List auth.AuthState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.authIs E p inner ∗ apply.authIsL E p L ∗ apply.applierSpec E c inner ∗
      apply.deletePreW E (.auth E.authOn c) (interface.mkOk (go.GoType.PointerType authApplierV3.ty) #p) info r rq o log Pre Q Post
        (fun oc => ∃ e, apply.authEndOf o.base.rangeEnd e ∧
          apply.authOutL E.authMode hs (auth.authInfoM info) c rq log
            ((o.key, e, .write) :: if o.base.prevKV then [(o.key, e, .read)] else []) oc) ∗
      srvApi.kvLogLb E.γs F ∗ L hs ∗ apply.applyTok E }}
    (App (Val (p @!! go.GoType.PointerType authApplierV3.ty @!! go!"DeleteRange")) (Val #r))
  {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
      apply.kvPostFL E (.auth E.authOn c) (interface.mkOk (go.GoType.PointerType authApplierV3.ty) #p) info rq log F
        (apply.deleteAnswerIs log o resp err) Pre Post
        (fun oc => ∃ e, apply.authEndOf o.base.rangeEnd e ∧
          apply.authOutL E.authMode hs (auth.authInfoM info) c rq log
            ((o.key, e, .write) :: if o.base.prevKV then [(o.key, e, .read)] else []) oc) ∗
      L hs ∗ apply.traceRes trace ∗ apply.applyTok E }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

theorem apply.authApplierV3.Range.wp_latest :
    apply.authApplierV3.Range.specL (GF := GF) (hG := hG) := by
  intro E c inner p r rq o log info L hs
  wp_start as ⟨#Hauth, #HauthL, #Hinner, Hpre, HL, Htt⟩
  iunfold apply.authIs at Hauth
  icases Hauth with ⟨#Happ, -, -, -⟩
  iunfold apply.authIsL at HauthL
  icases HauthL with ⟨%st, #Hasf, #Hst⟩
  iunfold apply.rangePre at Hpre
  icases Hpre with ⟨%Hk, #Hr, Hkv, Hres⟩
  ihave ⟨Hard, Hkv⟩ := apply.kvOwn_rd E log $$ Hkv
  ihave ⟨Hinfo, Hres⟩ := apply.chainRes_auth_out c p inner info $$ Happ Hres
  ihave #Hst' := Hst
  iunfold apply.isAuthStoreL at Hst'
  icases Hst' with ⟨%sti, %Hsti, -, #HRange, -⟩
  iunfold apply.permCheck3L at HRange
  ihave #Hr' := Hr
  iunfold txn.rangeRequestIs at Hr'
  icases Hr' with ⟨%Hrn, %ksl, %esl, %k, %e, %x1, %x2, %x3, %x4, %x5, %x6, %x7, %x8, %x9, %x10,
    %x11, #HK, #Hk, #HE, #He, -, -, -, -, -, -, -, -, -, -, -, %Ho, %Hkb⟩
  ihave %Hel := ownSlice_len _ _ _ $$ He
  have hkey : o.key = k := by rw [Ho]; simp only [txn.rangeOpOf.proj_key]
  have hre : o.base.rangeEnd = txn.rangeEndOf esl e := by rw [Ho]; simp only [txn.rangeOpOf.proj_base]
  have hend : apply.authEndOf o.base.rangeEnd e := by rw [hre]; exact apply.authEndOf_rangeEndOf esl e Hel.1
  subst Hsti
  ihave #Hin := Hinner
  iunfold apply.applierSpec at Hin
  icases Hin with ⟨%bi, %Hbi, #Ht⟩
  subst Hbi
  iunfold apply.applierTriples at Ht
  icases Ht with ⟨-, -, #HRangeI, -⟩
  wp_auto
  wp_apply HRange $$ %_ %info %(DFrac.own 1) %ksl %esl %k %e %DFrac.discard %DFrac.discard %hs [Hinfo Hard HL]
    as %err ⟨Hinfo, -, -, Hard, HL, #HeI, %Hvl, #Hpv⟩
  · iframe; iframe #; try (ipureintro; exact Hkb)
  have Hoff := apply.permVerdictL_isOn _ _ _ _ _ _ _ Hvl
  have Hone := apply.verdictL_one _ _ _ _ _ _ _ Hvl
  ihave Hkv := Hkv $$ Hard
  cases err with
  | ok e' =>
    have hon : E.authOn = true := by cases h : E.authOn <;> first | rfl | cases Hoff h
    wp_auto
    iapply HΦ
    iframe HL Htt
    isplitl
    rotate_left
    · iapply apply.traceRes_null
    iunfold apply.rangePostL
    iexists (.rejected .auth)
    isplitr
    · ipureintro
      refine ⟨by simp [apply.chainStep, apply.authChecks, Hk.2.1, apply.authMayReject, hon], ?_⟩
      refine ⟨e, hend, Or.inl ⟨rfl, ?_⟩⟩
      rw [← hkey] at Hone
      exact Hone.2 (fun h => by cases h)
    simp only [apply.rangeOutcomeIs, apply.rejErrIs, apply.Outcome.logAfter]
    iframe Hkv
    isplitr
    · isplitr
      · ipureintro; trivial
      · iframe HeI; ipureintro; simp
    isplitl [Hinfo Hres]
    · iapply apply.chainRes_auth_in c p (.ok bi) info $$ Happ Hinfo Hres
    iapply apply.chainClass_auth_rejected
  | nil =>
  wp_auto
  ihave #Hrc' : apply.rangeClass (GF := GF) E.authMode info o $$ []
  · rw [← hkey]
    iapply (apply.rangeClass_of_verdict E.authMode info o esl e Hel.1 hre) $$ Hpv
  ihave #Hrc := apply.reqClass_range E.authMode info rq o Hk.1 Hk.2.1 $$ Hrc'
  iunfold apply.chainResAny at Hres
  icases Hres with ⟨%info', Hres⟩
  wp_apply HRangeI $$ %r %rq %o %log %info' [Htt Hkv Hres] as %resp %trace %err ⟨Hpost, Htrc, Htt⟩
  · iframe Htt
    iunfold apply.rangePre
    iframe
    iframe #
    ipureintro; exact Hk
  iapply HΦ
  iframe HL Htt
  isplitr [Htrc]
  rotate_left
  · iexact Htrc
  iunfold apply.rangePost at Hpost
  iunfold apply.rangePostL
  icases Hpost with ⟨%oc, %Hst, HR, Hkv, Hres, -⟩
  iexists oc
  iframe HR Hkv
  isplitr
  · ipureintro
    refine ⟨?_, e, hend, Or.inr ⟨Hst, ?_⟩⟩
    · simp only [apply.chainStep, apply.authChecks, Hk.2.1]
      simp [Hst]
    · rw [← hkey] at Hone
      exact Hone.1 rfl
  ihave Hres := apply.chainResAny_of c _ info' $$ Hres
  isplitl [Hinfo Hres]
  · iapply apply.chainRes_auth_in c p (.ok bi) info $$ Happ Hinfo Hres
  iapply apply.chainClass_auth_pass $$ Hrc

theorem apply.authApplierV3.DeleteRange.wp_latest :
    apply.authApplierV3.DeleteRange.specL (GF := GF) (hG := hG) := by
  intro E c inner p r rq o log F Pre Q Post info L hs
  wp_start as ⟨#Hauth, #HauthL, #Hinner, Hpre, #HF, HL, Htt⟩
  iunfold apply.authIs at Hauth
  icases Hauth with ⟨#Happ, -, -, -⟩
  iunfold apply.authIsL at HauthL
  icases HauthL with ⟨%st, #Hasf, #Hst⟩
  iunfold apply.deletePreW at Hpre
  icases Hpre with ⟨%Hk, #Hcp, #Hr, Hm, %Tw, %Hwt⟩
  icases apply.mPre_split_chain _ _ _ _ _ _ _ _ $$ Hm with ⟨Hm, Hres⟩
  ihave ⟨Hard, Hkv⟩ := apply.mPreRest_rd E log Pre Q Post $$ Hm
  ihave ⟨Hinfo, Hres⟩ := apply.chainRes_auth_out c p inner info $$ Happ Hres
  ihave #Hst' := Hst
  iunfold apply.isAuthStoreL at Hst'
  icases Hst' with ⟨%sti, %Hsti, -, #HRange, #HDel, -⟩
  ihave #Hrl0 : apply.reqLeaseClass (GF := GF) E.authMode info (mvcc.leaseItemsOf (mvcc.stateAfter log)) rq $$ []
  · iapply apply.reqLeaseClass_noLease; rw [Hk.2.1]; exact ⟨by decide, by decide, by decide⟩
  iunfold apply.permCheck3L at HRange
  iunfold apply.permCheck3L at HDel
  ihave #Hr' := Hr
  iunfold txn.deleteRangeRequestIs at Hr'
  icases Hr' with ⟨%Hrn, %ksl, %esl, %k, %e, %pk, #HK, #Hk, #HE, #He, #HPK, %Ho, %Hkb⟩
  ihave %Hel := ownSlice_len _ _ _ $$ He
  have hkey : o.key = k := by rw [Ho]; simp only [txn.deleteOpOf.proj_key]
  have hre : o.base.rangeEnd = txn.rangeEndOf esl e := by rw [Ho]; simp only [txn.deleteOpOf.proj_base]
  have hpk : o.base.prevKV = pk := by rw [Ho]; simp only [txn.deleteOpOf.proj_base]
  have hend : apply.authEndOf o.base.rangeEnd e := by rw [hre]; exact apply.authEndOf_rangeEndOf esl e Hel.1
  subst Hsti
  ihave #Hin := Hinner
  iunfold apply.applierSpec at Hin
  icases Hin with ⟨%bi, %Hbi, #Ht⟩
  subst Hbi
  iunfold apply.applierTriples at Ht
  icases Ht with ⟨-, #HDelI, -⟩
  have hk : apply.authChecks (dispatchKind rq) = true := by rw [Hk.2.1]; rfl
  wp_auto
  wp_apply HDel $$ %_ %info %(DFrac.own 1) %ksl %esl %k %e %DFrac.discard %DFrac.discard %hs [Hinfo Hard HL]
    as %err ⟨Hinfo, -, -, Hard, HL, #HeI, %Hvw, #Hpw⟩
  · iframe; iframe #; try (ipureintro; exact Hkb)
  have Hoff := apply.permVerdictL_isOn _ _ _ _ _ _ _ Hvw
  have Honew := apply.verdictL_one _ _ _ _ _ _ _ Hvw
  ihave Hkv := Hkv $$ Hard
  cases err with
  | ok e' =>
    wp_auto
    iapply HΦ
    iframe HL Htt
    isplitl
    rotate_left
    · iapply apply.traceRes_null
    icases apply.mPreRest_reject_cs _ _ _ _ _ $$ Hkv with ⟨Hkv, %B, Hcs⟩
    have hX : (fun oc => ∃ e, apply.authEndOf o.base.rangeEnd e ∧
        apply.authOutL E.authMode hs (auth.authInfoM info) c rq log
          ((o.key, e, .write) :: if o.base.prevKV then [(o.key, e, .read)] else []) oc)
        (.rejected .auth) := by
      refine ⟨e, hend, Or.inl ⟨rfl, ?_⟩⟩
      rw [← hkey] at Honew
      exact apply.refusedL_append_left _ _ _ [(o.key, e, .write)]
        (if o.base.prevKV then [(o.key, e, .read)] else []) (Honew.2 (fun h => by cases h))
    iapply apply.auth_reject_kvPostFL E E.authOn c p (.ok bi) info rq log F _ _ Pre Q Post _ hk
      (Or.inl (by cases h : E.authOn <;> first | rfl | cases Hoff h)) hX $$ Happ [] Hkv Hinfo
      Hres Hcs
    simp only [apply.deleteAnswerIs, apply.deleteOutcomeIs, apply.rejErrIs]
    isplitr
    · ipureintro; trivial
    · iframe HeI; ipureintro; simp
  | nil =>
  wp_auto
  cases pk
  · wp_auto
    ihave #Hdc : apply.deleteClass (GF := GF) E.authMode info o $$ []
    · rw [← hkey]
      iapply (apply.deleteClass_of_verdicts E.authMode info o esl e Hel.1 hre)
      iframe Hpw
      iintro %h; rw [hpk] at h; cases h
    ihave #Hrc := apply.reqClass_deleteRange E.authMode info rq o Hk.1 Hk.2.1 $$ Hdc
    have hXp : ∀ oc, apply.chainStep apply.backendStep c rq log oc → ∃ e, apply.authEndOf o.base.rangeEnd e ∧
        apply.authOutL E.authMode hs (auth.authInfoM info) c rq log
          ((o.key, e, .write) :: if o.base.prevKV then [(o.key, e, .read)] else []) oc := fun oc hoc => by
      refine ⟨e, hend, Or.inr ⟨hoc, ?_⟩⟩
      rw [hpk]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [← hkey] at Honew
      exact Honew.1 rfl
    ihave #Hcp := apply.certPreW_inner E E.authOn c rq log _ hXp $$ Hcp
    iunfold apply.chainResAny at Hres
    icases Hres with ⟨%info', Hres⟩
    wp_apply HDelI $$ %r %rq %o %log %F %Pre %Q %Post %info' [Htt Hkv Hres] as %resp %trace %err ⟨Hpost, Htrc, Htt⟩
    · iframe Htt
      iunfold apply.deletePre
      iframe #
      isplitr
      · ipureintro; exact Hk
      isplitl
      · iapply apply.mPre_of_rest
        iframe
      iexists Tw; ipureintro
      exact Hwt (apply.pass_exists c rq log _ (apply.backendStep_exists_delete rq log o Hk.1 Hk.2.1) hXp)
    iapply HΦ
    iframe HL Htt
    isplitr [Htrc]
    rotate_left
    · iexact Htrc
    iapply apply.auth_pass_kvPostFL E E.authOn c p (.ok bi) info info' rq log F _ Pre Post _ ?_ $$ Happ Hpost Hinfo Hrc Hrl0
    intro oc hoc
    refine ⟨e, hend, Or.inr ⟨hoc, ?_⟩⟩
    rw [hpk]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← hkey] at Honew
    exact Honew.1 rfl
  wp_auto
  ihave ⟨Hard, Hkv⟩ := apply.mPreRest_rd E log Pre Q Post $$ Hkv
  wp_apply HRange $$ %_ %info %(DFrac.own 1) %ksl %esl %k %e %DFrac.discard %DFrac.discard %hs [Hinfo Hard HL]
    as %err ⟨Hinfo, -, -, Hard, HL, #HeI, %Hvr, #Hpr⟩
  · iframe; iframe #; try (ipureintro; exact Hkb)
  have Hoff' := apply.permVerdictL_isOn _ _ _ _ _ _ _ Hvr
  have Honer := apply.verdictL_one _ _ _ _ _ _ _ Hvr
  ihave Hkv := Hkv $$ Hard
  cases err with
  | ok e' =>
    wp_auto
    iapply HΦ
    iframe HL Htt
    isplitl
    rotate_left
    · iapply apply.traceRes_null
    icases apply.mPreRest_reject_cs _ _ _ _ _ $$ Hkv with ⟨Hkv, %B, Hcs⟩
    have hX : (fun oc => ∃ e, apply.authEndOf o.base.rangeEnd e ∧
        apply.authOutL E.authMode hs (auth.authInfoM info) c rq log
          ((o.key, e, .write) :: if o.base.prevKV then [(o.key, e, .read)] else []) oc)
        (.rejected .auth) := by
      refine ⟨e, hend, Or.inl ⟨rfl, ?_⟩⟩
      rw [hpk]
      simp only [↓reduceIte]
      rw [← hkey] at Honer
      exact apply.refusedL_append_right _ _ _ [(o.key, e, .write)] [(o.key, e, .read)]
        (Honer.2 (fun h => by cases h))
    iapply apply.auth_reject_kvPostFL E E.authOn c p (.ok bi) info rq log F _ _ Pre Q Post _ hk
      (Or.inl (by cases h : E.authOn <;> first | rfl | cases Hoff' h)) hX $$ Happ [] Hkv Hinfo
      Hres Hcs
    simp only [apply.deleteAnswerIs, apply.deleteOutcomeIs, apply.rejErrIs]
    isplitr
    · ipureintro; trivial
    · iframe HeI; ipureintro; simp
  | nil =>
  wp_auto
  ihave #Hdc : apply.deleteClass (GF := GF) E.authMode info o $$ []
  · rw [← hkey]
    iapply (apply.deleteClass_of_verdicts E.authMode info o esl e Hel.1 hre)
    iframe Hpw
    iintro %_; iexact Hpr
  ihave #Hrc := apply.reqClass_deleteRange E.authMode info rq o Hk.1 Hk.2.1 $$ Hdc
  have hXp : ∀ oc, apply.chainStep apply.backendStep c rq log oc → ∃ e, apply.authEndOf o.base.rangeEnd e ∧
      apply.authOutL E.authMode hs (auth.authInfoM info) c rq log
        ((o.key, e, .write) :: if o.base.prevKV then [(o.key, e, .read)] else []) oc := fun oc hoc => by
    refine ⟨e, hend, Or.inr ⟨hoc, ?_⟩⟩
    rw [hpk]
    simp only [↓reduceIte]
    rw [← hkey] at Honew Honer
    exact apply.passedL_append _ _ _ [(o.key, e, .write)] [(o.key, e, .read)] (Honew.1 rfl)
      (Honer.1 rfl)
  ihave #Hcp := apply.certPreW_inner E E.authOn c rq log _ hXp $$ Hcp
  iunfold apply.chainResAny at Hres
  icases Hres with ⟨%info', Hres⟩
  wp_apply HDelI $$ %r %rq %o %log %F %Pre %Q %Post %info' [Htt Hkv Hres] as %resp %trace %err ⟨Hpost, Htrc, Htt⟩
  · iframe Htt
    iunfold apply.deletePre
    iframe #
    isplitr
    · ipureintro; exact Hk
    isplitl
    · iapply apply.mPre_of_rest
      iframe
    iexists Tw; ipureintro
    exact Hwt (apply.pass_exists c rq log _ (apply.backendStep_exists_delete rq log o Hk.1 Hk.2.1) hXp)
  iapply HΦ
  iframe HL Htt
  isplitr [Htrc]
  rotate_left
  · iexact Htrc
  iapply apply.auth_pass_kvPostFL E E.authOn c p (.ok bi) info info' rq log F _ Pre Post _ ?_ $$ Happ Hpost Hinfo Hrc Hrl0
  intro oc hoc
  refine ⟨e, hend, Or.inr ⟨hoc, ?_⟩⟩
  rw [hpk]
  simp only [↓reduceIte]
  rw [← hkey] at Honew Honer
  exact apply.passedL_append _ _ _ [(o.key, e, .write)] [(o.key, e, .read)] (Honew.1 rfl) (Honer.1 rfl)

end proof

end EtcdGrove
end Perennial
