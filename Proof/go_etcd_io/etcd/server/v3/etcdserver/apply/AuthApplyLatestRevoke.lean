/-
**The auth applier's `LeaseRevoke` at the latest state** (auth-lease S2, `notes/auth-lease-s2-draft.md`
§4): `checkLeasePuts` over the lease owner's resource (`AuthApplyLatestPut.lean`), then the inner
applier's `LeaseRevoke` (`apply/auth.go:191-196`); the outcome decided at the latest state for the lease
(`authOutLL … [] I [id]`). The admin shortcut has no revision condition and a lease attaching no key
passes for any principal, the empty one included (`leasePassedL`). The floor is `[]`: a revocation's
floor fact is nobody's (`kvFloorOk` covers put, delete and txn only).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthApplyLatestPut
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthLemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `revokePre` with the certificates of the outcomes `X` admits (`certPreW`, as `putPreW`). -/
def apply.revokePreW (E : apply.AEnv GF) (c : apply.Chain) (a : GoInterface)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (r : Loc) (rq : IRRModel) (id : w64)
    (log : mvcc.Log) (T : List w64) (rs : apply.RestM) (Pre Q Post : IProp GF)
    (X : apply.Outcome → Prop) : IProp GF :=
  iprop(⌜rq.leaseRevoke = some id ∧ dispatchKind rq = .leaseRevoke ∧ apply.putOk log ∧
      (mvcc.stateAfter log).length ≤ 2 ^ 62⌝ ∗
    apply.certPreW E c rq log X ∗
    apply.leaseRevokeIs r id ∗ apply.mPre E c a info log Pre Q Post ∗ apply.revokeRes E T rs ∗
    ⌜(∃ oc, X oc ∧ oc ≠ .rejected .auth) → apply.winTgt E.win rq log T⌝)

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **`LeaseRevoke` on the apply thread** (auth-lease S2): `LeaseRevoke.spec`'s, the outcome decided at
the latest state for the lease at the owner's item map of the log's state (`authOutLL … [] I [id]`), the
certificates asked only of the outcomes that verdict admits (`revokePreW`). -/
abbrev apply.authApplierV3.LeaseRevoke.specL : Prop :=
  ∀ (E : apply.AEnv GF) (c : apply.Chain) (inner : GoInterface) (p r : Loc) (rq : IRRModel) (id : w64)
    (log : mvcc.Log) (T : List w64) (rs : apply.RestM) (Pre Q Post : IProp GF)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (L : List auth.AuthState → IProp GF) (hs : List auth.AuthState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.authIs E p inner ∗ apply.authIsL E p L ∗ apply.applierSpec E c inner ∗ apply.applyTok E ∗
      apply.revokePreW E (.auth E.authOn c) (interface.mkOk (go.GoType.PointerType authApplierV3.ty) #p)
        info r rq id log T rs Pre Q Post
        (apply.authOutLL E.authMode hs (auth.authInfoM info) c rq log []
          (mvcc.leaseItemsOf (mvcc.stateAfter log)) [id]) ∗
      L hs }}
    (App (Val (p @!! go.GoType.PointerType authApplierV3.ty @!! go!"LeaseRevoke")) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      apply.applyTok E ∗ L hs ∗
      apply.kvPostFL E (.auth E.authOn c) (interface.mkOk (go.GoType.PointerType authApplierV3.ty) #p)
        info rq log []
        (fun o => iprop(apply.revokeOutcomeIs resp err o ∗ apply.revokeResAfter E rq T rs resp err o))
        Pre Post
        (apply.authOutLL E.authMode hs (auth.authInfoM info) c rq log []
          (mvcc.leaseItemsOf (mvcc.stateAfter log)) [id]) }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- `auth_pass_kvPostFL` from the inner chain's `kvPost` (no floor), at the floor `[]`. -/
theorem apply.auth_pass_kvPostFL_nil (E : apply.AEnv GF) (on : Bool) (c : apply.Chain) (p : Loc)
    (inner : GoInterface) (info info' : go_etcd_io.etcd.server.v3.auth.AuthInfo) (rq : IRRModel)
    (log : mvcc.Log) (R : apply.Outcome → IProp GF) (Pre Post : IProp GF) (X : apply.Outcome → Prop)
    (hX : ∀ oc, apply.chainStep apply.backendStep c rq log oc → X oc)
    (hk : dispatchKind rq = .leaseRevoke) :
    structFieldRef authApplierV3 go!"applierV3" p ↦□ inner ⊢
      apply.kvPost E c inner info' rq log R Pre Post -∗
      structFieldRef authApplierV3 go!"authInfo" p ↦ info -∗ apply.reqClass E.authMode info rq -∗
      apply.reqLeaseClass E.authMode info (mvcc.leaseItemsOf (mvcc.stateAfter log)) rq -∗
      apply.kvPostFL E (.auth on c) (interface.mkOk (go.GoType.PointerType authApplierV3.ty) #p) info rq
        log [] R Pre Post X := by
  iintro #Happ Hpost Hinfo #Hcls #Hlc
  iunfold apply.kvPost at Hpost
  iunfold apply.kvPostFL
  icases Hpost with ⟨%oc, %Hst, HR, Hkv, Hres, HPP, -, -⟩
  ihave Hkv := apply.kvOwn_atP E _ _
    (fun L => apply.leaseExactL_other L rq log oc (by rw [hk]; decide) (by rw [hk]; decide)) $$ Hkv
  iexists oc
  iframe HR Hkv HPP
  isplitr
  · ipureintro
    refine ⟨?_, fun _ _ _ => List.nil_prefix, hX oc Hst⟩
    simp only [apply.chainStep]
    split <;> simp [Hst]
  ihave Hres := apply.chainResAny_of c inner info' $$ Hres
  isplitl [Hinfo Hres]
  · iapply apply.chainRes_auth_in c p inner info $$ Happ Hinfo Hres
  isplitl []
  · iapply apply.chainClass_auth_pass $$ Hcls
  · iapply apply.chainLeaseClass_auth_pass $$ Hlc

theorem apply.authApplierV3.LeaseRevoke.wp_latest
    (hLP : apply.checkLeasePuts.specL (GF := GF) (hG := hG)) :
    apply.authApplierV3.LeaseRevoke.specL (GF := GF) (hG := hG) := by
  intro E c inner p r rq id log T rs Pre Q Post info L hs
  wp_start as ⟨#Hauth, #HauthL, #Hinner, Htt, Hpre, HL⟩
  iunfold apply.authIs at Hauth
  icases Hauth with ⟨#Happ, -, ⟨%le, #Hlef, #Hle⟩, -⟩
  iunfold apply.isApplyLessor at Hle
  icases Hle with ⟨#Htl, -⟩
  iunfold apply.authIsL at HauthL
  icases HauthL with ⟨%st, #Hasf, #Hst⟩
  iunfold apply.revokePreW at Hpre
  icases Hpre with ⟨%Hk, #Hcp, #Hr, Hm, Hrr, %Hwt⟩
  icases apply.mPre_split_chain _ _ _ _ _ _ _ _ $$ Hm with ⟨Hm, Hres⟩
  ihave ⟨Hard, %Lw, Hu, Hkv⟩ := apply.mPreRest_lend E log Pre Q Post $$ Hm
  ihave ⟨Hinfo, Hres⟩ := apply.chainRes_auth_out c p inner info $$ Happ Hres
  ihave #Hr' := Hr
  iunfold apply.leaseRevokeIs at Hr'
  icases Hr' with ⟨%Hrn, #HrID⟩
  have hk : apply.authChecks (dispatchKind rq) = true := by rw [Hk.2.1]; rfl
  wp_auto
  wp_apply (hLP st le E.RD E.authMode L hs (mvcc.api.mvccLeases E.γ) Lw
      (mvcc.leaseItemsOf (mvcc.stateAfter log)) _ info (DFrac.own 1) id)
    $$ [$Hst $Htl $Hu $Hinfo $Hard $HL] as %err ⟨Hu, Hinfo, Hard, HL, #HeI, %Hoff, #Hlc, %Hvd⟩
  ihave Hkv := Hkv $$ Hard Hu
  cases err with
  | ok e' =>
    wp_auto
    iapply HΦ
    iframe Htt HL
    icases apply.mPreRest_reject_cs _ _ _ _ _ $$ Hkv with ⟨Hkv, %B, Hcs⟩
    iapply apply.auth_reject_kvPostFL E E.authOn c p inner info rq log [] _ _ Pre Q Post _ hk
      (Or.inl (by cases h : E.authOn <;> first | rfl | cases Hoff h))
      (Or.inl ⟨rfl, Or.inr ⟨id, List.mem_singleton.2 rfl, Hvd.2 (fun h => by cases h)⟩⟩)
      $$ Happ [Hrr] Hkv Hinfo Hres Hcs
    simp only [apply.revokeOutcomeIs, apply.rejErrIs]
    iunfold apply.revokeRes at Hrr
    icases Hrr with ⟨Hrdat, Hrev, HltT, HRO, -⟩
    iunfold apply.revokeResAfter
    rw [apply.revokeIds_rejected, apply.revokeRest_rejected]
    ihave #Hra := apply.revokeAnswer_err (GF := GF) E rq null (GoInterface.ok e')
      (by intro h; cases h)
    iframe Hrdat Hrev HltT HRO Hra
    isplitr
    · ipureintro; trivial
    · iframe HeI; ipureintro; simp
  | nil =>
  have Hpass : ∀ oc, apply.chainStep apply.backendStep c rq log oc →
      apply.authOutLL E.authMode hs (auth.authInfoM info) c rq log []
        (mvcc.leaseItemsOf (mvcc.stateAfter log)) [id] oc := by
    intro oc hoc
    exact Or.inr ⟨hoc, apply.passedL_nil _ _ _,
      fun id' hid => by rw [List.mem_singleton.1 hid]; exact Hvd.1 rfl⟩
  ihave #Hcp := apply.certPreW_inner E E.authOn c rq log _ Hpass $$ Hcp
  ihave #Hin := Hinner
  iunfold apply.applierSpec at Hin
  icases Hin with ⟨%bi, %Hbi, #Ht⟩
  subst Hbi
  iunfold apply.applierTriples at Ht
  icases Ht with ⟨-, -, -, -, #HRevI, -⟩
  iunfold apply.chainResAny at Hres
  icases Hres with ⟨%info', Hres⟩
  wp_auto
  wp_apply HRevI $$ %r %rq %id %log %T %rs %Pre %Q %Post %info' [Htt Hkv Hres Hrr]
    as %resp %err ⟨Hpost, Htt⟩
  · iframe Htt
    iunfold apply.revokePre
    iframe # Hrr
    isplitr
    · ipureintro; exact Hk
    isplitl
    · iapply apply.mPre_of_rest
      iframe
    ipureintro; exact Hwt (apply.pass_exists c rq log _ (apply.backendStep_exists_revoke rq log id Hk.1 Hk.2.1) Hpass)
  iapply HΦ
  iframe Htt HL
  ihave #Hrc : apply.reqClass (GF := GF) E.authMode info rq $$ []
  · simp only [apply.reqClass, Hk.2.1]; itrivial
  ihave #Hrl : apply.reqLeaseClass (GF := GF) E.authMode info (mvcc.leaseItemsOf (mvcc.stateAfter log)) rq $$ []
  · simp only [apply.reqLeaseClass, Hk.2.1]
    iexists id
    isplitr
    · ipureintro; exact Hk.1
    iapply Hlc; rfl
  iapply apply.auth_pass_kvPostFL_nil E E.authOn c p (.ok bi) info info' rq log _ Pre Post _ Hpass Hk.2.1
    $$ Happ Hpost Hinfo Hrc Hrl

end proof

end EtcdGrove
end Perennial
