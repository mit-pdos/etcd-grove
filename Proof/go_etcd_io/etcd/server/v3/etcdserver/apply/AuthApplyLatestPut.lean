/-
**The auth applier's `Put` at the latest state** (the auth plan's E2s; see
`AuthApplyLatest.lean`): `checkPutAuth` with the lessor finding no lease (`lookupNil`), its checks'
verdicts at the latest state, and `Put`'s outcome decided there (`authOutL` over `putPerms`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthApplyLatest

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The auth applier's lessor finds no lease** (`lookupNil` of its `lessor` field). -/
def apply.lessorNil (p : Loc) : IProp GF :=
  iprop(∃ le : GoInterface, structFieldRef authApplierV3 go!"lessor" p ↦□ le ∗ apply.lookupNil le)

instance apply.lessorNil_persistent (p : Loc) : Persistent (apply.lessorNil (GF := GF) p) := by
  unfold apply.lessorNil; infer_instance

end defs

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- `checkLeasePuts` when the lessor finds no lease: `nil`. -/
abbrev apply.checkLeasePuts.specNil : Prop :=
  ∀ (st le : GoInterface) (ai : Loc) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.lookupNil le }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.checkLeasePuts))
      (Val #st)) (Val #ai)) (Val #le)) (Val #id))
  {{ RET #GoInterface.nil; True }}

/-- **`checkPutAuth` on the apply thread**: `checkPutAuth.spec`'s, with the lessor finding no lease,
the verdict of the put's permissions at the latest state (`passedL`/`refusedL` of `putPerms`). -/
abbrev apply.checkPutAuth.specL : Prop :=
  ∀ (st le : GoInterface) (RD : IProp GF) (on : auth.AuthMode) (L : List auth.AuthState → IProp GF)
    (hs : List auth.AuthState) (ai : Loc) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (dq : DFrac) (r : Loc) (o : OpFull),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.isAuthStoreL st RD on L ∗ apply.lookupNil le ∗ ai ↦{dq} info ∗ RD ∗ L hs ∗
      txn.putRequestIs r o ∗ ⌜apply.shapedL on hs (apply.putPerms o)⌝ }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.checkPutAuth))
      (Val #st)) (Val #ai)) (Val #le)) (Val #r))
  {{ (err : GoInterface), RET #err; ai ↦{dq} info ∗ RD ∗ L hs ∗ applyErrIs err ∗
      ⌜on.isOn = false → err = GoInterface.nil⌝ ∗
      (∀ _ : err = GoInterface.nil, apply.putClass on info o) ∗
      ⌜(err = GoInterface.nil → apply.passedL on hs (auth.authInfoM info) (apply.putPerms o)) ∧
        (err ≠ GoInterface.nil → apply.refusedL on hs (auth.authInfoM info) (apply.putPerms o))⌝ }}

/-- **`Put` on the apply thread**: `Put.spec`'s, the lessor finding no lease, the outcome decided
at the latest state for the put's permissions (`authOutL` over `putPerms`); the certificates asked
only of the outcomes that verdict admits (`putPreW`, E3f). -/
abbrev apply.authApplierV3.Put.specL : Prop :=
  ∀ (E : apply.AEnv GF) (c : apply.Chain) (inner : GoInterface) (p r : Loc) (rq : IRRModel)
    (o : OpFull) (log F : mvcc.Log) (Pre Q Post : IProp GF)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (L : List auth.AuthState → IProp GF) (hs : List auth.AuthState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.authIs E p inner ∗ apply.authIsL E p L ∗ apply.lessorNil p ∗ apply.applierSpec E c inner ∗
      apply.putPreW E (.auth E.authOn c) (interface.mkOk (go.GoType.PointerType authApplierV3.ty) #p) info r rq o log Pre Q Post
        (apply.authOutL E.authMode hs (auth.authInfoM info) c rq log (apply.putPerms o)) ∗
      mvcc.idxCert E.γ.idx F ∗ L hs ∗ ⌜apply.shapedL E.authMode hs (apply.putPerms o)⌝ }}
    (App (Val (p @!! go.GoType.PointerType authApplierV3.ty @!! go!"Put")) (Val #r))
  {{ (resp trace : Loc) (err : GoInterface), RET (PairV (PairV #resp #trace) #err);
      apply.kvPostFL E (.auth E.authOn c) (interface.mkOk (go.GoType.PointerType authApplierV3.ty) #p) info rq log F
        (apply.putAnswerIs log o resp err) Pre Post
        (apply.authOutL E.authMode hs (auth.authInfoM info) c rq log (apply.putPerms o)) ∗
      L hs ∗ apply.traceRes trace }}

end spec

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

theorem apply.checkLeasePuts.wp_nil : apply.checkLeasePuts.specNil (GF := GF) (hG := hG) := by
  intro st le ai id
  wp_start as #Hnil
  iunfold apply.lookupNil at Hnil
  icases Hnil with ⟨%li, %Hli, #HLookup⟩
  subst Hli
  wp_auto
  wp_apply HLookup as %l %Hl
  subst Hl
  wp_auto
  iapply HΦ
  itrivial

theorem apply.checkPutAuth.wp_latest
    (hLP : apply.checkLeasePuts.specNil (GF := GF) (hG := hG)) :
    apply.checkPutAuth.specL (GF := GF) (hG := hG) := by
  intro st le RD on L hs ai info dq r o
  wp_start as ⟨#Hst, #Hnil, Hai, Hrd, HLr, #Hr, %Hsh⟩
  ihave #Hst' := Hst
  iunfold apply.isAuthStoreL at Hst'
  icases Hst' with ⟨%sti, %Hsti, #HPut, #HRange, -⟩
  iunfold apply.permCheck2L at HPut
  iunfold apply.permCheck3L at HRange
  iunfold txn.putRequestIs at Hr
  icases Hr with ⟨%Hrn, %ksl, %vsl, %k, %v, %lease, %pk, %iv, %il, #HK, #Hk, -, -, #HL, #HPK, -, -, -, %Ho, %Hkb⟩
  subst Ho
  have Hsh' : apply.shapedL on hs ([(k, [], .write)] ++ if pk then [(k, [], .read)] else []) := by
    simpa [apply.putPerms, txn.putOpOf.proj_key, txn.putOpOf.proj_base] using Hsh
  have hshw : apply.shapedL on hs [(k, [], .write)] :=
    ((apply.shapedL_append on hs [(k, [], .write)] _).1 Hsh').1
  wp_auto
  rw [Hsti]
  wp_apply HPut $$ [$Hai $Hk $Hrd $HLr] as %err ⟨Hai, -, Hrd, HLr, #HeI1, %Hv1, #Hpv1⟩
  · ipureintro; exact Hkb
  have Hone1 := apply.verdictL_one _ _ _ _ _ _ _ Hv1 hshw
  have Hoff1 := apply.permVerdictL_isOn _ _ _ _ _ _ _ Hv1
  cases err with
  | ok e =>
    wp_auto
    iapply HΦ; iframe Hai Hrd HLr HeI1
    isplitl []
    · ipureintro; intro h; exact Hoff1 h
    isplitl []
    · iintro %h; cases h
    ipureintro
    refine ⟨(fun h => by cases h), fun _ => ?_⟩
    simp only [apply.putPerms, txn.putOpOf.proj_key, txn.putOpOf.proj_base]
    exact apply.refusedL_append_left _ _ _ [(k, [], .write)] (if pk then [(k, [], .read)] else [])
      (Hone1.2 (fun h => by cases h))
  | nil =>
  wp_auto
  rw [← Hsti]
  wp_apply (hLP st le ai lease) $$ [$Hnil]
  (try wp_auto)
  cases pk
  · wp_auto
    iapply HΦ; iframe Hai Hrd HLr
    isplitl []
    · iapply applyErrIs_nil
    isplitl []
    · ipureintro; intro _; rfl
    isplitl []
    · iintro %_
      simp only [apply.putClass, apply.putPerms, txn.putOpOf.proj_key, txn.putOpOf.proj_base, Bool.false_eq_true, ↓reduceIte]
      iapply (apply.classRes_of_permVerdict on info k [] .write) $$ Hpv1
    ipureintro
    refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
    simp only [apply.putPerms, txn.putOpOf.proj_key, txn.putOpOf.proj_base, Bool.false_eq_true, ↓reduceIte]
    exact Hone1.1 rfl
  wp_auto
  have hshr : apply.shapedL on hs [(k, [], .read)] := by
    simpa using ((apply.shapedL_append on hs [(k, [], .write)] _).1 Hsh').2
  ihave Hnil' := ownSlice_nil (V := w8) (GF := GF) (DFrac.own 1)
  rw [Hsti]
  wp_apply HRange $$ %ai %info %dq %ksl %slice.nil %k %([] : List w8) %DFrac.discard %(DFrac.own 1) %hs [Hai Hnil' Hrd HLr]
    as %err ⟨Hai, -, -, Hrd, HLr, #HeI3, %Hv3, #Hpv3⟩
  · iframe; iframe #; try (ipureintro; exact Hkb)
  have Hone3 := apply.verdictL_one _ _ _ _ _ _ _ Hv3 hshr
  have Hoff3 := apply.permVerdictL_isOn _ _ _ _ _ _ _ Hv3
  cases err with
  | ok e =>
    wp_auto
    iapply HΦ; iframe Hai Hrd HLr HeI3
    isplitl []
    · ipureintro; intro h; exact Hoff3 h
    isplitl []
    · iintro %h; cases h
    ipureintro
    refine ⟨(fun h => by cases h), fun _ => ?_⟩
    simp only [apply.putPerms, txn.putOpOf.proj_key, txn.putOpOf.proj_base, ↓reduceIte]
    exact apply.refusedL_append_right _ _ _ [(k, [], .write)] [(k, [], .read)]
      (Hone3.2 (fun h => by cases h))
  | nil =>
    wp_auto
    iapply HΦ; iframe Hai Hrd HLr
    isplitl []
    · iapply applyErrIs_nil
    isplitl []
    · ipureintro; intro _; rfl
    isplitl []
    · iintro %_
      simp only [apply.putClass, apply.putPerms, txn.putOpOf.proj_key, txn.putOpOf.proj_base, ↓reduceIte]
      iapply apply.classRes_cons
      isplitl []
      · iapply (apply.classRes_of_permVerdict on info k [] .write) $$ Hpv1
      · iapply (apply.classRes_of_permVerdict on info k [] .read) $$ Hpv3
    ipureintro
    refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
    simp only [apply.putPerms, txn.putOpOf.proj_key, txn.putOpOf.proj_base, ↓reduceIte]
    exact apply.passedL_append _ _ _ [(k, [], .write)] [(k, [], .read)] (Hone1.1 rfl) (Hone3.1 rfl)

theorem apply.authApplierV3.Put.wp_latest
    (hPut : apply.checkPutAuth.specL (GF := GF) (hG := hG)) :
    apply.authApplierV3.Put.specL (GF := GF) (hG := hG) := by
  intro E c inner p r rq o log F Pre Q Post info L hs
  wp_start as ⟨#Hauth, #HauthL, #Hlnil, #Hinner, Hpre, #HF, HL, %Hsh⟩
  iunfold apply.authIs at Hauth
  icases Hauth with ⟨#Happ, -, -, -⟩
  iunfold apply.authIsL at HauthL
  icases HauthL with ⟨%st, #Hasf, #Hst⟩
  iunfold apply.lessorNil at Hlnil
  icases Hlnil with ⟨%le, #Hlef, #Hnil⟩
  iunfold apply.putPreW at Hpre
  icases Hpre with ⟨%Hk, #Hcp, #Hr, Hwt, Hm⟩
  iunfold apply.mPre at Hm
  icases Hm with ⟨Hkv, Hres, Hcs⟩
  ihave ⟨Hard, Hkv⟩ := apply.kvOwn_rd E log $$ Hkv
  ihave ⟨Hinfo, Hres⟩ := apply.chainRes_auth_out c p inner info $$ Happ Hres
  ihave #Hin := Hinner
  iunfold apply.applierSpec at Hin
  icases Hin with ⟨%bi, %Hbi, #Ht⟩
  subst Hbi
  iunfold apply.applierTriples at Ht
  icases Ht with ⟨#HI, -⟩
  have hk : apply.authChecks (dispatchKind rq) = true := by rw [Hk.2.1]; rfl
  wp_auto
  wp_apply (hPut st le E.RD E.authMode L hs _ info (DFrac.own 1) r o)
    $$ [$Hst $Hnil $Hinfo $Hard $HL $Hr] as %err ⟨Hinfo, Hard, HL, #HeI, %Hoff, #Hcls, %Hvd⟩
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
    simp only [apply.putAnswerIs, apply.putOutcomeIs, apply.rejErrIs]
    isplitr
    · ipureintro; trivial
    · iframe HeI; ipureintro; simp
  | nil =>
  wp_auto
  ihave #Hcls := Hcls $$ %rfl
  ihave #Hrc := apply.reqClass_put E.authMode info rq o Hk.1 Hk.2.1 $$ Hcls
  ihave #Hcp := apply.certPreW_inner E E.authOn c rq log
    (apply.authOutL E.authMode hs (auth.authInfoM info) c rq log (apply.putPerms o))
    (fun oc hoc => Or.inr ⟨hoc, Hvd.1 rfl⟩) $$ Hcp
  iunfold apply.chainResAny at Hres
  icases Hres with ⟨%info', Hres⟩
  wp_apply HI $$ %r %rq %o %log %F %Pre %Q %Post %info' [Hwt Hkv Hres Hcs] as %resp %trace %err ⟨Hpost, Htrc⟩
  · iunfold apply.putPre
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
    (apply.authOutL E.authMode hs (auth.authInfoM info) c rq log (apply.putPerms o))
    (fun oc hoc => Or.inr ⟨hoc, Hvd.1 rfl⟩) $$ Happ Hpost Hinfo Hrc

end proof

end EtcdGrove
end Perennial
