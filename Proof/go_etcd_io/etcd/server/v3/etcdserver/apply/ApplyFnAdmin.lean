/-
**`apply.Apply(lg, e, uberApply, w, shouldApplyV3)` on an admitted admin request in the mode
`on`** (the auth plan's E2o, 2026-10-26; `notes/decisions.md`, "E2o of the auth plan"). Lean-first
(no Rocq counterpart).

A second triple of `apply.Apply` (`apply.go`), beside its spec (`Spec/.../apply/Apply.lean`), for
the entries whose request the mode `on` admits by its shape (`adminKindOk`): the same code as
`Apply.wp_proof`'s (decode the entry, its ID, the waiter check, the wrapper), with the call to the
uber-applier through its admin triple (`uberApplier.Apply.adminSpec`, `ApplyAdmin.lean`). Without
a waiter and without side effects the request is skipped and nothing is spent (`adminOut`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Apply
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.ApplyAdmin

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

/-- **The `UberApplier` `ua` with its base applier's admin triples** (the auth plan's E2o;
persistent; E2v: the triples themselves, for the authority family `Own`, rather than the store's
`isAuthStepsX` they come from, `uberAuthSteps_of_stepsX`): `uberIs` and
the base applier's admin triples with the store's write resource `W`. -/
def apply.uberAuthSteps (ua : GoInterface) (E : apply.AEnv GF) (W : IProp GF) (Own : auth.AuthNames → List auth.AuthState → IProp GF) :
    IProp GF :=
  iprop(∃ (p : Loc) (opts : go_etcd_io.etcd.server.v3.etcdserver.apply.ApplierOptions),
    ⌜ua = interface.mkOk (go.GoType.PointerType uberApplier.ty) #p⌝ ∗ apply.uberIs E p opts ∗
    ∃ base : GoInterface, structFieldRef uberApplier go!"applyV3base" p ↦□ base ∗
      apply.applierAdmin E (apply.baseChain E.authOn) base W Own)

instance apply.uberAuthSteps_persistent (ua : GoInterface) (E : apply.AEnv GF) (W : IProp GF)
    (Own : auth.AuthNames → List auth.AuthState → IProp GF) : Persistent (apply.uberAuthSteps ua E W Own) := by
  unfold apply.uberAuthSteps; infer_instance

variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **`apply.Apply(lg, e, ua, w, shouldApplyV3)` on an admitted admin request in the mode
`on γa`** (see the file header): `Apply.spec`'s precondition but for the KV floor, the store's
write token, the rest buckets and the certificates, with `adminKindOk rq` in place of `rqOk`, the
uber-applier's admin step facts, the authority with its fuel, a time receipt and `W`;
`Apply.spec`'s postcondition but for the rest buckets, with `W` back and the admin outcome. -/
abbrev apply.Apply.adminSpec : Prop :=
  ∀ (lg e : Loc) (m : EntryModel) (ua w : GoInterface) (v3 : Bool) (E : apply.AEnv GF)
    (Pre Q Post : IProp GF) (x : apply.ApplyKV) (rq : apply.IRRModel) (id : w64) (RD : IProp GF)
    (K G : Option GName → w64 → IProp GF) (ot : Option GName) (W : IProp GF)
    (γa : auth.AuthNames) (hs : List auth.AuthState) (Own : auth.AuthNames → List auth.AuthState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.uberAuthSteps ua E W Own ∗ waitOk w RD K G ∗ RD ∗ K ot id ∗ ⌜lg ≠ null⌝ ∗ entryAt e m ∗
      (if v3 then iprop(□ ({{ E.P ∗ Pre }} (App (Val E.f) (Val #())) {{ RET #(); Q }}) ∗
          (Q ={⊤}=∗ E.P ∗ Post))
       else iprop(True)) ∗ Pre ∗
      apply.applyKV E ua x ∗
      ⌜apply.irrDecode m.data = some rq ∧ apply.irrId rq = some id ∧ apply.adminKindOk rq ∧
        apply.dispatchOk E.authOn rq ∧ E.authMode = .on γa ∧ receiptBound GF ≤ 2 ^ 48⌝ ∗
      Own γa hs ∗ ⧗ 1 ∗ W ∗ (if v3 then apply.adminExtra E γa rq hs Pre else iprop(True)) }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.Apply))
      (Val #lg)) (Val #e)) (Val #ua)) (Val #w)) (Val #v3))
  {{ (ar : Loc) (id' : w64), RET (PairV #ar #id'); RD ∗
      (if v3 then iprop(Post ∨ Pre) else Pre) ∗ apply.resultErrOk ar ∗ apply.resTrace ar ∗
      ⌜id' = id⌝ ∗
      ∃ (x' : apply.ApplyKV) (out : apply.ApplyOut), apply.applyKV E ua x' ∗
        ⌜apply.applyStep rq v3 x x' out⌝ ∗
        apply.applyResultIs rq v3 x.log ar out ∗ apply.applyAuthRes E.authMode x.chain rq v3 out ∗
        (⌜out.waived = false⌝ ∨ G ot id) ∗ W ∗ apply.adminOut Own γa E.authMode hs rq v3 ar out }}

end defs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **The uber-applier's admin triples carrying `X`** (the auth plan's E2v): from the store's
`isAuthStepsX` (of the real store with the tie, `isAuthStepsX_of_authInvT`) with the fuel triples
carrying `X`, for the authority with its fuel and `X`. -/
theorem apply.uberAuthSteps_of_stepsX
    (hUA : apply.applierV3backend.UserAdd.fuelSpecX (GF := GF) (hG := hG))
    (hRA : apply.applierV3backend.RoleAdd.fuelSpecX (GF := GF) (hG := hG))
    (hUGR : apply.applierV3backend.UserGrantRole.fuelSpecX (GF := GF) (hG := hG))
    (hRGP : apply.applierV3backend.RoleGrantPermission.fuelSpecX (GF := GF) (hG := hG))
    (hAE : apply.applierV3backend.AuthEnable.fuelSpecX (GF := GF) (hG := hG))
    (hAu : apply.applierV3backend.Authenticate.specX (GF := GF) (hG := hG))
    (E : apply.AEnv GF) (X : List auth.AuthState → IProp GF) (W : IProp GF) (p : Loc)
    (opts : go_etcd_io.etcd.server.v3.etcdserver.apply.ApplierOptions) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.uberIs E p opts ∗ apply.isAuthStepsX opts.AuthStore' E.P E.f E.authMode X W E.RD ⊢
      apply.uberAuthSteps (interface.mkOk (go.GoType.PointerType uberApplier.ty) #p) E W
        (fun γa h => iprop(auth.authOwnFu γa h ∗ X h)) := by
  iintro ⟨#Hpkg, #Hu, #Hst⟩
  iunfold apply.uberAuthSteps
  iexists p, opts
  iframe Hu
  isplitr
  · ipureintro; rfl
  iapply apply.applierAdmin_uberX hUA hRA hUGR hRGP hAE hAu E X W p opts $$ [Hpkg Hu Hst]
  iframe #

set_option hygiene false in
/-- The call `uberApply.Apply(wrapper, v3)` through its admin triple and the postcondition. -/
local macro "call_tail_admin" : tactic => `(tactic| (
  wp_apply (hUA E p opts x «$r0_ptr» rq sk v3 Pre Q Post W γa hs Own)
      $$ [Hown Hkv Hcs Ho Hrc HW Hx] as %ar ⟨%x', %out, Hown, Hkv, HPP, %Hst, Htr, Hres, #Hauth, HW, Hdone⟩
  · iframe # Hown Hkv Hcs Ho Hrc HW Hx
    isplitr
    · ipureintro; exact ⟨Hmode, Hadm, Hdk, Hrb⟩
    ipureintro
    intro h
    rw [← hsk] at h
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
    cases ht : rq.txn with
    | none => exact absurd (Hlt.2 ht) h.2
    | some _ => rfl
  ihave ⟨#Hok, Hres⟩ := apply.applyResultIs_resultErrOk rq v3 x.log ar out $$ Hres
  iapply HΦ
  iframe HRD
  isplitl [HPP]
  · iapply cPost_if; iexact HPP
  iframe Hok Htr
  isplitr
  · ipureintro; rfl
  iexists x', out
  iframe Hres Hauth HW Hdone
  isplitl [Hown Hkv]
  · iunfold apply.applyKV; iexists p; iframe Hown Hkv; ipureintro; rfl
  isplitr
  · ipureintro; exact Hst.1
  icases Hwv with (%Hsk | HG)
  · ileft; ipureintro
    rcases Hst.2 with h | ⟨o, h⟩ <;> subst h <;> simp [apply.ApplyOut.waived, Hsk]
  · iright; iexact HG))

theorem apply.Apply.wp_admin
    (hMU : pbutil.MustUnmarshalMessage.spec (GF := GF) (hG := hG))
    (hZS : zap.Stringer.spec (GF := GF) (hG := hG))
    (hDbg : zap.Logger.Debug.spec (GF := GF) (hG := hG))
    (hNSE : apply.noSideEffect.spec (GF := GF) (hG := hG))
    (hUA : apply.uberApplier.Apply.adminSpec (GF := GF) (hG := hG)) :
    apply.Apply.adminSpec (GF := GF) (hG := hG) := by
  intro lg e m ua w v3 E Pre Q Post x rq id RD K G ot W γa hs Own
  wp_start as ⟨#Hfor, #Hwok, HRD, HK, %Hlg, #He, Hhook, HPre, Hkv, %Hprem, Ho, Hrc, HW, Hx⟩
  obtain ⟨Hdec, Hid, Hadm, Hdk, Hmode, Hrb⟩ := Hprem
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.pbutil $$ []
  · iPkgInit
  ihave ⟨%Hen, %d, #Hfd, #Hds⟩ := entryAt_fields _ _ $$ He
  wp_auto
  wp_apply (hMU.2 raftReq_ptr _ d m.data DfracDiscarded rq) $$ [raftReq] as ⟨#Hirr, -⟩
  · iframe raftReq Hds
    ipureintro; exact Hdec
  wp_apply hZS as %f -
  wp_apply wp_slice_literal (l := [f])
  isplitr
  · ipureintro; rfl
  iintro %fsl -
  wp_auto
  wp_apply hDbg
  · ipureintro; exact Hlg
  ihave #Hirr' := Hirr
  iunfold apply.internalRaftRequestIs at Hirr'
  icases Hirr' with ⟨%Hpn, #HID, ⟨%lh, #FH, #Hh⟩, -, -, -, ⟨%lt, #FT, #Ht⟩, -⟩
  ihave #Ht := apply.optReqIs_txnW lt rq $$ Ht
  ihave %Hlt := apply.optReqIs_nil lt rq.txn _ apply.txnRequestIs_nn $$ Ht
  ihave %Hlh := apply.optReqIs_nil lh rq.header _ apply.headerIs_nn $$ Hh
  wp_auto
  wp_join iprop(id_ptr ↦ id) with [id] as id
  · -- `ID == 0`: the header's
    have Hid0 := Hid
    rw [apply.irrId_zero rq Hif] at Hid0
    wp_if_destruct
    · -- no header: `irrId rq = none`
      exfalso
      have hh : rq.header = none := Hlh.1 rfl
      simp [hh] at Hid0
    cases hhd : rq.header with
    | none => exact absurd (Hlh.2 hhd) Hif
    | some hm =>
      simp only [apply.optReqIs]
      iunfold apply.headerIs at Hh
      icases Hh with ⟨-, #HhID, -, -⟩
      wp_auto
      wp_join_done
      have : id = hm.id := by
        rw [hhd] at Hid0; exact (Option.some.inj Hid0).symm
      subst this
      iexact id
  · -- `ID != 0`: it
    have : id = rq.id := by
      rw [apply.irrId_nz rq Hif] at Hid; exact (Option.some.inj Hid).symm
    subst this
    iexact id
  iunfold waitOk at Hwok
  icases Hwok with ⟨%wi, %Hwi, #HIsReg⟩
  subst Hwi
  wp_apply HIsReg $$ [$HRD $HK] as %need ⟨HRD, Hneed⟩
  wp_join (Q := fun v => iprop(⌜v = #(!need && !decide (lt = null))⌝)) at (if: _ then _ else _)
  · cases need
    · wp_auto
      ipureintro; simp
    · wp_auto
      ipureintro; simp
  rename_i v
  iintro %Hv
  subst Hv
  wp_auto
  ihave ⟨Hw, %Hwn⟩ := typedPointsto_not_null_dup _ _ _ $$ «$r0»
  iStructNamed Hw
  ipersist InternalRaftRequest
  ipersist SkipRangeExecution
  ihave #Hwr : iprop(apply.irrWrapperIs «$r0_ptr» rq (!need && !decide (lt = null))) $$ []
  · iunfold apply.irrWrapperIs
    isplitr
    · ipureintro; exact Hwn
    iexists raftReq_ptr
    iframe #
  -- the uber-applier
  iunfold apply.uberAuthSteps at Hfor
  icases Hfor with ⟨%p, %opts, %Hua, #Hu, #Hsteps⟩
  iunfold apply.applyKV at Hkv
  icases Hkv with ⟨%p', %Hua', Hown, Hkv⟩
  subst Hua
  have := apply.mkOk_ptr_inj _ _ _ Hua'
  subst this
  ihave Hcs : iprop(apply.cPre v3 E.P E.f Pre Q Post) $$ [Hhook HPre]
  · cases v3
    · simp only [apply.cPre, Bool.false_eq_true, ↓reduceIte]
      iexact HPre
    · simp only [apply.cPre, ↓reduceIte, mvcc.csContract]
      icases Hhook with ⟨#Htr, Hup⟩
      iframe HPre Hup
      imodintro
      iexact Htr
  generalize hsk : (!need && !decide (lt = null)) = sk
  cases need
  · -- no waiter: applied only with side effects
    icases Hneed with (%Hf | HG)
    · cases Hf
    wp_auto
    wp_apply (hNSE raftReq_ptr rq) $$ [] as %b %Hb
    · iframe #
    subst Hb
    cases hns : apply.noSideEffect rq
    · wp_auto
      ihave Hwv : iprop(⌜sk = false⌝ ∨ G ot id) $$ [HG]
      · iright; iexact HG
      call_tail_admin
    · wp_auto
      iapply HΦ
      iframe HRD
      isplitl [Hcs]
      · iapply cPost_if; iapply apply.cPost_of_pre; iapply apply.cPre_pre; iexact Hcs
      isplitr
      · iunfold apply.resultErrOk; ileft; ipureintro; rfl
      isplitr
      · iapply apply.resTrace_null
      isplitr
      · ipureintro; rfl
      iexists x, .skipped
      simp only [apply.applyResultIs, apply.adminOut, apply.applyAuthRes]
      iframe HW Ho Hrc
      isplitl [Hown Hkv]
      · iunfold apply.applyKV; iexists p; iframe Hown Hkv; ipureintro; rfl
      isplitr
      · ipureintro; simp [apply.applyStep, hns]
      iright; iexact HG
  · -- a waiter: applied
    ihave Hwv : iprop(⌜sk = false⌝ ∨ G ot id) $$ []
    · ileft; ipureintro; rw [← hsk]; simp
    iclear Hneed
    wp_auto
    call_tail_admin


end proof

end EtcdGrove
end Perennial
