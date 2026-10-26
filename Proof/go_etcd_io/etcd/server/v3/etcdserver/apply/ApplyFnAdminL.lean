/-
**`apply.Apply(lg, e, uberApply, w, shouldApplyV3)` on an admitted admin request with the admin
check at the latest state** (the auth plan's E3c, 2026-10-27; `notes/decisions.md`, "E3c of the
auth plan"). Lean-first (no Rocq counterpart).

A third triple of `apply.Apply` (`apply.go`), beside its spec and E2o's admin triple
(`ApplyFnAdmin.lean`): the same code, with the call to the uber-applier through its latest-state
admin triple (`uberApplier.Apply.adminSpecL`, `ApplyAdminL.lean`). With no alarm set, the base
applier's latest-state `Apply` (`applierAdmL`) and the latest-state resource lent by the authority
family: a rejected entry's admin check refused at the latest state, a dispatched one's passed.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.ApplyFnAdmin
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.ApplyAdminL

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

/-- **The `UberApplier` `ua` with its base applier's admin triples and latest-state `Apply`**
(persistent): `uberAuthSteps`' with the base applier's `applierAdmL` for the latest-state family
`L`. -/
def apply.uberAuthStepsL (ua : GoInterface) (E : apply.AEnv GF) (W : IProp GF)
    (Own : auth.AuthNames → List auth.AuthState → IProp GF) (L : List auth.AuthState → IProp GF) :
    IProp GF :=
  iprop(∃ (p : Loc) (opts : go_etcd_io.etcd.server.v3.etcdserver.apply.ApplierOptions),
    ⌜ua = interface.mkOk (go.GoType.PointerType uberApplier.ty) #p⌝ ∗ apply.uberIs E p opts ∗
    ∃ base : GoInterface, structFieldRef uberApplier go!"applyV3base" p ↦□ base ∗
      apply.applierAdmin E (apply.baseChain E.authOn) base W Own ∗
      apply.applierAdmL E (apply.baseChain E.authOn) base L)

instance apply.uberAuthStepsL_persistent (ua : GoInterface) (E : apply.AEnv GF) (W : IProp GF)
    (Own : auth.AuthNames → List auth.AuthState → IProp GF) (L : List auth.AuthState → IProp GF) :
    Persistent (apply.uberAuthStepsL ua E W Own L) := by
  unfold apply.uberAuthStepsL; infer_instance

variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **`apply.Apply(lg, e, ua, w, shouldApplyV3)` on an admitted admin request with no alarm set,
the admin check at the latest state** (see the file header): `Apply.adminSpec`'s triple with
`uberAuthStepsL`, the current chain the base one and the authority family lending `L`
(`hsplit`); its postcondition but for `applyAuthRes`, with a rejected entry's check refused at the
latest state and a dispatched one's passed. -/
abbrev apply.Apply.adminSpecL : Prop :=
  ∀ (lg e : Loc) (m : EntryModel) (ua w : GoInterface) (v3 : Bool) (E : apply.AEnv GF)
    (Pre Q Post : IProp GF) (x : apply.ApplyKV) (rq : apply.IRRModel) (id : w64) (RD : IProp GF)
    (K G : Option GName → w64 → IProp GF) (ot : Option GName) (W : IProp GF)
    (γa : auth.AuthNames) (hs : List auth.AuthState) (Own : auth.AuthNames → List auth.AuthState → IProp GF)
    (L : List auth.AuthState → IProp GF),
  (∀ h, Own γa h ⊢ L h ∗ (L h -∗ Own γa h)) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.uberAuthStepsL ua E W Own L ∗ waitOk w RD K G ∗ RD ∗ K ot id ∗ ⌜lg ≠ null⌝ ∗ entryAt e m ∗
      (if v3 then iprop(□ ({{ E.P ∗ Pre }} (App (Val E.f) (Val #())) {{ RET #(); Q }}) ∗
          (Q ={⊤}=∗ E.P ∗ Post))
       else iprop(True)) ∗ Pre ∗
      apply.applyKV E ua x ∗
      ⌜apply.irrDecode m.data = some rq ∧ apply.irrId rq = some id ∧ apply.adminKindOk rq ∧
        apply.dispatchOk E.authOn rq ∧ E.authMode = .on γa ∧ receiptBound GF ≤ 2 ^ 48⌝ ∗
      ⌜x.chain = apply.baseChain E.authOn⌝ ∗
      Own γa hs ∗ ⧗ 1 ∗ W }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.Apply))
      (Val #lg)) (Val #e)) (Val #ua)) (Val #w)) (Val #v3))
  {{ (ar : Loc) (id' : w64), RET (PairV #ar #id'); RD ∗
      (if v3 then iprop(Post ∨ Pre) else Pre) ∗ apply.resultErrOk ar ∗ apply.resTrace ar ∗
      ⌜id' = id⌝ ∗
      ∃ (x' : apply.ApplyKV) (out : apply.ApplyOut), apply.applyKV E ua x' ∗
        ⌜apply.applyStep rq v3 x x' out⌝ ∗
        ⌜(out = .rejected → apply.needAdminPermission rq = true ∧ apply.adminRejL E.authMode hs rq) ∧
          (∀ o s, out = .dispatched o s → apply.adminPassL E.authMode hs rq)⌝ ∗
        apply.applyResultIs rq v3 x.log ar out ∗
        (⌜out.waived = false⌝ ∨ G ot id) ∗ W ∗ apply.adminOut Own γa E.authMode hs rq v3 ar out }}

end defs

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

set_option hygiene false in
/-- The call `uberApply.Apply(wrapper, v3)` through its admin triple and the postcondition. -/
local macro "call_tail_adminL" : tactic => `(tactic| (
  wp_apply (hUA E p opts x «$r0_ptr» rq sk v3 Pre Q Post W γa hs Own L hsplit)
      $$ [Hown Hkv Hcs Ho Hrc HW] as %ar ⟨%x', %out, Hown, Hkv, HPP, %Hst, %Hlat, Htr, Hres, HW, Hdone⟩
  · iframe # Hown Hkv Hcs Ho Hrc HW
    isplitr
    · ipureintro; exact ⟨Hmode, Hadm, Hdk, Hrb⟩
    isplitr
    · ipureintro
      intro h
      rw [← hsk] at h
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
      cases ht : rq.txn with
      | none => exact absurd (Hlt.2 ht) h.2
      | some _ => rfl
    ipureintro; exact Hch
  ihave ⟨#Hok, Hres⟩ := apply.applyResultIs_resultErrOk rq v3 x.log ar out $$ Hres
  iapply HΦ
  iframe HRD
  isplitl [HPP]
  · iapply cPost_if; iexact HPP
  iframe Hok Htr
  isplitr
  · ipureintro; rfl
  iexists x', out
  iframe Hres HW Hdone
  isplitl [Hown Hkv]
  · iunfold apply.applyKV; iexists p; iframe Hown Hkv; ipureintro; rfl
  isplitr
  · ipureintro; exact Hst.1
  isplitr
  · ipureintro
    refine ⟨Hlat.1, fun o s h => ?_⟩
    rcases Hst.2 with h' | ⟨o', h'⟩
    · rw [h'] at h; cases h
    · exact Hlat.2 o' h'
  icases Hwv with (%Hsk | HG)
  · ileft; ipureintro
    rcases Hst.2 with h | ⟨o, h⟩ <;> subst h <;> simp [apply.ApplyOut.waived, Hsk]
  · iright; iexact HG))

theorem apply.Apply.wp_adminL
    (hMU : pbutil.MustUnmarshalMessage.spec (GF := GF) (hG := hG))
    (hZS : zap.Stringer.spec (GF := GF) (hG := hG))
    (hDbg : zap.Logger.Debug.spec (GF := GF) (hG := hG))
    (hNSE : apply.noSideEffect.spec (GF := GF) (hG := hG))
    (hUA : apply.uberApplier.Apply.adminSpecL (GF := GF) (hG := hG)) :
    apply.Apply.adminSpecL (GF := GF) (hG := hG) := by
  intro lg e m ua w v3 E Pre Q Post x rq id RD K G ot W γa hs Own L hsplit
  wp_start as ⟨#Hfor, #Hwok, HRD, HK, %Hlg, #He, Hhook, HPre, Hkv, %Hprem, %Hch, Ho, Hrc, HW⟩
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
  iunfold apply.uberAuthStepsL at Hfor
  icases Hfor with ⟨%p, %opts, %Hua, #Hu, %base, #Hbf, #Hsteps, #HstepsL⟩
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
      call_tail_adminL
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
      simp only [apply.applyResultIs, apply.adminOut]
      iframe HW Ho Hrc
      isplitl [Hown Hkv]
      · iunfold apply.applyKV; iexists p; iframe Hown Hkv; ipureintro; rfl
      isplitr
      · ipureintro; simp [apply.applyStep, hns]
      isplitr
      · ipureintro; exact ⟨fun h => (by cases h), fun _ _ h => (by cases h)⟩
      iright; iexact HG
  · -- a waiter: applied
    ihave Hwv : iprop(⌜sk = false⌝ ∨ G ot id) $$ []
    · ileft; ipureintro; rw [← hsk]; simp
    iclear Hneed
    wp_auto
    call_tail_adminL

end proof

end EtcdGrove
end Perennial
