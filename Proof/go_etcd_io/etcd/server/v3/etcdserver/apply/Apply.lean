/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.Apply
public import Spec.google_golang_org.protobuf.proto.UnmarshalIRR
public import Spec.go_etcd_io.etcd.pkg.v3.pbutil.MustUnmarshal
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.requestV2__Unmarshal
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.requestV2__toInternalRaftRequest
public import Spec.go_uber_org.zap.Stringer
public import Spec.go_uber_org.zap.Logger__Debug
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.noSideEffect
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.uberApplier__Apply
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.UberLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Packaging

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- `if v3 then Post ∨ Pre else Pre` is `cPost v3 Pre Post`. -/
theorem cPost_if (v3 : Bool) (Pre Post : IProp GF) :
    apply.cPost v3 Pre Post ⊢ (if v3 then iprop(Post ∨ Pre) else Pre) := by
  cases v3 <;> simp only [apply.cPost, Bool.false_eq_true, ↓reduceIte] <;> iintro H <;> iexact H

set_option hygiene false in
/-- The call `uberApply.Apply(wrapper, v3)` and the postcondition. -/
local macro "call_tail" : tactic => `(tactic| (
  wp_apply (hUA E p opts x «$r0_ptr» rq sk v3 F Pre Q Post rs)
      $$ [Hown Hkv Hwt Hcs HFS HSp HRO] as %ar ⟨HFS, %x', %out, Hown, Hkv, HPP, HRO, %Hst, Htr, Hres, #Hauth⟩
  · iframe # Hown Hkv Hwt Hcs HFS HSp HRO
    ipureintro
    refine ⟨⟨Hrq, Hdk⟩, fun h => ?_⟩
    rw [← hsk] at h
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
    cases ht : rq.txn with
    | none => exact absurd (Hlt.2 ht) h.2
    | some _ => rfl
  ihave ⟨#Hok, Hres⟩ := apply.applyResultIs_resultErrOk rq v3 x.log ar out $$ Hres
  iapply HΦ
  iframe HRD HFS
  isplitl [HPP]
  · iapply cPost_if; iexact HPP
  iframe Hok Htr
  isplitr
  · ipureintro; rfl
  iexists x', out
  iframe Hres HRO Hauth
  isplitl [Hown Hkv]
  · iunfold apply.applyKV; iexists p; iframe Hown Hkv; ipureintro; rfl
  isplitr
  · ipureintro; exact ⟨Hst.1, Hst.2.2⟩
  icases Hwv with (%Hsk | HG)
  · ileft; ipureintro
    rcases Hst.2.1 with h | ⟨o, h⟩ <;> subst h <;> simp [apply.ApplyOut.waived, Hsk]
  · iright; iexact HG))

theorem apply.Apply.wp_proof
    (hProto : proto.UnmarshalIRR.spec (GF := GF) (hG := hG))
    (hMU : pbutil.MustUnmarshal.spec (GF := GF) (hG := hG))
    (hV2U : apply.requestV2.Unmarshal.spec (GF := GF) (hG := hG))
    (hV2To : apply.requestV2.toInternalRaftRequest.spec (GF := GF) (hG := hG))
    (hZS : zap.Stringer.spec (GF := GF) (hG := hG))
    (hDbg : zap.Logger.Debug.spec (GF := GF) (hG := hG))
    (hNSE : apply.noSideEffect.spec (GF := GF) (hG := hG))
    (hUA : apply.uberApplier.Apply.spec (GF := GF) (hG := hG)) :
    apply.Apply.spec (GF := GF) (hG := hG) := by
  intro lg e m ua w v3 E Pre Q Post x rq id RD K G ot F rs
  wp_start as ⟨#Hfor, #Hwok, HRD, HK, %Hlg, #He, Hhook, HPre, Hkv, Hwt, #Hcp, %Hprem, #HF, HFS, HSp, HRO⟩
  obtain ⟨Hdec, Hid, Hrq, Hdk⟩ := Hprem
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.pbutil $$ []
  · iPkgInit
  ihave #Pproto : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto $$ []
  · iPkgInit
  ihave ⟨%Hen, %d, #Hfd, #Hds⟩ := entryAt_fields _ _ $$ He
  wp_auto
  wp_apply (hProto d m.data DfracDiscarded raftReq_ptr _) $$ [raftReq] as %err ⟨-, Hproto⟩
  · iframe raftReq Hds
  wp_join (Q := fun v => iprop(⌜v = executeVal⌝ ∗ e_ptr ↦ e ∗ lg_ptr ↦ lg ∗
      apply.internalRaftRequestIs raftReq_ptr rq))
    at (if: _ then _ else _) with [Hproto e lg]
  · unfold apply.entryDecode at Hdec
    cases hIrr : apply.irrDecode m.data with
    | some rq' =>
      rw [hIrr] at Hdec
      injection Hdec with hRq
      subst hRq
      icases Hproto with ⟨%Herr, #Hirr⟩
      subst Herr
      wp_auto
      iframe e lg Hirr
      ipureintro; rfl
    | none =>
      rw [hIrr] at Hdec
      cases hV2 : apply.v2Decode m.data with
      | none => simp [hV2] at Hdec
      | some r =>
        rw [hV2] at Hdec
        simp only [Option.bind_some] at Hdec
        icases Hproto with ⟨%Herr, %v', raftReq⟩
        cases err with
        | nil => exact absurd rfl Herr
        | ok i1 =>
          wp_auto
          wp_apply (hMU (go.GoType.PointerType requestV2.ty) legacyReq_ptr d
            iprop(legacyReq_ptr ↦ (zeroValDef : requestV2)) iprop(legacyReq_ptr ↦ r)) $$ [legacyReq]
          · iframe # legacyReq
            iintro Hlr
            wp_apply (hV2U legacyReq_ptr _ d m.data DfracDiscarded) $$ [Hlr] as %err' ⟨-, Hlr⟩
            · iframe # Hlr
            rw [hV2]
            icases Hlr with ⟨%Herr', Hlr⟩
            subst Herr'
            iframe Hlr
            ipureintro; rfl
          iintro Hlr
          wp_auto
          iapply wp_fupd
          wp_apply (hV2To legacyReq_ptr r (DFrac.own 1) lg rq) $$ [Hlr] as %v ⟨Hlr, #Hval⟩
          · iframe Hlr
            ipureintro; exact ⟨Hlg, Hdec⟩
          imod (apply.internalRaftRequestIs_of_val raftReq_ptr v rq) $$ [raftReq Hval] with #Hirr
          · iframe # raftReq
          imodintro
          iframe e lg Hirr
          ipureintro; rfl
  rename_i v_if
  iintro ⟨%Hv_if, e, lg, #Hirr⟩
  subst Hv_if
  wp_auto
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
  iunfold apply.applierFor at Hfor
  icases Hfor with ⟨%p, %opts, %Hua, #Hu⟩
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
      call_tail
    · wp_auto
      iapply HΦ
      iframe HRD HFS
      isplitl [Hcs]
      · iapply cPost_if; iapply apply.cPost_of_pre; iapply apply.cPre_pre; iexact Hcs
      isplitr
      · iunfold apply.resultErrOk; ileft; ipureintro; rfl
      isplitr
      · iapply apply.resTrace_null
      isplitr
      · ipureintro; rfl
      iexists x, .skipped
      simp only [apply.applyResultIs, apply.restOut]
      iframe HRO
      isplitl [Hown Hkv]
      · iunfold apply.applyKV; iexists p; iframe Hown Hkv; ipureintro; rfl
      isplitr
      · ipureintro; simp [apply.applyStep, apply.applyFloorOk, hns]
      isplitr
      · itrivial
      isplitr
      · simp only [apply.applyAuthRes]; itrivial
      iright; iexact HG
  · -- a waiter: applied
    ihave Hwv : iprop(⌜sk = false⌝ ∨ G ot id) $$ []
    · ileft; ipureintro; rw [← hsk]; simp
    iclear Hneed
    wp_auto
    call_tail

end proof

end EtcdGrove
end Perennial
