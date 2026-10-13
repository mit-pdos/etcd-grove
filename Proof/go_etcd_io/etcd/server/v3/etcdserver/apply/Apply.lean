/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.Apply
public import Spec.go_etcd_io.etcd.pkg.v3.pbutil.MustUnmarshalMessage
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
  wp_apply (hUA E p opts x «$r0_ptr» rq sk v3 Pre Q Post)
      $$ [Hown Hkv Hwt Hcs] as %ar ⟨%x', %out, Hown, Hkv, HPP, %Hst, Hres⟩
  · iframe # Hown Hkv Hwt Hcs
    ipureintro
    refine ⟨⟨Hrq, Hdk⟩, ?_⟩
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
  iframe Hok
  isplitr
  · ipureintro; rfl
  iexists x', out
  iframe Hres
  isplitl [Hown Hkv]
  · iunfold apply.applyKV; iexists p; iframe Hown Hkv; ipureintro; rfl
  isplitr
  · ipureintro; exact Hst.1
  icases Hwv with (%Hsk | HG)
  · ileft; ipureintro
    rcases Hst.2 with h | ⟨o, h⟩ <;> subst h <;> simp [apply.ApplyOut.waived, Hsk]
  · iright; iexact HG))

theorem apply.Apply.wp_proof
    (hMU : pbutil.MustUnmarshalMessage.spec (GF := GF) (hG := hG))
    (hZS : zap.Stringer.spec (GF := GF) (hG := hG))
    (hDbg : zap.Logger.Debug.spec (GF := GF) (hG := hG))
    (hNSE : apply.noSideEffect.spec (GF := GF) (hG := hG))
    (hUA : apply.uberApplier.Apply.spec (GF := GF) (hG := hG)) :
    apply.Apply.spec (GF := GF) (hG := hG) := by
  intro lg e m ua w v3 E Pre Q Post x rq id RD K G ot
  wp_start as ⟨#Hfor, #Hwok, HRD, HK, %Hlg, #He, Hhook, HPre, Hkv, Hwt, %Hprem⟩
  obtain ⟨Hdec, Hid, Hrq, Hdk⟩ := Hprem
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.pbutil $$ []
  · iPkgInit
  ihave #He' := He
  iunfold entryAt at He'
  icases He' with ⟨%Hen, %pt, %pi, %pty, %d, -, -, -, -, -, -, #Hfd, #Hds⟩
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
      simp only [hhd, apply.optReqIs]
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
      iframe HRD
      isplitl [Hcs]
      · iapply cPost_if; iapply apply.cPost_of_pre; iapply apply.cPre_pre; iexact Hcs
      isplitr
      · iunfold apply.resultErrOk; ileft; ipureintro; rfl
      isplitr
      · ipureintro; rfl
      iexists x, .skipped
      simp only [apply.applyResultIs]
      isplitl [Hown Hkv]
      · iunfold apply.applyKV; iexists p; iframe Hown Hkv; ipureintro; rfl
      isplitr
      · ipureintro; simp [apply.applyStep, hns]
      isplitr
      · itrivial
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
