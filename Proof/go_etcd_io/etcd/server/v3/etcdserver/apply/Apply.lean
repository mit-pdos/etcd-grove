/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.Apply
public import Spec.go_etcd_io.etcd.pkg.v3.pbutil.MustUnmarshalMessage
public import Spec.go_uber_org.zap.Stringer
public import Spec.go_uber_org.zap.Logger__Debug
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.noSideEffect
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- `if v3 then Post ∨ Pre else Pre` is `cPost v3 Pre Post`. -/
theorem cPost_if (v3 : Bool) (Pre Post : IProp GF) :
    apply.cPost v3 Pre Post ⊢ (if v3 then iprop(Post ∨ Pre) else Pre) := by
  cases v3 <;> simp only [apply.cPost, Bool.false_eq_true, ↓reduceIte] <;> iintro H <;> iexact H

theorem apply.Apply.wp_proof
    (hMU : pbutil.MustUnmarshalMessage.spec (GF := GF) (hG := hG))
    (hZS : zap.Stringer.spec (GF := GF) (hG := hG))
    (hDbg : zap.Logger.Debug.spec (GF := GF) (hG := hG))
    (hNSE : apply.noSideEffect.spec (GF := GF) (hG := hG)) :
    apply.Apply.spec (GF := GF) (hG := hG) := by
  intro lg e m ua w v3 rq id RD K G ot P Q
  wp_start as ⟨#Hwok, HRD, HK, %Hlg, #He, %Hprem, ⟨%ui, %Hui, #Htr⟩, HP⟩
  obtain ⟨Hdec, Hid⟩ := Hprem
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
  subst Hui
  generalize hsk : (!need && !decide (lt = null)) = sk
  have hskt : sk = true → rq.txn.isSome = true := by
    intro h
    rw [← hsk] at h
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
    cases ht : rq.txn with
    | none => exact absurd (Hlt.2 ht) h.2
    | some _ => rfl
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
      wp_apply Htr $$ %«$r0_ptr» %sk [HP] as %ar HQ
      · iframe Hwr HP; ipureintro; exact hskt
      iapply HΦ
      iframe HRD
      isplitr
      · ipureintro; rfl
      ileft
      iexists sk
      iframe HQ
      iright; iexact HG
    · wp_auto
      iapply HΦ
      iframe HRD
      isplitr
      · ipureintro; rfl
      iright
      iframe HG HP
      ipureintro; exact ⟨rfl, rfl⟩
  · -- a waiter: applied
    iclear Hneed
    wp_auto
    wp_apply Htr $$ %«$r0_ptr» %sk [HP] as %ar HQ
    · iframe Hwr HP; ipureintro; exact hskt
    iapply HΦ
    iframe HRD
    isplitr
    · ipureintro; rfl
    ileft
    iexists sk
    iframe HQ
    ileft; ipureintro; rw [← hsk]; simp

end proof

end EtcdGrove
end Perennial
