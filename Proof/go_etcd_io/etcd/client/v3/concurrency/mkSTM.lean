/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/mkSTM.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.mkSTM
public import Spec.go_etcd_io.etcd.client.v3.concurrency.readSet__cmps
public import Spec.go_etcd_io.etcd.client.v3.concurrency.readSet__first
public import Spec.go_etcd_io.etcd.client.v3.concurrency.writeSet__cmps
public import Spec.go_etcd_io.etcd.client.v3.concurrency.stm__Get
public import Spec.go_etcd_io.etcd.client.v3.concurrency.stm__Put
public import Spec.go_etcd_io.etcd.client.v3.concurrency.stm__Rev
public import Spec.go_etcd_io.etcd.client.v3.concurrency.stm__Del
public import Spec.go_etcd_io.etcd.client.v3.concurrency.stm__commit
public import Spec.go_etcd_io.etcd.client.v3.concurrency.stm__reset
public import Spec.go_etcd_io.etcd.client.v3.concurrency.stmSerializable__Get
public import Spec.go_etcd_io.etcd.client.v3.concurrency.stmSerializable__Rev
public import Spec.go_etcd_io.etcd.client.v3.concurrency.stmSerializable__commit
public import Spec.go_etcd_io.etcd.client.v3.WithSerializable
public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvSTMRun

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem mkSTM.wp_proof
    (hRC : readSet.cmps.spec (GF := GF) (hG := hG))
    (hRF : readSet.first.spec (GF := GF) (hG := hG))
    (hWC : writeSet.cmps.spec (GF := GF) (hG := hG))
    (hGet : stm.Get.spec (GF := GF) (hG := hG))
    (hPut : stm.Put.spec (GF := GF) (hG := hG))
    (hRev : stm.Rev.spec (GF := GF) (hG := hG))
    (hDel : stm.Del.spec (GF := GF) (hG := hG))
    (hCommit : stm.commit.spec (GF := GF) (hG := hG))
    (hReset : stm.reset.spec (GF := GF) (hG := hG))
    (hSGet : stmSerializable.Get.spec (GF := GF) (hG := hG))
    (hSRev : stmSerializable.Rev.spec (GF := GF) (hG := hG))
    (hSCommit : stmSerializable.commit.spec (GF := GF) (hG := hG))
    (hWS : EtcdGrove.WithSerializable.spec (GF := GF) (hG := hG)) :
    mkSTM.spec (GF := GF) (hG := hG) := by
  intro c pfx op ov ctx cs
  wp_start as ⟨#Hcl, #Hop, #Hctx, %Hov⟩
  ihave #Hop2 := Hop
  iStructNamed Hop2
  wp_auto
  wp_if_destruct
  · iapply wp_fupd
    wp_apply (wp_map_make1 (K := GoString) (V := Loc) go.string
      (go.GoType.PointerType go_etcd_io.etcd.client.v3.GetResponse.ty)) as %pm Hpm
    ipersist s
    iStructNamed «$r0»
    iStructNamed stm
    ipersist client
    ipersist ctx
    ipersist conflicts
    imodintro
    ihave #Hconf : stmConflictsAt (GF := GF) isoSS pfx (structFieldRef stmSerializable go!"stm" «$r0_ptr») $$ []
    · unfold stmConflictsAt
      iexists _
      isplit
      · iexact conflicts
      unfold conflictsSpec
      imodintro
      iintro %reads %writes
      wp_start_folded as ⟨Hr, Hw⟩
      unfold stmRsetOwn stmWsetOwn
      icases Hr with ⟨%rm, %rsMap, Hrf, Hrm, #Hrs⟩
      icases Hw with ⟨%wm, %wsMap, Hwf, Hwm, #Hws⟩
      wp_auto
      wp_method_call
      wp_call
      wp_auto
      wp_apply hRC rm (DFrac.own 1) pfx rsMap reads $$ [$Hpkg $Hrm $Hrs] as %sl1 ⟨Hrm, %ms1, Hsl1, Hcap1, %Hms1⟩
      wp_method_call
      wp_call
      wp_auto
      wp_apply hRF rm (DFrac.own 1) pfx rsMap reads $$ [$Hpkg $Hrm $Hrs] as %f ⟨Hrm, %Hf⟩
      wp_method_call
      wp_call
      wp_auto
      wp_apply hWC wm (DFrac.own 1) pfx wsMap writes (f + W64 1) $$ [$Hpkg $Hwm $Hws]
        as %sl2 ⟨Hwm, %ms2, Hsl2, %Hms2⟩
      wp_apply wp_cmps_append sl1 sl2 ms1 ms2 $$ [$Hsl1 $Hcap1 $Hsl2] as %sl #Hsl
      iapply HΦ
      iframe
      iframe #
      ipureintro
      exact .inl ⟨rfl, f, ms1, ms2, Hf, Hms1, Hms2, rfl⟩
    rw [Hif]
    have hser : isoSer isoSS = true := by decide
    iapply HΦ
    iexists «$r0_ptr»
    isplitr
    · ipureintro; simp only [stmIface, hser, ↓reduceIte]
    isplitr
    · iapply stmMethods_ser hPut hDel hReset hSGet hSRev hSCommit isoSS pfx _ hser
      iexact Hpkg
    rw [Hov.1]
    iapply stmStale_ser_init isoSS hser pfx «$r0_ptr» c ctx cs null null pm
    iframe
    iframe #
  wp_if_destruct
  · iapply wp_fupd
    wp_apply (wp_map_make1 (K := GoString) (V := Loc) go.string
      (go.GoType.PointerType go_etcd_io.etcd.client.v3.GetResponse.ty)) as %pm Hpm
    ipersist s
    iStructNamed «$r0»
    iStructNamed stm
    ipersist client
    ipersist ctx
    ipersist conflicts
    imodintro
    ihave #Hconf : stmConflictsAt (GF := GF) isoS pfx (structFieldRef stmSerializable go!"stm" «$r0_ptr») $$ []
    · unfold stmConflictsAt
      iexists _
      isplit
      · iexact conflicts
      unfold conflictsSpec
      imodintro
      iintro %reads %writes
      wp_start_folded as ⟨Hr, Hw⟩
      unfold stmRsetOwn stmWsetOwn
      icases Hr with ⟨%rm, %rsMap, Hrf, Hrm, #Hrs⟩
      wp_auto
      wp_method_call
      wp_call
      wp_auto
      wp_apply hRC rm (DFrac.own 1) pfx rsMap reads $$ [$Hpkg $Hrm $Hrs] as %sl1 ⟨Hrm, %ms1, #Hsl1, -, %Hms1⟩
      iapply HΦ
      iframe
      iframe #
      ipureintro
      exact .inr (.inl ⟨.inl rfl, Hms1⟩)
    rw [‹ov.iso' = W64 1›]
    have hser : isoSer isoS = true := by decide
    iapply HΦ
    iexists «$r0_ptr»
    isplitr
    · ipureintro; simp only [stmIface, hser, ↓reduceIte]
    isplitr
    · iapply stmMethods_ser hPut hDel hReset hSGet hSRev hSCommit isoS pfx _ hser
      iexact Hpkg
    rw [Hov.1]
    iapply stmStale_ser_init isoS hser pfx «$r0_ptr» c ctx cs null null pm
    iframe
    iframe #
  wp_if_destruct
  · ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
    · iPkgInit
    iapply wp_fupd
    wp_apply hWS $$ [$Hcv] as %f0 #Hf0
    wp_apply wp_slice_literal (l := [f0])
    isplitr
    · ipureintro; rfl
    iintro %slo ⟨Hslo, -⟩
    wp_auto
    ipersist Hslo
    ipersist s
    iStructNamed «$r0»
    ipersist client
    ipersist ctx
    ipersist conflicts
    imodintro
    ihave #Hopts : optsAt (GF := GF) _ [withSerializableM] $$ []
    · unfold optsAt
      iexists [f0]
      iframe Hslo
      isplitr
      · ipureintro; rfl
      imodintro
      iintro %i %f %g %Hf %Hg
      rcases i with _ | i
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hf Hg; subst Hf Hg; iexact Hf0
      · simp at Hf
    ihave #Hconf : stmConflictsAt (GF := GF) isoRR pfx «$r0_ptr» $$ []
    · unfold stmConflictsAt
      iexists _
      isplit
      · iexact conflicts
      unfold conflictsSpec
      imodintro
      iintro %reads %writes
      wp_start_folded as ⟨Hr, Hw⟩
      unfold stmRsetOwn stmWsetOwn
      icases Hr with ⟨%rm, %rsMap, Hrf, Hrm, #Hrs⟩
      wp_auto
      wp_method_call
      wp_call
      wp_auto
      wp_apply hRC rm (DFrac.own 1) pfx rsMap reads $$ [$Hpkg $Hrm $Hrs] as %sl1 ⟨Hrm, %ms1, #Hsl1, -, %Hms1⟩
      iapply HΦ
      iframe
      iframe #
      ipureintro
      exact .inr (.inl ⟨.inr rfl, Hms1⟩)
    rw [‹ov.iso' = W64 2›]
    have hser : isoSer isoRR = false := by decide
    iapply HΦ
    iexists «$r0_ptr»
    isplitr
    · ipureintro; simp only [stmIface, hser, Bool.false_eq_true, ↓reduceIte]
    isplitr
    · iapply stmMethods_stm hGet hPut hRev hDel hCommit hReset isoRR pfx _ hser
      iexact Hpkg
    rw [Hov.1]
    iapply stmStale_stm_init isoRR hser pfx «$r0_ptr» c ctx cs null null _
    iframe
    iframe #
  wp_if_destruct
  · ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
    · iPkgInit
    iapply wp_fupd
    wp_apply hWS $$ [$Hcv] as %f0 #Hf0
    wp_apply wp_slice_literal (l := [f0])
    isplitr
    · ipureintro; rfl
    iintro %slo ⟨Hslo, -⟩
    wp_auto
    ipersist Hslo
    iStructNamed «$r0»
    ipersist client
    ipersist ctx
    ipersist conflicts
    imodintro
    ihave #Hopts : optsAt (GF := GF) _ [withSerializableM] $$ []
    · unfold optsAt
      iexists [f0]
      iframe Hslo
      isplitr
      · ipureintro; rfl
      imodintro
      iintro %i %f %g %Hf %Hg
      rcases i with _ | i
      · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hf Hg; subst Hf Hg; iexact Hf0
      · simp at Hf
    ihave #Hconf : stmConflictsAt (GF := GF) isoRC pfx «$r0_ptr» $$ []
    · unfold stmConflictsAt
      iexists _
      isplit
      · iexact conflicts
      unfold conflictsSpec
      imodintro
      iintro %reads %writes
      wp_start_folded as ⟨Hr, Hw⟩
      wp_auto
      iapply HΦ
      iframe
      iexists []
      ihave #Hnil := cmpsAt_nil (GF := GF)
      iframe #
      ipureintro
      exact .inr (.inr ⟨rfl, rfl⟩)
    rw [‹ov.iso' = W64 3›]
    have hser : isoSer isoRC = false := by decide
    iapply HΦ
    iexists «$r0_ptr»
    isplitr
    · ipureintro; simp only [stmIface, hser, Bool.false_eq_true, ↓reduceIte]
    isplitr
    · iapply stmMethods_stm hGet hPut hRev hDel hCommit hReset isoRC pfx _ hser
      iexact Hpkg
    rw [Hov.1]
    iapply stmStale_stm_init isoRC hser pfx «$r0_ptr» c ctx cs null null _
    iframe
    iframe #
  exfalso
  rcases Hov.2 with h | h | h | h <;> contradiction

end proof

end concurrency
end EtcdGrove
end Perennial
