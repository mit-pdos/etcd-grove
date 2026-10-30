/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/authkv/Work.lean` (`notes/authkv-main-plan.md`;
draft, 2026-10-29): **not proved** (a `sorry`, one of the skeleton's stubs). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.Work
public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.WorkCalls
public import Proof.go_etcd_io.etcd.client.v3.WatchCheck
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.keyOf
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.reqCtx
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.refused
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.checkKVs
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.checkTxnReads
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.Permitted
public import Spec.context.WithTimeoutBackgroundMd
public import Spec.go_etcd_io.etcd.client.v3.OpPut
public import Spec.go_etcd_io.etcd.client.v3.OpGet
public import Spec.go_etcd_io.etcd.client.v3.OpTxn
public import Spec.go_etcd_io.etcd.client.v3.Compare
public import Spec.go_etcd_io.etcd.client.v3.Value
public import Spec.go_etcd_io.etcd.client.v3.WithRange
public import Spec.go_etcd_io.etcd.client.v3.WithPrefix
public import Spec.go_etcd_io.etcd.client.v3.WithRev
public import Spec.go_etcd_io.etcd.client.v3.watcher__Watch
public import Spec.context.ErrAny
public import Spec.google_golang_org.grpc.metadata.AppendToOutgoingContext

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver client

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.authkv.Assumptions]

theorem Work.wp_proof
    (wp_keyOf : keyOf.spec (GF := GF) (hG := hG))
    (wp_reqCtx : reqCtx.spec (GF := GF) (hG := hG))
    (wp_refused : refused.spec (GF := GF) (hG := hG))
    (wp_checkKVs : checkKVs.spec (GF := GF) (hG := hG))
    (wp_checkTxnReads : checkTxnReads.spec (GF := GF) (hG := hG))
    (wp_Permitted : Permitted.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackgroundMd.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_Append : metadata.AppendToOutgoingContext.spec (GF := GF) (hG := hG))
    (wp_OpPut : OpPut.spec (GF := GF) (hG := hG)) (wp_OpGet : OpGet.spec (GF := GF) (hG := hG))
    (wp_OpTxn : OpTxn.spec (GF := GF) (hG := hG))
    (wp_Compare : Compare.spec (GF := GF) (hG := hG)) (wp_Value : Value.spec (GF := GF) (hG := hG))
    (wp_WithRange : WithRange.spec (GF := GF) (hG := hG))
    (wp_WithPrefix : WithPrefix.spec (GF := GF) (hG := hG))
    (wp_WithRev : WithRev.spec (GF := GF) (hG := hG))
    (wp_Watch : watcher.Watch.spec (GF := GF) (hG := hG)) :
    Work.spec (GF := GF) (hG := hG) := by
  intro CS EA FA RA CRE CEC cl who V s E ρ cid mid γa Lset n hwho hγa hV hAs
  obtain ⟨hVa, hVm, hVn, hVs, hVE, hVk⟩ := hV
  wp_start as ⟨#Hnc, #Hwf, #Htok, #Hkv, #Htls, #Hinv, #Hf, #Htag⟩
  ihave #Htok0 := Htok
  iunfold clientTokAt at Htok0
  icases Htok0 with ⟨%api, %conn, #Hkvf, #Hobj, #Hat, -, -⟩
  ihave #Pc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  imod mvcc.idxCert_nil (GF := GF) E.γ.idx with #HF0
  ihave #Hnil := optsAt_nil (GF := GF)
  ihave #Henv : akCallEnv cl api conn s E ρ cid mid γa Lset n who $$ []
  · unfold akCallEnv; iframe #
  wp_auto
  wp_apply wp_keyOf go!"a" who go!"0"
  (try wp_auto)
  wp_apply wp_keyOf go!"c" who go!"0"
  (try wp_auto)
  -- the puts
  wp_apply (wp_reqCtx who hAs) as %c %cancel ⟨#Hcancel, %ci, %cd, %c0, %Hc, #Hctx, #Hce, %Hout⟩
  subst Hc
  (try wp_auto)
  wp_apply (work_put cl api conn s E ρ cid mid γa Lset n who ci cd (keyOfK go!"a" who go!"0")
      go!"v0" hγa (reqCtx_out who _ c0 Hout.1 Hout.2)
      (opHistOk_put_a who go!"0" go!"v0" (by decide))) $$ [] as %resp %err %Herr
  · iframe #
  (try wp_auto)
  wp_apply Hcancel
  (try wp_auto)
  wp_apply wp_Permitted who (keyOfK go!"a" who go!"0")
  (try wp_auto)
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ who_ptr ↦ who ∗ err_ptr ↦ err)))
    $$ [who err]
  · by_cases hpa : permittedK who (keyOfK go!"a" who go!"0")
    · rw [decide_eq_true hpa]
      (try wp_auto)
      iframe
      ipureintro; rfl
    · rw [decide_eq_false hpa]
      (try wp_auto)
      have hne : err ≠ GoInterface.nil := fun h =>
        hpa (akOpGranted_put who _ go!"v0" (keyOfK_ne_nil _ _ _ (by decide)) (Herr h))
      wp_apply (wp_refused who _ err hne)
      (try wp_auto)
      iframe
      ipureintro; rfl
  iintro %v ⟨%hv, who, err⟩
  subst hv
  (try wp_auto)
  -- the put outside `[a, b)`: refused
  wp_apply (wp_reqCtx who hAs) as %c %cancel ⟨#Hcancel, %ci, %cd, %c0, %Hc, #Hctx, #Hce, %Hout⟩
  subst Hc
  (try wp_auto)
  wp_apply (work_put cl api conn s E ρ cid mid γa Lset n who ci cd (keyOfK go!"c" who go!"0")
      go!"v0" hγa (reqCtx_out who _ c0 Hout.1 Hout.2)
      (fun h => absurd (akOpGranted_put who _ go!"v0" (keyOfK_ne_nil _ _ _ (by decide)) h)
        (not_permitted_c who _))) $$ [] as %resp %err %Herr
  · iframe #
  (try wp_auto)
  wp_apply Hcancel
  (try wp_auto)
  wp_apply (wp_refused who _ err (fun h => absurd (akOpGranted_put who _ go!"v0"
    (keyOfK_ne_nil _ _ _ (by decide)) (Herr h)) (not_permitted_c who _)))
  (try wp_auto)
  -- the range `[a, b)`: `u`'s
  wp_apply (wp_reqCtx who hAs) as %c %cancel ⟨#Hcancel, %ci, %cd, %c0, %Hc, #Hctx, #Hce, %Hout⟩
  subst Hc
  (try wp_auto)
  wp_apply wp_WithRange hi as %f1 #Hf1
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %osl ⟨Hosl, -⟩
  ipersist Hosl
  ihave #Hopts := optsAt_one (GF := GF) _ f1 (withRangeM hi) $$ [Hosl Hf1]
  · iframe #
  (try wp_auto)
  wp_apply (work_get cl api conn s E ρ cid mid γa Lset n who ci cd lo _ [withRangeM hi] hγa
      (reqCtx_out who _ c0 Hout.1 Hout.2) get_ab_ok.1 get_ab_ok.2.1) $$ []
    as %resp %err Hres
  · iframe #
  (try wp_auto)
  wp_apply Hcancel
  (try wp_auto)
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ who_ptr ↦ who ∗ g_ptr ↦ resp ∗
      err_ptr ↦ err))) $$ [who g err Hres]
  · icases Hres with (%Hne | ⟨%Herr, %m, #Hm, %Hg⟩)
    · cases err with
      | nil => exact absurd rfl Hne
      | ok i =>
        (try wp_auto)
        iframe
        ipureintro; rfl
    · subst Herr
      have hu := read_ab_u who Hg.1
      subst hu
      (try wp_auto)
      iunfold rangeRespMsg at Hm
      icases Hm with ⟨%Hnn, %h, %sl, %ps, #Hh, #Hhf, #Hkvf, #Hsl, #Hkvs, #Hmore, #Hcount⟩
      (try wp_auto)
      wp_apply (wp_checkKVs go!"u" sl ps m.kvs
        (fun kv hk => permitted_of_inRange_ab _ (Hg.2 kv hk))) $$ []
      · iframe #
      (try wp_auto)
      iframe
      ipureintro; rfl
  iintro %v ⟨%hv, who, g, err⟩
  subst hv
  (try wp_auto)
  -- the prefix `c/`: refused
  wp_apply (wp_reqCtx who hAs) as %c %cancel ⟨#Hcancel, %ci, %cd, %c0, %Hc, #Hctx, #Hce, %Hout⟩
  subst Hc
  (try wp_auto)
  wp_apply wp_WithPrefix as %f1 #Hf1
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %osl ⟨Hosl, -⟩
  ipersist Hosl
  ihave #Hopts := optsAt_one (GF := GF) _ f1 (withPrefixM) $$ [Hosl Hf1]
  · iframe #
  (try wp_auto)
  wp_apply (work_get cl api conn s E ρ cid mid γa Lset n who ci cd go!"c/" _ [withPrefixM] hγa
      (reqCtx_out who _ c0 Hout.1 Hout.2) get_c_ok.1 get_c_ok.2.1) $$ []
    as %resp %err Hres
  · iframe #
  (try wp_auto)
  wp_apply Hcancel
  (try wp_auto)
  icases Hres with (%Hne | ⟨%Herr, %m, -, %Hg⟩)
  rotate_left
  · exfalso
    exact read_c_refused who (by first | exact Hg.1 | (rw [get_c_ok.2.2.1, get_c_ok.2.2.2] at Hg; exact Hg.1))
  wp_apply (wp_refused who _ err Hne)
  (try wp_auto)
  -- the range `[a, d)`: refused
  wp_apply (wp_reqCtx who hAs) as %c %cancel ⟨#Hcancel, %ci, %cd, %c0, %Hc, #Hctx, #Hce, %Hout⟩
  subst Hc
  (try wp_auto)
  wp_apply wp_WithRange go!"d" as %f1 #Hf1
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %osl ⟨Hosl, -⟩
  ipersist Hosl
  ihave #Hopts := optsAt_one (GF := GF) _ f1 (withRangeM go!"d") $$ [Hosl Hf1]
  · iframe #
  (try wp_auto)
  wp_apply (work_get cl api conn s E ρ cid mid γa Lset n who ci cd lo _ [withRangeM go!"d"] hγa
      (reqCtx_out who _ c0 Hout.1 Hout.2) get_past_ok.1 get_past_ok.2.1) $$ []
    as %resp %err Hres
  · iframe #
  (try wp_auto)
  wp_apply Hcancel
  (try wp_auto)
  icases Hres with (%Hne | ⟨%Herr, %m, -, %Hg⟩)
  rotate_left
  · exfalso
    exact read_past_refused who (by first | exact Hg.1 | (rw [get_past_ok.2.2.1, get_past_ok.2.2.2] at Hg; exact Hg.1))
  wp_apply (wp_refused who _ err Hne)
  (try wp_auto)
  -- T1: a put in `[a, b)` and a get of `[a, b)`: `u`'s
  wp_apply (wp_reqCtx who hAs) as %c %cancel ⟨#Hcancel, %ci, %cd, %c0, %Hc, #Hctx, #Hce, %Hout⟩
  subst Hc
  (try wp_auto)
  wp_apply wp_keyOf go!"a" who go!"t"
  (try wp_auto)
  wp_apply (wp_OpPut (keyOfK go!"a" who go!"t") go!"vt" slice.nil []) as %op1 #Hop1
  · iframe #
    ipureintro; exact not_putPanics _ _
  (try wp_auto)
  wp_apply wp_WithRange hi as %f1 #Hf1
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %osl ⟨Hosl, -⟩
  ipersist Hosl
  ihave #Hopts := optsAt_one (GF := GF) _ f1 (withRangeM hi) $$ [Hosl Hf1]
  · iframe #
  (try wp_auto)
  wp_apply (wp_OpGet lo _ [withRangeM hi]) as %op2 #Hop2
  · iframe #
    ipureintro; exact get_ab_ok.1.1
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %tsl ⟨Htsl, -⟩
  ipersist Htsl
  ihave #Hops := opsAt_two (GF := GF) _
      ([op1, zero_val go_etcd_io.etcd.client.v3.Op].set (sint.nat (W64 (0 + 1))) op2) op1 op2
      (opPutModel (keyOfK go!"a" who go!"t") go!"vt" []) (opGetModel lo [withRangeM hi]) rfl
    $$ [Htsl Hop1 Hop2]
  · iframe #
  (try wp_auto)
  wp_apply (client_Txn_on cl api conn _ ci cd) as %tv ⟨%tp, %Htv, Hobj, #Hkt⟩
  · iframe #
  subst Htv
  (try wp_auto)
  wp_apply (v3.txn.wp_Then tp _ ci cd TxnBuild.empty _ _
      [.put (keyOfK go!"a" who go!"t") go!"vt" (W64 0), .get (opGetModel lo [withRangeM hi])])
    $$ [Hobj] as Hobj
  · iframe #
    iframe Hobj
    ipureintro
    exact ⟨by simp [txnOpOf_put, txnOpOf_get_ab], rfl, rfl⟩
  ihave Hobj : txnObjAt (GF := GF) tp [go!"127.0.0.1:23916"] ci cd
      ⟨t1M (keyOfK go!"a" who go!"t") go!"vt", false, true, false⟩ $$ [Hobj]
  · iExactEq Hobj
    simp [TxnModel.empty, t1M]
  (try wp_auto)
  have hk1 : keyOfK go!"a" who go!"t" ≠ [] := keyOfK_ne_nil _ _ _ (by decide)
  obtain ⟨hp1, hin1, hsh1, hro1, hpl1⟩ := t1M_ok (keyOfK go!"a" who go!"t") go!"vt" hk1
  have hop1 : akOpGranted who (.txn (txnWireOf (t1M (keyOfK go!"a" who go!"t") go!"vt"))) →
      opHistOk (.txn (txnWireOf (t1M (keyOfK go!"a" who go!"t") go!"vt"))) := by
    intro h
    obtain ⟨rfl, hr⟩ := akOpGranted_txn_put who _ go!"vt" (W64 0) _ hk1
      (by simp [t1M, txnWireOf, opWire]) h
    exact opHistOk_txn_put_get _ _ _
      (by rw [show writerK (keyOfK go!"a" go!"u" go!"t") = go!"u" by decide]; exact ⟨rfl, hr⟩)
  wp_apply (work_commit cl api conn tp s E ρ cid mid γa Lset n who ci cd
      ⟨t1M (keyOfK go!"a" who go!"t") go!"vt", false, true, false⟩ hγa
      (reqCtx_out who _ c0 Hout.1 Hout.2) hp1 hin1 hsh1 hro1 hpl1 hop1)
    $$ [Hobj] as %resp %err ⟨%Herr, Hres⟩
  · iframe #
    iframe Hobj
  (try wp_auto)
  wp_apply Hcancel
  (try wp_auto)
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ who_ptr ↦ who ∗ t_ptr ↦ resp ∗
      err_ptr ↦ err))) $$ [who t err Hres]
  · cases err with
    | ok i =>
      (try wp_auto)
      iframe
      ipureintro; rfl
    | nil =>
      icases Hres with (%Hne | ⟨%m, #Hm, %Hf⟩)
      · exact absurd rfl Hne
      obtain ⟨rfl, -⟩ := akOpGranted_txn_put who _ go!"vt" (W64 0) _ hk1
        (by simp [t1M, txnWireOf, opWire]) (Herr rfl)
      (try wp_auto)
      iunfold txnRespMsg at Hm
      icases Hm with ⟨%Hnn, %h, %sl, %ps, #Hh, #Hhf, #Hsucc, #Hrs, #Hsl, #Hms⟩
      (try wp_auto)
      obtain ⟨r, s0, skip, hs, hr⟩ := Hf
      have hab := t1_reads (keyOfK go!"a" go!"u" go!"t") go!"vt" r s0 skip m hs hr
      wp_apply (wp_checkTxnReads go!"u" sl ps m.resps (fun x hx => by
        have := hab x hx
        cases x <;> simp only [respInAB, respReadsOk] at this ⊢
        exact fun kv hkv => permitted_of_inRange_ab _ (this kv hkv))) $$ []
      · iframe #
      (try wp_auto)
      iframe
      ipureintro; rfl
  iintro %v ⟨%hv, who, t, err⟩
  subst hv
  (try wp_auto)
  -- T2: a put in `[a, b)` and one outside it: refused
  wp_apply (wp_reqCtx who hAs) as %c %cancel ⟨#Hcancel, %ci, %cd, %c0, %Hc, #Hctx, #Hce, %Hout⟩
  subst Hc
  (try wp_auto)
  wp_apply wp_keyOf go!"a" who go!"t1"
  (try wp_auto)
  wp_apply (wp_OpPut (keyOfK go!"a" who go!"t1") go!"vt" slice.nil []) as %op1 #Hop1
  · iframe #
    ipureintro; exact not_putPanics _ _
  (try wp_auto)
  wp_apply wp_keyOf go!"c" who go!"t1"
  (try wp_auto)
  wp_apply (wp_OpPut (keyOfK go!"c" who go!"t1") go!"vt" slice.nil []) as %op2 #Hop2
  · iframe #
    ipureintro; exact not_putPanics _ _
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %tsl ⟨Htsl, -⟩
  ipersist Htsl
  ihave #Hops := opsAt_two (GF := GF) _
      ([op1, zero_val go_etcd_io.etcd.client.v3.Op].set (sint.nat (W64 (0 + 1))) op2) op1 op2
      (opPutModel (keyOfK go!"a" who go!"t1") go!"vt" [])
      (opPutModel (keyOfK go!"c" who go!"t1") go!"vt" []) rfl
    $$ [Htsl Hop1 Hop2]
  · iframe #
  (try wp_auto)
  wp_apply (client_Txn_on cl api conn _ ci cd) as %tv ⟨%tp, %Htv, Hobj, #Hkt⟩
  · iframe #
  subst Htv
  (try wp_auto)
  wp_apply (v3.txn.wp_Then tp _ ci cd TxnBuild.empty _ _
      [.put (keyOfK go!"a" who go!"t1") go!"vt" (W64 0),
        .put (keyOfK go!"c" who go!"t1") go!"vt" (W64 0)])
    $$ [Hobj] as Hobj
  · iframe #
    iframe Hobj
    ipureintro
    exact ⟨by simp [txnOpOf_put], rfl, rfl⟩
  ihave Hobj : txnObjAt (GF := GF) tp [go!"127.0.0.1:23916"] ci cd
      ⟨t2M (keyOfK go!"a" who go!"t1") (keyOfK go!"c" who go!"t1") go!"vt", false, true, false⟩
    $$ [Hobj]
  · iExactEq Hobj
    simp [TxnModel.empty, t2M]
  (try wp_auto)
  have hk2 : keyOfK go!"c" who go!"t1" ≠ [] := keyOfK_ne_nil _ _ _ (by decide)
  obtain ⟨hp2, hin2, hsh2, hro2, hpl2⟩ := t2M_ok (keyOfK go!"a" who go!"t1")
    (keyOfK go!"c" who go!"t1") go!"vt" (keyOfK_ne_nil _ _ _ (by decide)) hk2
  have hng2 : ¬ akOpGranted who (.txn (txnWireOf
      (t2M (keyOfK go!"a" who go!"t1") (keyOfK go!"c" who go!"t1") go!"vt"))) := fun h =>
    not_permitted_c who _ (akOpGranted_txn_put who _ go!"vt" (W64 0) _ hk2
      (by simp [t2M, txnWireOf, opWire]) h)
  wp_apply (work_commit cl api conn tp s E ρ cid mid γa Lset n who ci cd
      ⟨t2M (keyOfK go!"a" who go!"t1") (keyOfK go!"c" who go!"t1") go!"vt", false, true, false⟩
      hγa (reqCtx_out who _ c0 Hout.1 Hout.2) hp2 hin2 hsh2 hro2 hpl2 (fun h => absurd h hng2))
    $$ [Hobj] as %resp %err ⟨%Herr, -⟩
  · iframe #
    iframe Hobj
  (try wp_auto)
  wp_apply Hcancel
  (try wp_auto)
  wp_apply (wp_refused who _ err (fun h => hng2 (Herr h)))
  (try wp_auto)
  -- T3: `If(in0 = "none")`, a put in `[a, b)` in its then branch, one outside it in its else
  -- branch: refused
  wp_apply (wp_reqCtx who hAs) as %c %cancel ⟨#Hcancel, %ci, %cd, %c0, %Hc, #Hctx, #Hce, %Hout⟩
  subst Hc
  (try wp_auto)
  wp_apply wp_keyOf go!"c" who go!"t2"
  (try wp_auto)
  wp_apply (wp_OpPut (keyOfK go!"c" who go!"t2") go!"vt" slice.nil []) as %op2 #Hop2
  · iframe #
    ipureintro; exact not_putPanics _ _
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %esl ⟨Hesl, -⟩
  ipersist Hesl
  ihave #Heops := opsAt_one (GF := GF) _ op2 (opPutModel (keyOfK go!"c" who go!"t2") go!"vt" [])
    $$ [Hesl Hop2]
  · iframe #
  (try wp_auto)
  wp_apply wp_keyOf go!"a" who go!"t2"
  (try wp_auto)
  wp_apply (wp_OpPut (keyOfK go!"a" who go!"t2") go!"vt" slice.nil []) as %op1 #Hop1
  · iframe #
    ipureintro; exact not_putPanics _ _
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %tsl ⟨Htsl, -⟩
  ipersist Htsl
  ihave #Htops := opsAt_one (GF := GF) _ op1 (opPutModel (keyOfK go!"a" who go!"t2") go!"vt" [])
    $$ [Htsl Hop1]
  · iframe #
  (try wp_auto)
  wp_apply wp_Value (keyOfK go!"a" who go!"0") as %cv #Hcv
  (try wp_auto)
  wp_apply (wp_Compare cv _ go!"=" .eq _ (.str go!"none")) as %cc #Hcc
  · iframe #
    ipureintro
    exact ⟨by unfold cmpOpOf; simp, _, rfl, rfl⟩
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %csl ⟨Hcsl, -⟩
  ipersist Hcsl
  ihave #Hcmps := cmpsAt_one (GF := GF) _ cc _ $$ [Hcsl Hcc]
  · iframe #
  (try wp_auto)
  wp_apply (client_Txn_on cl api conn _ ci cd) as %tv ⟨%tp, %Htv, Hobj, #Hkt⟩
  · iframe #
  subst Htv
  (try wp_auto)
  wp_apply (v3.txn.wp_If tp _ ci cd TxnBuild.empty _ _) $$ [Hobj] as Hobj
  · iframe #
    iframe Hobj
    ipureintro; exact ⟨rfl, rfl, rfl⟩
  (try wp_auto)
  wp_apply (v3.txn.wp_Then tp _ ci cd _ _ _ [.put (keyOfK go!"a" who go!"t2") go!"vt" (W64 0)])
    $$ [Hobj] as Hobj
  · iframe #
    iframe Hobj
    ipureintro
    exact ⟨by simp [txnOpOf_put], rfl, rfl⟩
  (try wp_auto)
  wp_apply (v3.txn.wp_Else tp _ ci cd _ _ _ [.put (keyOfK go!"c" who go!"t2") go!"vt" (W64 0)])
    $$ [Hobj] as Hobj
  · iframe #
    iframe Hobj
    ipureintro
    exact ⟨by simp [txnOpOf_put], rfl⟩
  ihave Hobj : txnObjAt (GF := GF) tp [go!"127.0.0.1:23916"] ci cd
      ⟨t3M (compareM (cmpKeyM .value (keyOfK go!"a" who go!"0")) .eq (.str go!"none"))
        (keyOfK go!"a" who go!"t2") (keyOfK go!"c" who go!"t2") go!"vt", true, true, true⟩
    $$ [Hobj]
  · iExactEq Hobj
    simp [TxnModel.empty, t3M]
  (try wp_auto)
  have hk2 : keyOfK go!"c" who go!"t2" ≠ [] := keyOfK_ne_nil _ _ _ (by decide)
  obtain ⟨hp3, hin3, hsh3, hro3, hpl3⟩ := t3M_ok
    (compareM (cmpKeyM .value (keyOfK go!"a" who go!"0")) .eq (.str go!"none"))
    (keyOfK go!"a" who go!"t2") (keyOfK go!"c" who go!"t2") go!"vt"
    ⟨keyOfK_ne_nil _ _ _ (by decide), Or.inl rfl⟩ (by simp [compareM, cmpKeyM])
    (keyOfK_ne_nil _ _ _ (by decide)) hk2
  have hng3 : ¬ akOpGranted who (.txn (txnWireOf
      (t3M (compareM (cmpKeyM .value (keyOfK go!"a" who go!"0")) .eq (.str go!"none"))
        (keyOfK go!"a" who go!"t2") (keyOfK go!"c" who go!"t2") go!"vt"))) := fun h =>
    not_permitted_c who _ (akOpGranted_txn_put who _ go!"vt" (W64 0) _ hk2
      (by simp [t3M, txnWireOf, opWire]) h)
  wp_apply (work_commit cl api conn tp s E ρ cid mid γa Lset n who ci cd
      ⟨t3M (compareM (cmpKeyM .value (keyOfK go!"a" who go!"0")) .eq (.str go!"none"))
        (keyOfK go!"a" who go!"t2") (keyOfK go!"c" who go!"t2") go!"vt", true, true, true⟩
      hγa (reqCtx_out who _ c0 Hout.1 Hout.2) hp3 hin3 hsh3 hro3 hpl3 (fun h => absurd h hng3))
    $$ [Hobj] as %resp %err ⟨%Herr, -⟩
  · iframe #
    iframe Hobj
  (try wp_auto)
  wp_apply Hcancel
  (try wp_auto)
  wp_apply (wp_refused who _ err (fun h => hng3 (Herr h)))
  (try wp_auto)
  -- T4: a nested transaction putting outside `[a, b)`: refused
  wp_apply (wp_reqCtx who hAs) as %c %cancel ⟨#Hcancel, %ci, %cd, %c0, %Hc, #Hctx, #Hce, %Hout⟩
  subst Hc
  (try wp_auto)
  wp_apply wp_keyOf go!"c" who go!"t3"
  (try wp_auto)
  wp_apply (wp_OpPut (keyOfK go!"c" who go!"t3") go!"vt" slice.nil []) as %op1 #Hop1
  · iframe #
    ipureintro; exact not_putPanics _ _
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %nsl ⟨Hnsl, -⟩
  ipersist Hnsl
  ihave #Hnops := opsAt_one (GF := GF) _ op1 (opPutModel (keyOfK go!"c" who go!"t3") go!"vt" [])
    $$ [Hnsl Hop1]
  · iframe #
  (try wp_auto)
  ihave #Hcnil := cmpsAt_nil' (GF := GF)
  wp_apply (wp_OpTxn slice.nil [] _ slice.nil) as %top ⟨#Htop, #Htc, %Htsl⟩
  · iframe #
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  ipersist Hsl
  (try wp_auto)
  wp_apply (client_Txn_on cl api conn _ ci cd) as %tv ⟨%tp, %Htv, Hobj, #Hkt⟩
  · iframe #
  subst Htv
  (try wp_auto)
  wp_apply (then_commit_nested_refused cl api conn tp s E ρ cid mid γa Lset n who ci cd _ _ top
      hγa (reqCtx_out who _ c0 Hout.1 Hout.2)) $$ [Hobj] as HC
  · iframe #
    iframe Hobj
    ipureintro; exact Htsl
  (try wp_auto)
  wp_apply HC as %resp %err %Hne
  (try wp_auto)
  wp_apply Hcancel
  (try wp_auto)
  wp_apply (wp_refused who _ err Hne)
  (try wp_auto)
  -- the delete of `a/who/d`: `u`'s
  wp_apply (wp_reqCtx who hAs) as %c %cancel ⟨#Hcancel, %ci, %cd, %c0, %Hc, #Hctx, #Hce, %Hout⟩
  subst Hc
  (try wp_auto)
  wp_apply wp_keyOf go!"a" who go!"d"
  (try wp_auto)
  have hkd : keyOfK go!"a" who go!"d" ≠ [] := keyOfK_ne_nil _ _ _ (by decide)
  wp_apply (work_delete cl api conn s E ρ cid mid γa Lset n who ci cd (keyOfK go!"a" who go!"d")
      hkd hγa (reqCtx_out who _ c0 Hout.1 Hout.2) (fun h => by
        obtain ⟨rfl, hr⟩ := akOpGranted_delete who _ hkd h
        exact opHistOk_delete_point _
          (by rw [show writerK (keyOfK go!"a" go!"u" go!"d") = go!"u" by decide]; exact ⟨rfl, hr⟩)))
    $$ [] as %resp %err %Herr
  · iframe #
  (try wp_auto)
  wp_apply Hcancel
  (try wp_auto)
  wp_apply wp_keyOf go!"a" who go!"d"
  (try wp_auto)
  wp_apply wp_Permitted who (keyOfK go!"a" who go!"d")
  (try wp_auto)
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ who_ptr ↦ who ∗ err_ptr ↦ err)))
    $$ [who err]
  · by_cases hpd : permittedK who (keyOfK go!"a" who go!"d")
    · rw [decide_eq_true hpd]
      (try wp_auto)
      iframe
      ipureintro; rfl
    · rw [decide_eq_false hpd]
      (try wp_auto)
      wp_apply (wp_refused who _ err (fun h => hpd (akOpGranted_delete who _ hkd (Herr h))))
      (try wp_auto)
      iframe
      ipureintro; rfl
  iintro %v ⟨%hv, who, err⟩
  subst hv
  (try wp_auto)
  -- the delete of `c/who/d`: refused
  wp_apply (wp_reqCtx who hAs) as %c %cancel ⟨#Hcancel, %ci, %cd, %c0, %Hc, #Hctx, #Hce, %Hout⟩
  subst Hc
  (try wp_auto)
  wp_apply wp_keyOf go!"c" who go!"d"
  (try wp_auto)
  have hkc : keyOfK go!"c" who go!"d" ≠ [] := keyOfK_ne_nil _ _ _ (by decide)
  wp_apply (work_delete cl api conn s E ρ cid mid γa Lset n who ci cd (keyOfK go!"c" who go!"d")
      hkc hγa (reqCtx_out who _ c0 Hout.1 Hout.2)
      (fun h => absurd (akOpGranted_delete who _ hkc h) (not_permitted_c who _)))
    $$ [] as %resp %err %Herr
  · iframe #
  (try wp_auto)
  wp_apply Hcancel
  (try wp_auto)
  wp_apply (wp_refused who _ err
    (fun h => not_permitted_c who _ (akOpGranted_delete who _ hkc (Herr h))))
  (try wp_auto)
  done
