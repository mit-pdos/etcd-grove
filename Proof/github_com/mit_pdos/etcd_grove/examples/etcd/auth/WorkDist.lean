/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/auth/WorkDist.lean` (`Work.spec_dist`, F7 stage S11):
`Work.wp_proof`'s text (`Work.lean`) at the cluster view, each call through `WorkCallsDist.lean`'s dist laws
(`work_putD`, `work_deleteD`, `work_getD`, `work_commitD`, over the auth-on contracts), `cli.Txn` through
`client_Txn_dist.law`, and the watch of `c/` through `WatchOn_dist`: its events' check `watchCheckedD` is refuted
at the frozen history (`akDistEnv_watch`). T4's commit through `then_commit_nested_refusedD` (over
`Txn_CommitOn_dist`'s write arm widened to nested transactions, F7 S11). Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.auth.WorkDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.WorkCallsDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.ClientCallDistLaws
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.WatchOnDist
public import Proof.go_etcd_io.etcd.client.v3.WatchCheck
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.auth.keyOf
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.auth.reqCtx
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.auth.refused
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.auth.checkKVs
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.auth.checkTxnReads
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.auth.Permitted
public import Spec.context.WithTimeoutBackgroundMd
public import Spec.go_etcd_io.etcd.client.v3.OpPut
public import Spec.go_etcd_io.etcd.client.v3.OpGet
public import Spec.go_etcd_io.etcd.client.v3.OpTxn
public import Spec.go_etcd_io.etcd.client.v3.Compare
public import Spec.go_etcd_io.etcd.client.v3.Value
public import Spec.go_etcd_io.etcd.client.v3.WithRange
public import Spec.go_etcd_io.etcd.client.v3.WithPrefix
public import Spec.go_etcd_io.etcd.client.v3.WithRev
public import Spec.context.ErrAny
public import Spec.google_golang_org.grpc.metadata.AppendToOutgoingContext
public import Proof.go_etcd_io.etcd.client.v3.TxnPlainSpec
public import Spec.go_etcd_io.etcd.client.v3.txn__If

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_auth

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net go_etcd_io.etcd.server.v3.etcdserver client
open etcd_dist etcd_dist.authd etcd_dist_client

section pure
variable [GooseExts]

/-- `Work`'s puts fit in a gRPC message (`akPut_sizeOk`). -/
theorem akPut_sizeOkD {x who n v : GoString} (hwho : who ∈ principals)
    (hx : x.length ≤ 2 ^ 10) (hn : n.length ≤ 2 ^ 10) (hv : v.length ≤ 2 ^ 28) :
    opSizeOk (opPutModel (keyOfK x who n) v []) :=
  opSizeOk_opPutModel (K := 2 ^ 20) (E := 0) (V := 2 ^ 28) (optsKeep_nil _ _ _)
    (keyOfK_principal_le hwho hx hn) hv (by decide)

/-- `Work`'s deletes fit in a gRPC message (`akDelete_sizeOk`). -/
theorem akDelete_sizeOkD {x who n : GoString} (hwho : who ∈ principals)
    (hx : x.length ≤ 2 ^ 10) (hn : n.length ≤ 2 ^ 10) :
    opSizeOk (opDeleteModel (keyOfK x who n) []) :=
  opSizeOk_opDeleteModel (K := 2 ^ 20) (E := 0) (V := 0) (optsKeep_nil _ _ _)
    (keyOfK_principal_le hwho hx hn) (by decide)

/-- `Work`'s ranges `[key, e)` of literal bounds fit in a gRPC message (`akRange_sizeOk`). -/
theorem akRange_sizeOkD {key e : GoString} (hk : key.length ≤ 2 ^ 28) (he : e.length ≤ 2 ^ 28) :
    opSizeOk (opGetModel key [withRangeM e]) :=
  opSizeOk_opGetModel (K := 2 ^ 28) (E := 2 ^ 28) (V := 0)
    (optsKeep_cons (withRangeM_keep he) (optsKeep_nil _ _ _)) hk (by decide)

/-- `Work`'s prefix ranges of a literal prefix fit in a gRPC message (`akPrefix_sizeOk`). -/
theorem akPrefix_sizeOkD {key : GoString} (hk : key.length ≤ 2 ^ 28) :
    opSizeOk (opGetModel key [withPrefixM]) :=
  opSizeOk_opGetModel (K := 2 ^ 28) (E := 2 ^ 28) (V := 0)
    (optsKeep_cons (withPrefixM_keep (by decide) (Nat.le_refl _)) (optsKeep_nil _ _ _)) hk
    (by decide)

/-- `Work`'s ranges are linearizable (`KV_GetOn_dist`'s premise). -/
theorem akSer_rangeD (key e : GoString) :
    (rangeWireOf (opGetModel key [withRangeM e])).base.serializable = false := by
  first
  | rfl
  | simp [rangeWireOf, txn.rangeOpOf, opGetModel, opFold, OpFull.getInit, OpFull.newOp, OpModel.zero,
      withRangeM]

/-- `Work`'s prefix ranges are linearizable (`KV_GetOn_dist`'s premise). -/
theorem akSer_prefixD (key : GoString) :
    (rangeWireOf (opGetModel key [withPrefixM])).base.serializable = false := by
  first
  | rfl
  | (simp [rangeWireOf, txn.rangeOpOf, opGetModel, opFold, OpFull.getInit, OpFull.newOp, OpModel.zero,
      withPrefixM]; split <;> rfl)

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.auth.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [esrv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

set_option maxHeartbeats 3200000 in
/-- See the file header. -/
theorem Work.wp_proof_dist
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
    (wp_If : EtcdGrove.txn.If.spec (GF := GF) (hG := hG))
    (wp_Then : EtcdGrove.txn.Then.spec (GF := GF) (hG := hG))
    (wp_Else : EtcdGrove.txn.Else.spec (GF := GF) (hG := hG))
    (wp_Txn : etcd_txnlin.client_Txn_dist.law (GF := GF) (hG := hG))
    (wp_Put : KV_PutOn_dist.spec (GF := GF) (hG := hG))
    (wp_Delete : KV_DeleteOn_dist.spec (GF := GF) (hG := hG))
    (wp_Get : KV_GetOn_dist.spec (GF := GF) (hG := hG))
    (wp_Commit : Txn_CommitOn_dist.spec (GF := GF) (hG := hG))
    (wp_WatchOn : WatchOn_dist.spec (GF := GF) (hG := hG)) :
    Work.spec_dist (GF := GF) (hG := hG) := by
  intro CS EA FA RA π cl api w who a addrs V Γ cfg γR hwho ha hauth hau hP hAs
  wp_start as ⟨Hlt, #Huc, #Hwc, #Henv⟩
  ihave #Pc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave ⟨%γz, %hs, %Lset, %r, #HE⟩ := akCallEnvD_of cl api a addrs V Γ cfg γR who hauth hau hP $$ []
  · iframe #
  ihave #HE' := HE
  iunfold akCallEnvD at HE'
  icases HE' with ⟨-, -, -, #Hinv, -, -, -⟩
  ihave #Huc' := Huc
  iunfold etcd_dist.authd.userClientAt at Huc'
  icases Huc' with ⟨#Hkc, #Hcfg, %Hcfgtok⟩
  ihave #Hnil := optsAt_nil (GF := GF)
  wp_auto
  wp_apply wp_keyOf go!"a" who go!"0"
  (try wp_auto)
  wp_apply wp_keyOf go!"c" who go!"0"
  (try wp_auto)
  -- the puts
  wp_apply (wp_reqCtx who hAs) as %c %cancel ⟨#Hcancel, %ci, %cd, %Hc, #Hctx, #Hce, #Hout0⟩
  subst Hc
  ihave #Hout : metadata.outMD ci (akOut who) $$ []
  · unfold akOut; iexact Hout0
  (try wp_auto)
  wp_apply (work_putD wp_Put cl api a V Γ cfg γR who γz hs Lset r ci cd (keyOfK go!"a" who go!"0")
      go!"v0"
      (opHistOk_put_a who go!"0" go!"v0" (by decide))
      (akPut_sizeOkD hwho (by decide) (by decide) (by decide))) $$ [$Hlt] as %resp %err ⟨Hlt, %Herr⟩
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
  wp_apply (wp_reqCtx who hAs) as %c %cancel ⟨#Hcancel, %ci, %cd, %Hc, #Hctx, #Hce, #Hout0⟩
  subst Hc
  ihave #Hout : metadata.outMD ci (akOut who) $$ []
  · unfold akOut; iexact Hout0
  (try wp_auto)
  wp_apply (work_putD wp_Put cl api a V Γ cfg γR who γz hs Lset r ci cd (keyOfK go!"c" who go!"0")
      go!"v0"
      (fun h => absurd (akOpGranted_put who _ go!"v0" (keyOfK_ne_nil _ _ _ (by decide)) h)
        (not_permitted_c who _))
      (akPut_sizeOkD hwho (by decide) (by decide) (by decide))) $$ [$Hlt] as %resp %err ⟨Hlt, %Herr⟩
  · iframe #
  (try wp_auto)
  wp_apply Hcancel
  (try wp_auto)
  wp_apply (wp_refused who _ err (fun h => absurd (akOpGranted_put who _ go!"v0"
    (keyOfK_ne_nil _ _ _ (by decide)) (Herr h)) (not_permitted_c who _)))
  (try wp_auto)
  -- the range `[a, b)`: `u`'s
  wp_apply (wp_reqCtx who hAs) as %c %cancel ⟨#Hcancel, %ci, %cd, %Hc, #Hctx, #Hce, #Hout0⟩
  subst Hc
  ihave #Hout : metadata.outMD ci (akOut who) $$ []
  · unfold akOut; iexact Hout0
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
  wp_apply (work_getD wp_Get cl api a V Γ cfg γR who γz hs Lset r ci cd lo _ [withRangeM hi] get_ab_ok.1 get_ab_ok.2.1 (akSer_rangeD _ _)
      (akRange_sizeOkD (by decide) (by decide))) $$ [$Hlt]
    as %resp %err ⟨Hlt, Hres⟩
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
      have hu := read_ab_uD who Hg.1
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
  wp_apply (wp_reqCtx who hAs) as %c %cancel ⟨#Hcancel, %ci, %cd, %Hc, #Hctx, #Hce, #Hout0⟩
  subst Hc
  ihave #Hout : metadata.outMD ci (akOut who) $$ []
  · unfold akOut; iexact Hout0
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
  wp_apply (work_getD wp_Get cl api a V Γ cfg γR who γz hs Lset r ci cd go!"c/" _ [withPrefixM] get_c_ok.1 get_c_ok.2.1 (akSer_prefixD _)
      (akPrefix_sizeOkD (by decide))) $$ [$Hlt]
    as %resp %err ⟨Hlt, Hres⟩
  · iframe #
  (try wp_auto)
  wp_apply Hcancel
  (try wp_auto)
  icases Hres with (%Hne | ⟨%Herr, %m, -, %Hg⟩)
  rotate_left
  · exfalso
    exact read_c_refusedD who Hg.1
  wp_apply (wp_refused who _ err Hne)
  (try wp_auto)
  -- the range `[a, d)`: refused
  wp_apply (wp_reqCtx who hAs) as %c %cancel ⟨#Hcancel, %ci, %cd, %Hc, #Hctx, #Hce, #Hout0⟩
  subst Hc
  ihave #Hout : metadata.outMD ci (akOut who) $$ []
  · unfold akOut; iexact Hout0
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
  wp_apply (work_getD wp_Get cl api a V Γ cfg γR who γz hs Lset r ci cd lo _ [withRangeM go!"d"] get_past_ok.1 get_past_ok.2.1 (akSer_rangeD _ _)
      (akRange_sizeOkD (by decide) (by decide))) $$ [$Hlt]
    as %resp %err ⟨Hlt, Hres⟩
  · iframe #
  (try wp_auto)
  wp_apply Hcancel
  (try wp_auto)
  icases Hres with (%Hne | ⟨%Herr, %m, -, %Hg⟩)
  rotate_left
  · exfalso
    exact read_past_refusedD who Hg.1
  wp_apply (wp_refused who _ err Hne)
  (try wp_auto)
  -- T1: a put in `[a, b)` and a get of `[a, b)`: `u`'s
  wp_apply (wp_reqCtx who hAs) as %c %cancel ⟨#Hcancel, %ci, %cd, %Hc, #Hctx, #Hce, #Hout0⟩
  subst Hc
  ihave #Hout : metadata.outMD ci (akOut who) $$ []
  · unfold akOut; iexact Hout0
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
  wp_apply (wp_Txn cl api [a] V Γ ci cd) $$ [$Hlt] as %tv ⟨Hlt, %tp, %Htv, Hobj, #Hkt⟩
  · iframe #
  subst Htv
  (try wp_auto)
  wp_apply ((EtcdGrove.txn.Then.spec_plain wp_Then) tp _ ci cd TxnBuild.empty _ _
      [.put (keyOfK go!"a" who go!"t") go!"vt" (W64 0), .get (opGetModel lo [withRangeM hi])])
    $$ [Hobj] as Hobj
  · iframe #
    iframe Hobj
    ipureintro
    exact ⟨by simp [txnOpOf_put, txnOpOf_get_ab], rfl, rfl⟩
  ihave Hobj : txnObjAt (GF := GF) tp [a] ci cd
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
  wp_apply (work_commitD wp_Commit cl api tp a V Γ cfg γR who γz hs Lset r ci cd
      ⟨t1M (keyOfK go!"a" who go!"t") go!"vt", false, true, false⟩ (by simp [TxnModel.plain, TxnOp.plain, t1M]) hin1
      (t1M_size _ _ (keyOfK_principal_le hwho (by decide) (by decide)) (by decide))
      hro1 hpl1 hop1)
    $$ [$Hlt Hobj] as %resp %err ⟨Hlt, %Herr, Hres⟩
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
  wp_apply (wp_reqCtx who hAs) as %c %cancel ⟨#Hcancel, %ci, %cd, %Hc, #Hctx, #Hce, #Hout0⟩
  subst Hc
  ihave #Hout : metadata.outMD ci (akOut who) $$ []
  · unfold akOut; iexact Hout0
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
  wp_apply (wp_Txn cl api [a] V Γ ci cd) $$ [$Hlt] as %tv ⟨Hlt, %tp, %Htv, Hobj, #Hkt⟩
  · iframe #
  subst Htv
  (try wp_auto)
  wp_apply ((EtcdGrove.txn.Then.spec_plain wp_Then) tp _ ci cd TxnBuild.empty _ _
      [.put (keyOfK go!"a" who go!"t1") go!"vt" (W64 0),
        .put (keyOfK go!"c" who go!"t1") go!"vt" (W64 0)])
    $$ [Hobj] as Hobj
  · iframe #
    iframe Hobj
    ipureintro
    exact ⟨by simp [txnOpOf_put], rfl, rfl⟩
  ihave Hobj : txnObjAt (GF := GF) tp [a] ci cd
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
  wp_apply (work_commitD wp_Commit cl api tp a V Γ cfg γR who γz hs Lset r ci cd
      ⟨t2M (keyOfK go!"a" who go!"t1") (keyOfK go!"c" who go!"t1") go!"vt", false, true, false⟩
      (by simp [TxnModel.plain, TxnOp.plain, t2M]) hin2
      (t2M_size _ _ _ (keyOfK_principal_le hwho (by decide) (by decide))
        (keyOfK_principal_le hwho (by decide) (by decide)) (by decide))
      hro2 hpl2 (fun h => absurd h hng2))
    $$ [$Hlt Hobj] as %resp %err ⟨Hlt, %Herr, -⟩
  · iframe #
    iframe Hobj
  (try wp_auto)
  wp_apply Hcancel
  (try wp_auto)
  wp_apply (wp_refused who _ err (fun h => hng2 (Herr h)))
  (try wp_auto)
  -- T3: `If(in0 = "none")`, a put in `[a, b)` in its then branch, one outside it in its else
  -- branch: refused
  wp_apply (wp_reqCtx who hAs) as %c %cancel ⟨#Hcancel, %ci, %cd, %Hc, #Hctx, #Hce, #Hout0⟩
  subst Hc
  ihave #Hout : metadata.outMD ci (akOut who) $$ []
  · unfold akOut; iexact Hout0
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
  wp_apply (wp_Txn cl api [a] V Γ ci cd) $$ [$Hlt] as %tv ⟨Hlt, %tp, %Htv, Hobj, #Hkt⟩
  · iframe #
  subst Htv
  (try wp_auto)
  wp_apply (wp_If tp _ ci cd TxnBuild.empty _ _) $$ [Hobj] as Hobj
  · iframe #
    iframe Hobj
    ipureintro; exact ⟨rfl, rfl, rfl⟩
  (try wp_auto)
  wp_apply ((EtcdGrove.txn.Then.spec_plain wp_Then) tp _ ci cd _ _ _ [.put (keyOfK go!"a" who go!"t2") go!"vt" (W64 0)])
    $$ [Hobj] as Hobj
  · iframe #
    iframe Hobj
    ipureintro
    exact ⟨by simp [txnOpOf_put], rfl, rfl⟩
  (try wp_auto)
  wp_apply ((EtcdGrove.txn.Else.spec_plain wp_Else) tp _ ci cd _ _ _ [.put (keyOfK go!"c" who go!"t2") go!"vt" (W64 0)])
    $$ [Hobj] as Hobj
  · iframe #
    iframe Hobj
    ipureintro
    exact ⟨by simp [txnOpOf_put], rfl⟩
  ihave Hobj : txnObjAt (GF := GF) tp [a] ci cd
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
  wp_apply (work_commitD wp_Commit cl api tp a V Γ cfg γR who γz hs Lset r ci cd
      ⟨t3M (compareM (cmpKeyM .value (keyOfK go!"a" who go!"0")) .eq (.str go!"none"))
        (keyOfK go!"a" who go!"t2") (keyOfK go!"c" who go!"t2") go!"vt", true, true, true⟩
      (by simp [TxnModel.plain, TxnOp.plain, t3M]) hin3
      (t3M_size _ _ _ _ ⟨by simpa [compareM, cmpKeyM] using
          keyOfK_principal_le (x := go!"a") (n := go!"0") hwho (by decide) (by decide),
          by simp [compareM, cmpKeyM], by simp [compareM, cmpKeyM]⟩
        (keyOfK_principal_le hwho (by decide) (by decide))
        (keyOfK_principal_le hwho (by decide) (by decide)) (by decide))
      hro3 hpl3 (fun h => absurd h hng3))
    $$ [$Hlt Hobj] as %resp %err ⟨Hlt, %Herr, -⟩
  · iframe #
    iframe Hobj
  (try wp_auto)
  wp_apply Hcancel
  (try wp_auto)
  wp_apply (wp_refused who _ err (fun h => hng3 (Herr h)))
  (try wp_auto)
  -- T4: a nested transaction putting outside `[a, b)`: refused
  wp_apply (wp_reqCtx who hAs) as %c %cancel ⟨#Hcancel, %ci, %cd, %Hc, #Hctx, #Hce, #Hout0⟩
  subst Hc
  ihave #Hout : metadata.outMD ci (akOut who) $$ []
  · unfold akOut; iexact Hout0
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
  wp_apply (wp_Txn cl api [a] V Γ ci cd) $$ [$Hlt] as %tv ⟨Hlt, %tp, %Htv, Hobj, #Hkt⟩
  · iframe #
  subst Htv
  (try wp_auto)
  wp_apply (then_commit_nested_refusedD wp_Then wp_Commit cl api tp a V Γ cfg γR who γz hs Lset r ci cd _ _ top hwho) $$ [Hobj] as HC
  · iframe #
    iframe Hobj
    ipureintro; exact Htsl
  (try wp_auto)
  wp_apply HC $$ [$Hlt] as %resp %err Hlt %Hne
  (try wp_auto)
  wp_apply Hcancel
  (try wp_auto)
  wp_apply (wp_refused who _ err Hne)
  (try wp_auto)
  -- the delete of `a/who/d`: `u`'s
  wp_apply (wp_reqCtx who hAs) as %c %cancel ⟨#Hcancel, %ci, %cd, %Hc, #Hctx, #Hce, #Hout0⟩
  subst Hc
  ihave #Hout : metadata.outMD ci (akOut who) $$ []
  · unfold akOut; iexact Hout0
  (try wp_auto)
  wp_apply wp_keyOf go!"a" who go!"d"
  (try wp_auto)
  have hkd : keyOfK go!"a" who go!"d" ≠ [] := keyOfK_ne_nil _ _ _ (by decide)
  wp_apply (work_deleteD wp_Delete cl api a V Γ cfg γR who γz hs Lset r ci cd (keyOfK go!"a" who go!"d")
      (fun h => by
        obtain ⟨rfl, hr⟩ := akOpGranted_delete who _ hkd h
        exact opHistOk_delete_point _
          (by rw [show writerK (keyOfK go!"a" go!"u" go!"d") = go!"u" by decide]; exact ⟨rfl, hr⟩))
      (akDelete_sizeOkD hwho (by decide) (by decide)))
    $$ [$Hlt] as %resp %err ⟨Hlt, %Herr⟩
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
  wp_apply (wp_reqCtx who hAs) as %c %cancel ⟨#Hcancel, %ci, %cd, %Hc, #Hctx, #Hce, #Hout0⟩
  subst Hc
  ihave #Hout : metadata.outMD ci (akOut who) $$ []
  · unfold akOut; iexact Hout0
  (try wp_auto)
  wp_apply wp_keyOf go!"c" who go!"d"
  (try wp_auto)
  have hkc : keyOfK go!"c" who go!"d" ≠ [] := keyOfK_ne_nil _ _ _ (by decide)
  wp_apply (work_deleteD wp_Delete cl api a V Γ cfg γR who γz hs Lset r ci cd (keyOfK go!"c" who go!"d")
      
      (fun h => absurd (akOpGranted_delete who _ hkc h) (not_permitted_c who _))
      (akDelete_sizeOkD hwho (by decide) (by decide)))
    $$ [$Hlt] as %resp %err ⟨Hlt, %Herr⟩
  · iframe #
  (try wp_auto)
  wp_apply Hcancel
  (try wp_auto)
  wp_apply (wp_refused who _ err
    (fun h => not_permitted_c who _ (akOpGranted_delete who _ hkc (Herr h))))
  (try wp_auto)
  -- the watch of `c/` from revision 1: refused, it reports nothing
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  wp_apply context.wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bgMd hWT wp_ErrAny hAs _) $$ []
    as %wc %wcd %wcancel ⟨#Hwcancel, #HwOk, -, #Hwctx, #Hwnone, #Hwlib⟩
  ihave #HwC := ctxOk_outgoingC wc wcd $$ HwOk
  (try wp_auto)
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
      ∃ (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
        wctx_ptr ↦ GoInterface.ok ci ∗ context.isContext ci cd ∗ metadata.outgoingCtxOk ci ∗
        metadata.outgoingCtxOkC ci ∗ metadata.outMD ci (akOut who)))) $$ [wctx]
  · wp_if_destruct
    · ihave #Pmd : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.metadata $$ []
      · iPkgInit
      (try wp_auto)
      wp_apply wp_slice_literal (V := GoString) [go!"token", badToken]
      isplitr
      · ipureintro; rfl
      iintro %ksl ⟨Hksl, -⟩
      simp only [go.arrayLiteralSize, List.foldl, Int.reduceAdd,
        show max (max (2 : Int) 0) 0 = 2 from rfl]
      (try wp_auto)
      ihave #Hwout0 := context.outgoingCtxOk_of_libCtxOk wc $$ Hwlib
      wp_apply wp_Append wc wcd _ (DFrac.own 1) go!"token" badToken none
          (by unfold metadata.lowerKey; decide) $$ [Hksl]
        as %c' ⟨%ci, %vs, %Hc', #Hctx', #Hout', #HoutC', #Hmd, -⟩
      · iframe; iframe #
      subst Hc'
      (try wp_auto)
      iframe
      isplitr
      · ipureintro; rfl
      iexists { wcd with Values := vs }
      iframe Hctx' Hout' HoutC'
      unfold akOut
      rw [_root_.if_pos rfl]
      iexact Hmd
    · (try wp_auto)
      iframe
      iexists wcd
      iframe Hwctx HwC
      isplitl []
      · ihave #Hwout1 := context.outgoingCtxOk_of_libCtxOk wc $$ Hwlib
        iexact Hwout1
      unfold akOut
      simp only [Hif, ↓reduceIte]
      iexact Hwnone
  iintro %v ⟨%hv, %wci, %wcd', wctx, #Hwctx', #Hwoutc, #HwoutC, #Hwout⟩
  subst hv
  (try wp_auto)
  wp_apply wp_WithPrefix as %f1 #Hf1
  wp_apply wp_WithRev (W64 1) as %f2 #Hf2
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %wosl ⟨Hwosl, -⟩
  ipersist Hwosl
  ihave #Hwopts := optsAt_two (GF := GF) _
      ([f1, zero_val GoFunc].set (sint.nat (W64 (0 + 1))) f2) f1 f2 withPrefixM (withRevM (W64 1))
      rfl $$ [Hwosl Hf1 Hf2]
  · iframe #
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  ihave #Hwc' := Hwc
  iunfold etcd_dist.watchClientAt at Hwc'
  icases Hwc' with ⟨-, -, #Hwf, -⟩
  ihave ⟨%Lw, %hγR', #HLw, #Hfl, #Hrefute⟩ := akDistEnv_watch addrs Γ γR a ha (principalOf cfg)
    (akPrin_three hP) $$ Henv
  ihave #Hau := akHist_readAu Γ.kv $$ Hinv
  iunfold kvReadAu at Hau
  iunfold kvAu at Hau
  (try wp_auto)
  wp_apply (wp_WatchOn cl w [a] V Γ cfg γR Lw wci wcd' (akOut who) go!"c/" _ [withPrefixM, withRevM (W64 1)]
      (W64 1) (fun σ => iprop(⌜stateHistOk σ⌝)) hau hauth hγR' (outTokOkS_reqMd _ who (akPrin_bad hP)))
    $$ [] as %wch %γw ⟨#Hsp, Hcons, -⟩
  · iframe #
    isplitr
    · ipureintro; exact Hcfgtok
    isplitr
    · iapply EtcdGrove.context.watchCtx_of_isContext; isplitl [] <;> iassumption
    ipureintro; exact watch_c_okD
  (try wp_auto)
  ihave HI : (∃ (rs : List go_etcd_io.etcd.client.v3.WatchResponse)
      (v0 : go_etcd_io.etcd.client.v3.WatchResponse),
      "Hcons" ∷ spscConsumer γw.spsc rs ∗ "wresp" ∷ wresp_ptr ↦ v0 : IProp GF) $$ [Hcons wresp]
  · iexists [], _; iframe
  wp_for HI
  wp_apply (wp_spsc_receive (t := go_etcd_io.etcd.client.v3.WatchResponse.ty) γw.spsc wch _ _ rs)
    $$ [$Hsp $Hcons] as %v %ok Hv
  cases ok
  · -- the channel closed: the loop ends
    wp_auto
    wp_for_post
    wp_apply Hwcancel
    (try wp_auto)
    iapply HΦ; iframe Hlt; try itrivial
  simp only [↓reduceIte]
  icases Hv with ⟨Hel, Hcons⟩
  ihave Hel := watchStateElemP_elem _ _ _ _ _ _ _ $$ Hel
  iunfold watchStateElem at Hel
  icases Hel with ⟨%r, %σ, %c, %c', #Hresp, -, -, -, -, #Hau', -⟩
  iunfold respAt at Hresp
  icases Hresp with ⟨#Hevs, -, -⟩
  iunfold eventsAt at Hevs
  icases Hevs with ⟨%ls, #Hls, %Hlen, -⟩
  ihave %Hsll := ownSlice_len _ _ _ $$ Hls
  wp_auto
  by_cases he : r.events = []
  · -- no events: the loop goes on
    have h0 : ¬ (sint.Z (W64 0) < sint.Z v.Events'.len) := by
      rw [he] at Hlen
      have := Hsll.1; have := Hsll.2
      simp only [List.length_nil] at Hlen
      word
    rw [decide_eq_false h0]
    wp_auto
    wp_for_post
    iframe
    iexists _, _
    iframe
  · -- events: the watch was granted, which it was not (`akDistEnv_watch`)
    ihave #Hw := Hau' $$ %he
    ihave #Hw2 : watchCheckedD [a] Γ γR (principalOf cfg) Lw go!"c/" go!"c0" $$ [Hw]
    · iExactEq Hw
      first
      | rfl
      | rw [show prefixRangeEnd go!"c/" = go!"c0" by decide]
    ihave Hf := Hrefute $$ %(⊤ : CoPset) %(fun _ _ => CoPset.mem_full) Hw2
    imod Hf with HF
    iexfalso
    iexact HF

end proof

end etcd_auth
end EtcdGrove
end Perennial
