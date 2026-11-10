/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__createMergedSnapshotMessage.lean`.
Lean-first (no Rocq counterpart); D22 S-h, 2026-10-20.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__createMergedSnapshotMessage
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__KV
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.newSnapshotReaderCloser
public import Spec.google_golang_org.protobuf.proto.CloneConfState
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.snapshot__Size
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.NewMessage

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `proto.Clone` of a nil-or-read-only conf state: a fresh one holding the same, owned (nil for
nil). -/
theorem wp_clone_csOpt (hClone : proto.CloneConfState.spec (GF := GF) (hG := hG)) (cs : Loc)
    (c : ConfStateM) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗
        csOpt cs DFrac.discard c }}
      (App (Val (@! google_golang_org.protobuf.proto.Clone))
        (Val #(interface.mkOk (go.GoType.PointerType go_etcd_io.raft.v3.raftpb.ConfState.ty) #cs)))
    {{ (p' : Loc), RET #(interface.mkOk (go.GoType.PointerType go_etcd_io.raft.v3.raftpb.ConfState.ty) #p');
        csOpt p' (DFrac.own 1) c }} := by
  iintro %Φ ⟨#Hpkg, #Hc⟩ HΦ
  iunfold csOpt at Hc
  icases Hc with (⟨%Hn, %Hce⟩ | #Hc)
  · subst Hn Hce
    wp_apply hClone.2
    iapply HΦ
    iunfold csOpt
    ileft; ipureintro; exact ⟨rfl, rfl⟩
  · wp_apply hClone.1 cs DFrac.discard c $$ [] as %p' ⟨-, Hp'⟩
    · iframe #
    iapply HΦ
    iunfold csOpt
    iright; iexact Hp'

theorem EtcdServer.createMergedSnapshotMessage.wp_proof
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hKV : EtcdServer.KV.spec (GF := GF) (hG := hG))
    (hNSR : newSnapshotReaderCloser.spec (GF := GF) (hG := hG))
    (hClone : proto.CloneConfState.spec (GF := GF) (hG := hG))
    (hSize : backend.snapshot.Size.spec (GF := GF) (hG := hG))
    (hNM : snap.NewMessage.spec (GF := GF) (hG := hG)) :
    EtcdServer.createMergedSnapshotMessage.spec (GF := GF) (hG := hG) := by
  intro s ml st snapt snapi cs lg kv be dq RC RC' RS RS' Qd γs Hsz20 Hsh
  wp_start as ⟨#Hlgf, %Hlgnn, Hlr, #Hkvf, Hkc, HRC, Hbef, Hbs, HRS, Hm, #Huf, #Hcs, Htok⟩
  (try wp_auto)
  wp_apply hLg s lg $$ [Hlr] as ⟨-, Hlr⟩
  · iframe #; iframe Hlr; ipureintro; exact Hlgnn
  (try wp_auto)
  wp_apply hKV s kv $$ []
  · iframe #
  iunfold srvKVCommitOk at Hkc
  icases Hkc with ⟨%ki, %Hki, #Hcommit⟩
  subst Hki
  (try wp_auto)
  -- `s.KV().Commit()`
  wp_bind (App (Val #(methods ki.ty go!"Commit" ki.v)) (Val #()))
  iapply Hcommit $$ HRC
  inext
  iintro HRC'
  -- (D22 the stored-index window, 2026-10-23) what `Snapshot()` takes, from what `Commit()` gave
  ihave HRS := HRS $$ HRC'
  (try wp_auto)
  -- `s.be.Snapshot()`
  iunfold srvBeSnapOk at Hbs
  icases Hbs with ⟨%bi, %Hbi, #Hsnap⟩
  subst Hbi
  (try wp_auto)
  wp_bind (App (Val #(methods bi.ty go!"Snapshot" bi.v)) (Val #()))
  iapply Hsnap $$ [HRS Htok]
  · iframe HRS Htok
  inext
  iintro %sp %D ⟨Hsn, HRS', HQ⟩
  iunfold backend.snapOpen at Hsn
  icases Hsn with ⟨%γd, Hsn⟩
  (try wp_auto)
  -- `newSnapshotReaderCloser(lg, dbsnap)`, with half of the snapshot (its `Size` read after)
  icases (backend.snapOpenQ_half sp D γd 1).1 $$ Hsn with ⟨Hsn1, Hsn2⟩
  wp_apply hNSR lg sp D γd $$ [Hsn1] as %rc ⟨Htok, Hrc⟩
  · iframe #; iframe Hsn1; ipureintro; exact Hlgnn
  (try wp_auto)
  ihave #Pproto : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto $$ []
  · iPkgInit
  -- `proto.Clone(confState)`: the clone holds `c`, owned (nil for nil)
  -- (raft-entsize [r3c]) the voters' conf state, of at most `2 ^ 20` ids
  iunfold epCsVoters at Hcs
  icases Hcs with ⟨%c, #Hc0, %Hci⟩
  ihave #Hc : csOpt cs DFrac.discard c $$ []
  · iunfold csOpt; iright; iexact Hc0
  have Hclen : (c.Voters' ++ c.Learners' ++ c.VotersOutgoing' ++ c.LearnersNext').length ≤ 2 ^ 20 := by
    obtain ⟨hv, hvo, hl, hln, -⟩ := Hci
    simp only [List.length_append, hv.length_eq, hvo.length_eq, hl.length_eq, hln.length_eq,
      GMap.length_elements, Membership.simple, GMap.size_empty]
    omega
  wp_apply wp_clone_csOpt hClone cs c $$ [] as %p' Hp'
  · iframe #
  (try wp_auto)
  -- the merged metadata and snapshot (`&snapi`, `&snapt` frozen: nothing writes them after)
  imod cellRO_alloc snapi_ptr snapi $$ snapi with #cI
  imod cellRO_alloc snapt_ptr snapt $$ snapt with #cT
  -- (raft-entsize [r3c]) at their contents: fresh literals, without unknown fields
  imod smPtsCC_of_struct «$v0_ptr»
    ({ state' := zeroValDef, ConfState' := p', Index' := snapi_ptr, Term' := snapt_ptr,
       unknownFields' := slice.nil, sizeCache' := 0 } : go_etcd_io.raft.v3.raftpb.SnapshotMetadata)
    (SnapshotMetadataM.mk c snapi snapt) ⊤ rfl
    $$ [«$v0» Hp'] with ⟨%md, Hmd, %Hmd⟩
  · iframe «$v0» Hp' cI cT
  imod ownSnapCC_of_struct «$r0_ptr»
    ({ state' := zeroValDef, Data' := slice.nil, Metadata' := «$v0_ptr», unknownFields' := slice.nil,
       sizeCache' := 0 } : go_etcd_io.raft.v3.raftpb.Snapshot) md ⊤ rfl rfl
    $$ [«$r0» Hmd] with Hsnp
  · iframe «$r0» Hmd
  -- `m.Snapshot = snapshot`, at the raft message's content (no top-level unknown fields), the
  -- message then frozen
  icases msgPtsC_msgPtsCC_uf ml (DFrac.own 1) DFrac.discard false st [] $$ [Hm Huf]
    with ⟨%c0, HmC, %Hc0⟩
  · iframe Hm Huf
  icases msgPtsCC_store_Snapshot ml DFrac.discard false c0 $$ HmC with ⟨%ps, HSn, Hback⟩
  (try wp_auto)
  ihave Hsnp : snapOptCC «$r0_ptr» (DFrac.own 1) (some ⟨none, some md, []⟩) $$ [Hsnp]
  · simp only [snapOptCC]; iexact Hsnp
  ihave HmC := Hback $$ %_ %(some ⟨none, some md, []⟩) HSn Hsnp
  imod msgPtsCC_persist ml _ _ $$ HmC with #HmC
  obtain ⟨Hmod0, -, Hu0⟩ := Hc0
  obtain ⟨Hse, Hsc, Hsr⟩ := Hsh
  have hr : c0.resps = [] := by
    have := congrArg MsgSt.resps Hmod0
    simp only [MsgC.model, Hsr, List.map_eq_nil_iff] at this; exact this
  have he : c0.f.entries = [] := by
    have := congrArg MsgSt.ents Hmod0
    simp only [MsgC.model, Hse, List.map_eq_nil_iff] at this; exact this
  have hctx : (c0.f.context.getD []).length = 0 := by
    have := congrArg MsgSt.ctx Hmod0
    simp only [MsgC.model, Hsc] at this; rw [this]; rfl
  have hcsb : ∀ cs ∈ md.confState, cs.uf = [] ∧
      (cs.voters ++ cs.learners ++ cs.votersOutgoing ++ cs.learnersNext).length ≤ 2 ^ 20 := by
    intro cs hcs
    refine ⟨Hmd.2.2 cs hcs, ?_⟩
    have h1 := congrArg SnapshotMetadataM.ConfState' Hmd.1
    rw [Option.mem_def] at hcs
    simp only [SnapMetaC.model, hcs, Option.map_some, Option.getD_some] at h1
    rw [← h1] at Hclen; simpa [CSC.model] using Hclen
  have hmodel : (MsgC.mk { c0.f with snapshot := some ⟨none, some md, []⟩ } c0.resps).model =
      mergedSt st c snapi snapt := by
    rw [← Hmod0]
    simp only [MsgC.model, MsgC.f, MsgC.resps, mergedSt, SnapC.model, Option.map_some,
      Option.getD_some, Option.getD_none, Hmd.1, MsgFC.msgM]
  have hcsu : (MsgC.mk { c0.f with snapshot := some ⟨none, some md, []⟩ } c0.resps).csUfNil := by
    intro sn hsn m hm cs hcs
    simp only [MsgC.f, Option.mem_def, Option.some.injEq] at hsn
    subst hsn
    simp only [Option.mem_def, Option.some.injEq] at hm
    subst hm
    exact Hmd.2.2 cs hcs
  have hok : msgSizeOk (MsgC.mk { c0.f with snapshot := some ⟨none, some md, []⟩ } c0.resps) := by
    rw [hr]; exact merged_sizeOk c0.f md he hctx Hu0 Hmd.2.1 hcsb
  ihave #HszC : msgSzC False ml (mergedSt st c snapi snapt) $$ []
  · iunfold msgSzC
    iexists _
    ihave #Hro := msgPtsCC_msgRoC ml _ (by simp only [MsgC.resps]; exact hr) $$ HmC
    iframe Hro
    ipureintro; exact ⟨hmodel, hcsu, msgSize_lt_of_ok _ hok, False.elim⟩
  ihave #Hm : msgOwn ml DFrac.discard (mergedSt st c snapi snapt) $$ []
  · rw [← hmodel]
    iapply msgPtsCC_msgPtsC ml DFrac.discard DFrac.discard false _ hcsu $$ HmC
  -- `dbsnap.Size()`, with the sender's half, which then goes to the reader (the pipe's hand-over)
  ihave #Pbe : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
  wp_apply hSize sp D γd _ $$ [Hsn2] as %n ⟨Hsn2, %Hsz⟩
  · iframe #; iframe Hsn2
  ihave ⟨Hrs, #Hrcc⟩ := Hrc $$ Hsn2
  -- `snap.NewMessage(m, rc, size)`, with the reader's close contract (sweep repairs 1, S1)
  wp_apply hNM ml (mergedSt st c snapi snapt) rc n $$ [] as %mg ⟨#Hmi, %tsz, %cc, %γc, #Htsz, #Hcc, #Hccb⟩
  · simp only [mergedSt]; iframe Hm Hrcc; ipureintro; exact Hsz
  (try wp_auto)
  iapply HΦ
  simp only [mergedSt]
  iframe Hlr HRS' Hbef Htok
  iexists rc, D, c
  iframe Hm HszC Hc Hrs HQ
  isplitl
  · iunfold mergedMsg
    iframe Hmi
    iexists tsz, cc, γc
    iframe Htsz Hcc Hccb
  ipureintro; exact Hclen

end proof

end EtcdGrove
end Perennial
