/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__createMergedSnapshotMessage.lean`.
Lean-first (no Rocq counterpart); D22 S-h, 2026-10-20.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__createMergedSnapshotMessage
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapshotCindex
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.replayTerms__covers
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.confStateFromMembers
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.replayTerms__termAt
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
    (hNM : snap.NewMessage.spec (GF := GF) (hG := hG))
    (hRead : schema.UnsafeReadConsistentIndex.spec (GF := GF) (hG := hG))
    (hUR : backend.snapshot.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (hCovers : replayTerms.covers.spec (GF := GF) (hG := hG))
    (hTermAt : replayTerms.termAt.spec (GF := GF) (hG := hG)) :
    EtcdServer.createMergedSnapshotMessage.spec (GF := GF) (hG := hG) := by
  intro s ml st snapt snapi ci backendTerm terms boot cs lg kv be dq RC RC' RS RS' Qd γs Hsz20 Hsh
  wp_start as ⟨#Hlgf, #Hlgnn, Hlr, #Hkvf, Hkc, HRC, Hbef, Hbs, HRS, Hm, #Huf, #Hcs, Htok⟩
  (try wp_auto)
  wp_apply hLg s lg $$ [Hlr] as ⟨-, Hlr⟩
  · iframe #; iframe Hlr
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
  icases HQ with ⟨HQ, %storedTerm, %hmeta, Hreplay⟩
  wp_apply snapshot_read_cindex_open hRead hUR hID hName hSafe sp γd D 1 (ci, storedTerm) hmeta $$ [Hsn] as Hsn
  · iexact Hsn
  (try wp_auto)
  ipersist lg; ipersist dbsnap; ipersist ci; ipersist term; ipersist terms; ipersist replayConf
  ihave #Pbe : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
  ihave #Psch : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
  · iPkgInit
  ihave #Pmeta : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema.snapshotmeta $$ []
  · iPkgInit
  ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Psch
  icases Hsi with ⟨⟨%bk, #Hmeta, -⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    ⟨%membersBucket, #HmembersBucket, -⟩, ⟨%confKey, #HconfKey, #HconfBytes⟩, -⟩
  ihave #Hbucket := mvcc.meta_isBucket hID hName hSafe bk $$ [$Psch $Hmeta]
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ backend.snapOpenQ sp D γd 1 ∗
    snapi_ptr ↦ (if uint.Z snapi < uint.Z ci then ci else snapi) ∗
    snapt_ptr ↦ (if uint.Z snapi < uint.Z ci then backendTerm else snapt) ∗
    ∃ chosen : Loc, confState_ptr ↦ chosen ∗ epCsVoters γs chosen ∗
      ⌜¬uint.Z snapi < uint.Z ci → chosen = cs⌝)))
    $$ [Hsn Hreplay snapi snapt confState]
  · wp_if_destruct
    · have ahead : uint.Z snapi < uint.Z ci := by first | exact Hif | word
      ihave Hmeta := Hreplay $$ %ahead
      iunfold replayImageMetadata at Hmeta
      icases Hmeta with ⟨%useBoot, Hdecision, Hsource⟩
      have hnz : ci ≠ W64 0 := by word
      simp only [hnz, ahead, ↓reduceIte]
      (try wp_auto)
      wp_bind (If _ _ (Val #false))
      iapply (wp_wand (Φ := fun v => iprop(⌜v = #useBoot⌝))) $$ [Hdecision]
      · by_cases hb : boot = null
        · subst boot
          simp only [↓reduceIte]
          icases Hdecision with %hfalse
          subst useBoot
          (try wp_auto)
          ipureintro; rfl
        · simp only [hb, ↓reduceIte]
          icases Hdecision with ⟨%runs, #Hruns, %hbool⟩
          (try wp_auto)
          (try simp only [hb, decide_false, Bool.not_false, intoVal_eq_iff, ↓reduceIte])
          (try wp_auto)
          rw [replayTerms.TypeAssumptions.ptr_unfold'covers.method_unfold]
          (try wp_auto)
          wp_apply hCovers terms runs ci $$ [$Hpkg $Hruns]
          (try wp_auto)
          ipureintro; rw [hbool]
      iintro %v %hv
      subst v
      cases useBoot
      rotate_left
      · simp only [↓reduceIte]
        icases Hsource with ⟨#Hboot, Ht⟩
        iunfold replaySnapshotTerm at Ht
        simp only [↓reduceIte]
        icases Ht with ⟨%runs, %run, #Hruns, %hfound⟩
        (try wp_auto)
        rw [replayTerms.TypeAssumptions.ptr_unfold'termAt.method_unfold]
        (try wp_auto)
        wp_apply hTermAt terms runs ci run hfound.1 $$ [$Hpkg $Hruns]
        (try wp_auto)
        rw [← hfound.2]
        iframe Hsn snapi snapt
        isplitr; · ipureintro; rfl
        iexists boot; iframe confState Hboot
        ipureintro; intro hf; exact (hf True.intro).elim
      · simp only [Bool.false_eq_true, ↓reduceIte]
        icases Hsource with ⟨Ht, %hreadCfg⟩
        (try wp_auto)
        wp_bind (If _ _ _)
        iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ snapt_ptr ↦ backendTerm))) $$ [Ht snapt]
        · wp_if_destruct
          · iunfold replaySnapshotTerm at Ht
            simp only [↓reduceIte]
            icases Ht with ⟨%runs, %run, #Hruns, %hfound⟩
            (try wp_auto)
            rw [replayTerms.TypeAssumptions.ptr_unfold'termAt.method_unfold]
            (try wp_auto)
            wp_apply hTermAt terms runs ci run hfound.1 $$ [$Hpkg $Hruns]
            (try wp_auto)
            rw [← hfound.2]
            iframe snapt
            (try (ipureintro; rfl))
          · have hz : storedTerm ≠ W64 0 := by first | exact Hif | word
            iunfold replaySnapshotTerm at Ht
            simp only [hz, ↓reduceIte]
            icases Ht with %heq
            (try wp_auto)
            rw [← heq]
            iframe snapt
            (try (ipureintro; rfl))
        iintro %v ⟨%hv, snapt⟩
        subst v
        (try wp_auto)
        wp_apply hreadCfg lg sp γd bk confKey $$ [$Pmeta $Pbe $Hbucket $HconfBytes $Hsn] as %cp ⟨Hsn, Hcfg⟩
        (try wp_auto)
        wp_if_destruct
        · (try simp only [↓reduceIte])
          icases Hcfg with %hread
          unfold replayMemberRead at hread
          (try wp_auto)
          wp_apply hread membersBucket $$ [$Pmeta $Pbe $HmembersBucket $Hsn] as %mp ⟨Hsn, Hmap⟩
          iunfold replaySnapshotMembers at Hmap
          icases Hmap with ⟨%ptrs, %memberID, %learner, Hptrs, #Hmembers, %hmembers⟩
          (try wp_auto)
          iapply wp_fupd
          wp_apply wp_confStateFromMembers mp ptrs (DFrac.own 1) memberID learner
            $$ [$Hpkg $Hptrs $Hmembers] as %value ⟨-, %keys, %hk, Hv, Hl⟩
          obtain ⟨hkeys, hnodup, hshape⟩ := hk
          (try wp_auto)
          have hcfg := hmembers keys hkeys hnodup
          imod confStateFromMembers_freeze γs cs_ptr value.Voters' value.Learners' _ _ hcfg $$ [cs Hv Hl] with #Hnew
          · rw [← hshape]
            iframe cs Hv Hl
          imodintro
          iframe Hsn snapi snapt
          isplitr; · ipureintro; rfl
          iexists cs_ptr
          iframe confState Hnew
          ipureintro; intro hf; exact (hf True.intro).elim
        · have hn : cp ≠ null := by first | exact Hif | assumption
          simp only [hn, ↓reduceIte]
          (try wp_auto)
          iframe Hsn snapi snapt
          iexists cp
          iframe confState Hcfg
          ipureintro; intro hf; exact (hf True.intro).elim
    · have caught : ¬uint.Z snapi < uint.Z ci := by first | exact Hif | word
      simp only [caught, ↓reduceIte]
      (try wp_auto)
      iframe Hsn snapi snapt
      iexists cs; iframe confState Hcs; ipureintro; intro _; rfl
  iintro %v ⟨%hv, Hsn, snapi, snapt, %chosen, confState, #Hchosen, %hchosen⟩
  subst v
  (try wp_auto)
  -- `newSnapshotReaderCloser(lg, dbsnap)`, with half of the snapshot (its `Size` read after)
  icases (backend.snapOpenQ_half sp D γd 1).1 $$ Hsn with ⟨Hsn1, Hsn2⟩
  wp_apply hNSR lg sp D γd $$ [Hsn1] as %rc ⟨Htok, Hrc⟩
  · iframe #; iframe Hsn1
  (try wp_auto)
  ihave #Pproto : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto $$ []
  · iPkgInit
  -- `proto.Clone(confState)`: the clone holds `c`, owned (nil for nil)
  -- (raft-entsize [r3c]) the voters' conf state, of at most `2 ^ 20` ids
  iunfold epCsVoters at Hchosen
  icases Hchosen with ⟨%c, #Hc0, %Hci⟩
  ihave #Hc : csOpt chosen DFrac.discard c $$ []
  · iunfold csOpt; iright; iexact Hc0
  have Hclen : (c.Voters' ++ c.Learners' ++ c.VotersOutgoing' ++ c.LearnersNext').length ≤ 2 ^ 20 := by
    obtain ⟨hv, hvo, hl, hln, -⟩ := Hci
    simp only [List.length_append, hv.length_eq, hvo.length_eq, hl.length_eq, hln.length_eq,
      GMap.length_elements, Membership.simple, GMap.size_empty]
    omega
  wp_apply wp_clone_csOpt hClone chosen c $$ [] as %p' Hp'
  · iframe #
  (try wp_auto)
  -- the merged metadata and snapshot (`&snapi`, `&snapt` frozen: nothing writes them after)
  imod cellRO_alloc snapi_ptr (if uint.Z snapi < uint.Z ci then ci else snapi) $$ snapi with #cI
  imod cellRO_alloc snapt_ptr (if uint.Z snapi < uint.Z ci then backendTerm else snapt) $$ snapt with #cT
  -- (raft-entsize [r3c]) at their contents: fresh literals, without unknown fields
  imod smPtsCC_of_struct «$v0_ptr»
    ({ state' := zeroValDef, ConfState' := p', Index' := snapi_ptr, Term' := snapt_ptr,
       unknownFields' := slice.nil, sizeCache' := 0 } : go_etcd_io.raft.v3.raftpb.SnapshotMetadata)
    (SnapshotMetadataM.mk c (if uint.Z snapi < uint.Z ci then ci else snapi) (if uint.Z snapi < uint.Z ci then backendTerm else snapt)) ⊤ rfl
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
      mergedSt st c (if uint.Z snapi < uint.Z ci then ci else snapi) (if uint.Z snapi < uint.Z ci then backendTerm else snapt) := by
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
  ihave #HszC : msgSzC False ml (mergedSt st c (if uint.Z snapi < uint.Z ci then ci else snapi) (if uint.Z snapi < uint.Z ci then backendTerm else snapt)) $$ []
  · iunfold msgSzC
    iexists _
    ihave #Hro := msgPtsCC_msgRoC ml _ (by simp only [MsgC.resps]; exact hr) $$ HmC
    iframe Hro
    ipureintro; exact ⟨hmodel, hcsu, msgSize_lt_of_ok _ hok, False.elim⟩
  ihave #Hm : msgOwn ml DFrac.discard (mergedSt st c (if uint.Z snapi < uint.Z ci then ci else snapi) (if uint.Z snapi < uint.Z ci then backendTerm else snapt)) $$ []
  · rw [← hmodel]
    iapply msgPtsCC_msgPtsC ml DFrac.discard DFrac.discard false _ hcsu $$ HmC
  -- `dbsnap.Size()`, with the sender's half, which then goes to the reader (the pipe's hand-over)
  ihave #Pbe : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
  wp_apply hSize sp D γd _ $$ [Hsn2] as %n ⟨Hsn2, %Hsz⟩
  · iframe #; iframe Hsn2
  ihave ⟨Hrs, #Hrcc⟩ := Hrc $$ Hsn2
  -- `snap.NewMessage(m, rc, size)`, with the reader's close contract (sweep repairs 1, S1)
  wp_apply hNM ml (mergedSt st c (if uint.Z snapi < uint.Z ci then ci else snapi) (if uint.Z snapi < uint.Z ci then backendTerm else snapt)) rc n $$ [] as %mg ⟨#Hmi, %tsz, %cc, %γc, #Htsz, #Hcc, #Hccb⟩
  · simp only [mergedSt]; iframe Hm Hrcc; ipureintro; exact Hsz
  (try wp_auto)
  iapply HΦ
  simp only [mergedSt]
  iframe Hlr HRS' Hbef Htok
  iexists rc, D, c
  iframe Hm HszC Hrs HQ
  isplitl
  · iunfold mergedMsg
    iframe Hmi
    iexists tsz, cc, γc
    iframe Htsz Hcc Hccb
  isplitr
  · iintro %hno; rw [← hchosen hno]; iexact Hc
  ipureintro; exact ⟨Hci, Hclen⟩

end proof

end EtcdGrove
end Perennial
