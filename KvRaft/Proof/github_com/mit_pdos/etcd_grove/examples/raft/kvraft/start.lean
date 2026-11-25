/-
Proof of `KvRaft/Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvraft/start.lean` (2026-11-24, G5: the body of
`StartNode` until then), at the store's seam (`kvFacts γ`, TCP's per-address premise `tcpAP`, `kvRep γ vs dir`,
the stopper `kvStp γ vs dir`) and the start resource `kvNodeStart γ vs dir` (`StartDefs.lean`). Kvdurable's
`Cluster.start` (`RaftNoAx/.../kvdurablenoax/Cluster__start.lean`), over the network:

* the bootstrap configuration built (`1..Voters`, frozen);
* the storage: `newStorage`, then the file read (the bodied `durable.Read`, its update over the generation's
  file invariant `kdFileInvK`: `durSt` is outside the crash disjunction, and the writer's half pins its
  value `cur`, whose facts `kvStart`'s `fileHolds γ S cur` gives) and, if there is one, `openStorage`;
* the stored snapshot, the replicated state, `FirstIndex`, `Applied`, as in `Cluster.start`;
* the transport, made by the constructor (`ptCtor`, from `kvPeerAddrs`), `RestartNode` (the `raft.Config`
  literal; its update `kv_restartAu`, over the file invariant with the crash token), the transport started
  on the node (`ptFresh`);
* `newReplica`, its send callback the transport's `Send` (`kv_sendSpec_pt`), and the incarnation's stopper
  (`kvStp`: the replica's `repStopper`, the transport's `ptStop`, the start resource's persistent rest).
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.start
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.FileOf
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.newStorage
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.openStorage
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.newReplica
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.decodeState
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Stats__add
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.oneIn
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.below
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.quietLogger__Debugf
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.quietLogger__Errorf
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.quietLogger__Infof
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.quietLogger__Warningf
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.lib.durable.Read
public import KvRaft.Spec.go_etcd_io.raft.v3.RestartNode
public import KvRaft.Spec.go_etcd_io.raft.v3.MemoryStorage__Snapshot
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetData
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import KvRaft.Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetConfState
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.KdStorageApi
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.StartDefs
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.SendLemmas
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.QLogger
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.SnapMake
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.RunLemmas
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.ClusterLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Iris.ProofMode Net go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [Net.NetProtoGS]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [durable_sem : github_com.mit_pdos.etcd_grove.examples.lib.durable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

attribute [local instance] kdStorageModel

theorem start.wp_proof
    (wp_FileOf : FileOf.spec (GF := GF) (hG := hG))
    (wp_Read : github_com.mit_pdos.etcd_grove.examples.lib.durable.Read.spec (GF := GF) (hG := hG))
    (wp_newStorage : newStorage.spec (GF := GF) (hG := hG))
    (wp_openStorage : openStorage.spec (GF := GF) (hG := hG))
    (wp_MSnapshot : MemoryStorage.Snapshot.spec (GF := GF) (hG := hG))
    (wp_GetMetadata : raftpb.Snapshot.GetMetadata.spec (GF := GF) (hG := hG))
    (wp_GetData : raftpb.Snapshot.GetData.spec (GF := GF) (hG := hG))
    (wp_GetIndex : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG))
    (wp_GetConfState : raftpb.SnapshotMetadata.GetConfState.spec (GF := GF) (hG := hG))
    (wp_decodeState : decodeState.spec (GF := GF) (hG := hG))
    (wp_add : Stats.add.spec (GF := GF) (hG := hG))
    (wp_oneIn : oneIn.spec (GF := GF) (hG := hG))
    (wp_below : below.spec (GF := GF) (hG := hG))
    (wp_RestartNode : RestartNode.spec (GF := GF) (hG := hG))
    (wp_newReplica : newReplica.spec (GF := GF) (hG := hG))
    (wp_InitialState : Storage.InitialState.spec (GF := GF) (hG := hG))
    (wp_Snapshot : Storage.Snapshot.spec (GF := GF) (hG := hG))
    (wp_LastIndex : MemoryStorage.LastIndex.spec (GF := GF) (hG := hG))
    (wp_FirstIndex : MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG))
    (wp_Term : MemoryStorage.Term.spec (GF := GF) (hG := hG))
    (wp_Entries : MemoryStorage.Entries.spec (GF := GF) (hG := hG))
    (wp_Debugf : quietLogger.Debugf.spec (GF := GF) (hG := hG))
    (wp_Errorf : quietLogger.Errorf.spec (GF := GF) (hG := hG))
    (wp_Infof : quietLogger.Infof.spec (GF := GF) (hG := hG))
    (wp_Warningf : quietLogger.Warningf.spec (GF := GF) (hG := hG))
    (γ : KdNames) (vs : List w64) (dir : GoString) :
    start.spec (GF := GF) (hG := hG) (kvFacts γ (fun _ => True)) (tcpAP (kvFacts γ (fun _ => True)))
      (kvRep γ vs dir) (kvStp γ vs dir) (kvNodeStart γ vs dir) γ.r.cluster kdRaftN := by
  intro cfg M
  iunfold startLaw
  iintro !> %sp %f
  wp_start as ⟨#HM, HS, #Hstats', #Hctor⟩
  iunfold kvNodeStart at HS
  icases HS with ⟨%Hdir, %fl, %qc, Hst, #Hglob, #Hpeers, %Hopts⟩
  have Hopts0 := Hopts
  ihave #Hglob0 := Hglob
  obtain ⟨Hok, Hvs⟩ := Hopts
  iunfold kvStart at Hst
  icases Hst with ⟨%S, %cur, #Hcl, #Hos, #HosS, #Hdi, Hdh, Hcpm, #HfInv, Hwr, #Hfh, Hvac, %Hfl⟩
  obtain ⟨HdfOk, Hdfn, Hid1, Hidm⟩ := Hfl
  iunfold kvStartGlobals at Hglob
  icases Hglob with ⟨%Hcf, #Hfits, #HstorInv, #Hcci, ⟨%et, #Het⟩, ⟨%ed, #Hed⟩⟩
  obtain ⟨Hdup, Hbl0, Htr0, Hsl, Hmd, Hmax⟩ := Hcf
  obtain ⟨HV1, HV32, HI0, HI62, Hsz⟩ := Hok
  subst Hdir
  try wp_auto
  -- the configuration's fields, read-only
  ipersist cfg
  ihave Hcfg := typedPointsto_split _ _ _ $$ cfg
  simp only [TypedPointsto.typedPointstoDef]
  icases Hcfg with ⟨#cID, #cDir, #cAddrs, #cOpts, -⟩
  ihave Hco := typedPointsto_split _ _ _ $$ cOpts
  simp only [TypedPointsto.typedPointstoDef]
  icases Hco with ⟨#oV, #oP, #oC, #oS, #oM, #oMC, #oI, -⟩
  -- the bootstrap voters
  generalize «$r0_ptr» = bp
  ihave %Hv4nn := typedPointsto_not_null $$ «$r0»
  icases typedPointsto_split _ _ _ $$ «$r0» with Hv4
  simp only [TypedPointsto.typedPointstoDef]
  icases Hv4 with ⟨state, Voters, Learners, VotersOutgoing, LearnersNext, AutoLeave, unknownFields,
    sizeCache, -⟩
  ihave IH : iprop(∃ (k : w64) (sv : GoSlice),
      "id" ∷ id_ptr ↦ k ∗ "HbV" ∷ bp.[raftpb.ConfState, go!"Voters"] ↦ sv ∗
      "Hsv" ∷ sv ↦* raft_kvreconf.bootVoters (uint.nat k - 1) ∗ "Hsvc" ∷ ownSliceCap w64 sv (DFrac.own 1) ∗
      "%Hk" ∷ ⌜1 ≤ uint.nat k ∧ uint.nat k ≤ uint.nat cfg.Opts'.Voters' + 1⌝) $$ [id Voters]
  · iexists W64 1, slice.nil
    iframe id Voters
    simp only [named, show uint.nat (W64 1) - 1 = 0 from rfl, show raft_kvreconf.bootVoters 0 = [] from rfl]
    isplitr
    · iapply ownSlice_nil
    isplitr
    · iapply ownSliceCap_nil
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · try wp_auto
    wp_apply wp_slice_literal (V := w64) [k]
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hsv $Hsvc $Hsl1] as %sv' ⟨Hsv, Hsvc, -⟩
    try wp_auto
    wp_for_post
    iframe
    iexists k + W64 1, sv'
    have Hk1 : uint.nat (k + W64 1) - 1 = uint.nat k := by word
    have Hkv : uint.nat k ≤ uint.nat cfg.Opts'.Voters' := by word
    have Hbv : raft_kvreconf.bootVoters (uint.nat k - 1) ++ [k] = raft_kvreconf.bootVoters (uint.nat k) := by
      obtain ⟨m, hm⟩ : ∃ m, uint.nat k = m + 1 := ⟨uint.nat k - 1, by omega⟩
      rw [hm, show m + 1 - 1 = m from by omega]
      simp only [raft_kvreconf.bootVoters, List.range_succ, List.map_append, List.map_singleton]
      congr 2; word
    rw [Hk1, ← Hbv]
    iframe
    ipureintro; constructor <;> word
  have Hkv : uint.nat k = uint.nat cfg.Opts'.Voters' + 1 := by word
  rw [Hkv, show uint.nat cfg.Opts'.Voters' + 1 - 1 = uint.nat cfg.Opts'.Voters' from by omega, ← Hvs]
  -- the bootstrap conf state, frozen
  ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod pbMsg_alloc raftpb.ConfState bp _ _ slice.nil [] ⊤ (ufWire_nil _) $$ [state sizeCache unknownFields Hnil]
    with #Hpb
  · iframe
  ihave HcsB : csPts bp (DFrac.own 1) (raft_kvreconf.bootCS vs) false
    $$ [HbV Hsv Learners VotersOutgoing LearnersNext AutoLeave]
  · iunfold csPts
    iexists sv, _, _, _, _
    simp only [named, raft_kvreconf.bootCS]
    iframe HbV Hsv Learners VotersOutgoing LearnersNext AutoLeave Hpb
    isplitr
    · ipureintro; exact Hv4nn
    isplitr
    · iapply ownSlice_nil
    isplitr
    · iapply ownSlice_nil
    isplitr
    · iapply ownSlice_nil
    isplitr
    · iapply cellRO_null
    ipureintro; intro h; cases h
  imod csPts_persist _ _ _ _ $$ HcsB with #HbootCS
  ihave #HbootO : ownCSM bp DFrac.discard (raft_kvreconf.bootCS vs) $$ []
  · unfold ownCSM; iexact HbootCS
  -- the file's contents, as the writer's half pins them
  iunfold fileHolds at Hfh
  icases Hfh with ⟨%o', %Hfo, #HcF⟩
  obtain ⟨Hcur, Hoko, HSHo⟩ := Hfo
  subst Hcur
  ihave #Hdur : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.durable
    $$ []
  · iPkgInit
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hpbi : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  ihave #Hinit := isInitialized_access $$ Hraft
  iunfold isInitialized at Hinit
  iNamed Hinit
  have Hvnd : vs.Nodup := by rw [Hvs]; exact raft_kvreconf.bootVoters_nodup _ (by word)
  try wp_auto
  wp_apply wp_FileOf cfg.Dir' cfg.ID' $$ [$Hpkg]
  try wp_auto
  wp_apply wp_newStorage bp $$ [$Hpkg] as %s0 ⟨%ms0, %ip0, %γs0, %Hsz0, HmsF0, #Hsb0, #Himg0, Himage0,
    #Hl0, #Hd00, Hend0, Hsn0, Hmeta0, Hfresh0⟩
  try wp_auto
  rw [← Hdfn]
  wp_bind (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.durable.Read)) _)
  iapply (wp_Read fl.γd fl.df fl.fR qc HdfOk) $$ Hdur Hos HosS Hdi Hdh Hcpm
  -- the file read inside its invariant: its value, `durSt`'s, which the writer's half pins
  iauintro
  unfold atomic_acc
  ihave #HfInv' := HfInv
  iunfold kdFileInvK at HfInv'
  imod inv_acc (E := DurFs.durAuMask) (kdRepN_sub_durAu cfg.ID') $$ HfInv' with ⟨Hi, Hclose⟩
  iunfold kdFileBody at Hi
  imod later_exists_except0 $$ Hi with ⟨%S0, Hi⟩
  imod later_exists_except0 $$ Hi with ⟨%s0', Hi⟩
  imod later_exists_except0 $$ Hi with ⟨%pb0, Hi⟩
  icases Hi with ⟨Hds, Hwv, Hb⟩
  imod Hds
  imod Hwv
  ihave %Hag := ghostVar_agree fl.wr _ _ _ _ $$ Hwr Hwv
  simp only [Prod.mk.injEq] at Hag
  obtain ⟨rfl, rfl, rfl⟩ := Hag
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ DurFs.durAuMask \ ↑(kdRepN .@ uint.nat cfg.ID') from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists ⟨kdFileVal o', none⟩
  iframe Hds
  isplit
  · iintro Hds
    imod Hclose2 with -
    imod Hclose $$ [Hds Hwv Hb] with -
    · inext
      iunfold kdFileBody
      iexists S, ⟨kdFileVal o', none⟩, none
      iframe Hds Hwv Hb
    imodintro
    iframe
  iintro Hds
  imod Hclose2 with -
  imod Hclose $$ [Hds Hwv Hb] with -
  · inext
    iunfold kdFileBody
    iexists S, ⟨kdFileVal o', none⟩, none
    iframe Hds Hwv Hb
  imodintro
  iintro Hdh Hcpm
  simp only [DurFs.readRes]
  try wp_auto
  ihave #Hsb0' : kdStorBoot s0 bp (raft_kvreconf.bootCS vs) $$ []
  · unfold kdStorBoot; iframe Hsb0 HbootO
  wp_bind (If _ _ _)
  iapply (wp_wand_r (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ boot_ptr ↦ bp ∗
    startStor st_ptr bp (raft_kvreconf.bootCS vs) (kdImgOf o'))))
  isplitl [boot st data HmsF0 Himage0 Hend0 Hsn0 Hmeta0 Hfresh0]
  · cases o' with
    | none =>
      simp only [kdFileVal, Option.isSome_none, Option.map_none]
      imod kdStor_register s0 ms0 γs0 ⊤ (fun _ _ => CoPset.mem_full) Hsz0 $$ HstorInv HmsF0 with #Hrec0
      imod memSnapNone_open_empty γs0 $$ Hsn0 with #Hslb0
      try wp_auto
      isplitr
      · ipureintro; first | rfl | trivial
      iframe boot
      unfold startStor
      iexists s0, ms0, ip0, γs0, zero_val EntryM
      have hF : kdImgOf none = imgEmpty := rfl
      have hS : kdFreshSnap imgEmpty = memSnapEmpty := by
        simp [kdFreshSnap, imgEmpty, memSnapEmpty]
      rw [hF, hS]
      simp only [imgEmpty, memSnapEmpty, List.take_nil, List.drop_nil, List.length_nil]
      rw [show uint.nat (W64 0) = 0 from rfl]
      simp only [Nat.zero_add, Nat.add_zero]
      iframe st Hrec0 Hsb0' Hl0 Hfresh0 Hmeta0 Himg0 Himage0 Hd00 Hend0 Hslb0
      isplitr
      · ipureintro; first | rfl | trivial
      isplitr
      · iapply memLog_nil
      isplitr
      · iapply memLog_nil
      iapply memCompacted_zero
    | some f =>
      simp only [kdFileVal, Option.map_some, Option.getD_some, Option.isSome_some]
      try wp_auto
      wp_apply wp_string_to_bytes (encStor f) as %sl ⟨Hsl, -⟩
      have HfOk := Hoko f rfl
      have Hsc : uint.nat f.snap.Metadata'.Index' ≤ uint.nat f.hs.Commit' := by
        by_cases h0 : f.snap.Metadata'.Index' = W64 0
        · rw [h0]; simp
        · have := (HSHo.2.2.2.2.2.2.2.2.1 f.snap (by simp only [kdContents]; rw [if_neg h0])).2
          exact this
      wp_apply wp_openStorage bp (raft_kvreconf.bootCS vs) sl f HfOk Hsc
        $$ [$Hpkg $HstorInv $HbootO $Hsl] as %s %good ⟨%Hgood, %ms, %ip, %γs, %e0, #Hrec, #Hsb,
          #Hl, Hfresh, Hmeta, #Himg, Himage, %He0, #Hd0, #Hfro, Hents, Hend, #Hcmp, #Hslb⟩
      subst Hgood
      try wp_auto
      isplitr
      · ipureintro; first | rfl | trivial
      iframe boot
      unfold startStor kdImgOf kdFreshSnap
      iexists s, ms, ip, γs, e0
      simp only [Option.getD_some]
      iframe st Hrec Hsb Hl Hfresh Hmeta Himg Himage Hd0 Hfro Hents Hend Hcmp Hslb
      ipureintro; exact He0
  iintro %v ⟨%Hv, boot, Hstor⟩
  subst Hv
  -- the contents `F`
  have HFok : KdFileOk (kdImgOf o') := by
    cases o' with
    | none => exact kdFileOk_imgEmpty
    | some f => exact Hoko f rfl
  have HFSH : StorageHolds S (kdContents (some (kdImgOf o'))) := by
    cases o' with
    | none => show StorageHolds S (kdContents (some imgEmpty)); rw [← kdContents_none]; exact HSHo
    | some f => exact HSHo
  have HFof : ∀ f, o' = some f → f = kdImgOf o' := by intro f h; subst h; rfl
  ihave #Hcert : kdSnapCert γ (kdImgOf o').snap $$ []
  · cases o' with
    | none =>
      unfold kdImgOf kdSnapCert
      ileft; ipureintro; rfl
    | some f =>
      unfold kdImgOf
      simp only [Option.getD_some]
      iapply HcF $$ %f %rfl
  generalize HF : kdImgOf o' = F at HFok HFSH HFof ⊢
  iunfold startStor at Hstor
  icases Hstor with ⟨%s, %ms, %ip, %γs, %e0, st, #Hrec, #Hsb, #Hl, Hfresh, Hmeta, #Himg, Himage,
    %He0, #Hd0, #Hfro, Hents, Hend, #Hcmp, #Hslb⟩
  ihave #Hrec' := Hrec
  iunfold kdStorRec at Hrec'
  icases Hrec' with ⟨#Hmsf, -⟩
  try wp_auto
  wp_apply wp_MSnapshot ms γs (kdJ γ.r.cluster γ.files) (some (uint.nat F.prev, kdFreshSnap F))
    (uint.nat F.prev) none _ $$ [$Hraft Hfresh $Hcmp $ErrSnapUnavail]
    as %snap %err ⟨-, %Herr, %sv, Hsn, %Hsv, Hfr⟩
  · rw [memStorAt_some]; iframe Hl Hfresh
  icases Hfr with ⟨%Hsveq, Hfresh⟩
  subst Hsveq
  obtain ⟨HWf, Hp61, Hlen, Hidx, Hpsi, Hsil, Hpc, Hcl, Hterm⟩ := _root_.id HFok
  imod ownSnapW_persist snap _ _ $$ Hsn with ⟨%pm, %pc, %Hpmc, #Hsn, #Hpm, #Hpc, #Hcs⟩
  try wp_auto
  wp_apply wp_GetMetadata.1 snap DFrac.discard (kdFreshSnap F) $$ [$Hpbi $Hsn] as %pm' ⟨#Hsm, -⟩
  wp_apply wp_GetIndex pm' _ _ $$ [$Hpbi $Hsm] as -
  rw [kdFreshSnap_index]
  try wp_auto
  wp_apply wp_map_make1 (K := GoString) (V := GoString) as %mK0 HK0
  wp_apply wp_map_make1 (K := GoString) (V := GoString) as %mA0 HA0
  try wp_auto
  -- the replicated state: the snapshot's, or the empty one at the bootstrap configuration
  wp_bind (If _ _ _)
  iapply (wp_wand_r (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
    ∃ (mK mA csp : Loc) (Kv A : GMap (List w8) (List w8)) (cfg : ConfStateM) (ap : List LogEntry)
      (m : Membership),
      stats_ptr ↦ sp ∗ kv_ptr ↦ mK ∗ ops_ptr ↦ mA ∗ cs_ptr ↦ csp ∗ mK ↦$ Kv ∗ mA ↦$ A ∗
      csOpt csp DFrac.discard cfg ∗ isCommittedLogLb γ.r.cluster ap ∗ confAt γ.r.cluster ap.length m ∗
      ⌜confStateIs cfg m ∧ ap.length = uint.nat F.snap.Metadata'.Index' ∧
        (∀ k, (Kv !! k).getD [] = raft_kvreconf.kvFold (raft_kvreconf.logHist ap) k) ∧
        raft_kvreconf.AppliedOk A (raft_kvreconf.logHist ap) ∧ GMap.size m.ids < 2 ^ 61 ∧
        confStateIs (kdInitCS (raft_kvreconf.bootCS vs) F) m ∧ (ap.length : Int) < 2 ^ 61 ∧
        MapFits Kv ∧ MapFits A⌝ ∗
      (⌜F.snap.Metadata'.Index' = W64 0⌝ ∨ snapshotValid γ.r.cluster F.snap))))
  isplitl [stats kv ops cs HK0 HA0 snap]
  · wp_if_destruct
    · -- no snapshot
      try wp_auto
      isplitr
      · ipureintro; first | rfl | trivial
      iexists mK0, mA0, bp, ∅, ∅, raft_kvreconf.bootCS vs, [], Membership.simple (GMap.listToSet vs)
      iframe stats kv ops cs HK0 HA0
      isplitr
      · iunfold csOpt; iright; iexact HbootO
      isplitr
      · iapply isCommittedLogLb_nil
      isplitr
      · iunfold kdCluster at Hcl
        icases Hcl with ⟨-, -, #Hca0, -⟩
        iexact Hca0
      isplitr
      · ipureintro
        refine ⟨raft_kvreconf.bootCS_is vs Hvnd, by simp; word, ?_, ?_, ?_, ?_, by simp, ?_, ?_⟩
        · intro k; simp [raft_kvreconf.logHist, raft_kvreconf.histOf, raft_kvreconf.kvFold, raft_kvreconf.kvEmpty]
        · refine ⟨fun d => ?_, fun d v h => ?_⟩
          · simp [raft_kvreconf.logHist, raft_kvreconf.histOf]
          · simp at h
        · simp only [Membership.ids, Membership.simple, GMap.union_empty_r_L]
          rw [GMap.size_list_to_set vs Hvnd, Hvs, raft_kvreconf.bootVoters_length]
          word
        · unfold kdInitCS; rw [if_pos (by word)]; exact raft_kvreconf.bootCS_is vs Hvnd
        · intro k v h; simp at h
        · intro k v h; simp at h
      ileft; ipureintro; word
    · -- a snapshot
      have hfs : kdFreshSnap F = F.snap := by unfold kdFreshSnap; rw [if_neg Hif]
      rw [hfs]
      iunfold kdSnapCert at Hcert
      icases Hcert with (%H0 | ⟨#Hsv, %L, %m, #HL, #HcaL, %HLf⟩)
      · exact absurd H0 Hif
      obtain ⟨HLlen, HLdat, HLcs, HLsz⟩ := HLf
      obtain ⟨kvs, ops, Hdat, Hwk, Hwo, Hkv, Hans⟩ := HLdat
      ihave %HL61 : ⌜(L.length : Int) < 2 ^ 61⌝ $$ []
      · iunfold snapshotValid at Hsv
        icases Hsv with ⟨%l', %m', -, -, -, %Hl'⟩
        ipureintro; omega
      try wp_auto
      wp_apply wp_GetData.1 snap _ F.snap $$ [$Hpbi $Hsn] as %ds ⟨Hds, -⟩
      rw [Hdat, ← encState_eq]
      wp_apply wp_decodeState ds _ kvs ops Hwk Hwo $$ [$Hpkg $Hds]
        as %mK %mA ⟨Hds, %K', %A', HK', HA', %HKA⟩
      ihave %Hdsl := ownSlice_len $$ Hds
      have Hel : ((encMap kvs).length : Int) < 2 ^ 63 ∧ ((encMap ops).length : Int) < 2 ^ 63 := by
        obtain ⟨h1, -⟩ := Hdsl
        have h2 : ((encState kvs ops).length : Int) < 2 ^ 63 := by rw [h1]; word
        simp only [encState, List.length_append] at h2
        omega
      try wp_auto
      wp_apply wp_GetMetadata.1 snap DFrac.discard F.snap $$ [$Hpbi $Hsn] as %pm2 ⟨#Hsm2, -⟩
      wp_apply wp_GetConfState pm2 _ _ $$ [$Hpbi $Hsm2] as %pc2 ⟨#Hpc2, -⟩
      ihave #Hcso : csOpt pc2 DFrac.discard F.snap.Metadata'.ConfState' $$ []
      · iunfold csOptA at Hpc2
        iunfold csOpt
        icases Hpc2 with (%H | #H | #H)
        · ileft; ipureintro; exact H
        · iright; iexact H
        · iright; iapply csPts_weaken $$ H
      try wp_auto
      wp_apply wp_add sp (W64 11) (by decide) (by decide) $$ [$Hpkg $Hstats']
      try wp_auto
      isplitr
      · ipureintro; first | rfl | trivial
      iexists mK, mA, pc2, K', A', F.snap.Metadata'.ConfState', L, m
      iframe stats kv ops cs HK' HA' Hcso HL HcaL
      isplitr
      · ipureintro
        refine ⟨HLcs, HLlen, ?_, ?_, HLsz, ?_, HL61, ?_, ?_⟩
        · intro k; rw [HKA.1 k]; exact Hkv k
        · unfold raft_kvreconf.AppliedOk
          have : (fun d => A' !! d) = (fun o => List.lookup o ops) := funext HKA.2
          rw [this]; exact Hans
        · unfold kdInitCS; rw [if_neg Hif]; exact HLcs
        · exact MapFits_of_lookup kvs K' HKA.1 Hel.1
        · exact MapFits_of_lookup ops A' HKA.2 Hel.2
      iright; iexact Hsv
  iintro %v ⟨%Hv, %mK, %mA, %csp, %Kv, %A, %ccs, %ap, %m, stats, kv, ops, cs, HK, HA, #Hcso, #Hap, #Hcap,
    %Hrs, Hval⟩
  subst Hv
  obtain ⟨Hcfgm, Haplen, HKv, HAok, Hmsz, Hinit, Hap61, HKfit, HAfit⟩ := Hrs
  try wp_auto
  -- `FirstIndex`: the log's start plus one (detached: compacted at most there)
  wp_apply Storage.wp_FirstIndex wp_FirstIndex s ms γs (uint.nat F.prev)
    $$ [$Hrec $Hraft $Hl $Hcmp] as %fi ⟨%Hfi, #Hcmp'⟩
  ihave ⟨%Hfi', Hfresh⟩ := memStorFresh_compacted ms γs _ _ _ $$ [$Hfresh $Hcmp']
  have Hfi1 : fi = F.prev + W64 1 := by word
  subst Hfi1
  have Hsi61 : uint.Z F.snap.Metadata'.Index' < 2 ^ 61 := by word
  try wp_auto
  -- `Applied`: `0`, or from the log's start to the snapshot's index
  wp_bind (If _ _ _)
  iapply (wp_wand_r (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
    ∃ (ap0 rf : w64), applied_ptr ↦ ap0 ∗ rafted_ptr ↦ rf ∗ index_ptr ↦ F.snap.Metadata'.Index' ∗
      ⌜(ap0 = W64 0 ∧ rf = F.prev) ∨
        (uint.nat F.prev ≤ uint.nat ap0 ∧ uint.nat ap0 ≤ uint.nat F.snap.Metadata'.Index' ∧
          rf = ap0)⌝)))
  isplitl [applied rafted first index]
  · wp_apply wp_oneIn (W64 3) (by decide) $$ [$Hpkg] as %b -
    cases b with
    | true =>
      try wp_auto
      isplitr
      · ipureintro; first | rfl | trivial
      iexists _, _
      iframe applied rafted index
      ipureintro; left; constructor <;> word
    | false =>
      try wp_auto
      wp_apply wp_below _ $$ [$Hpkg] as %r %Hr
      try wp_auto
      isplitr
      · ipureintro; first | rfl | trivial
      iexists _, _
      iframe applied rafted index
      ipureintro; right
      have Hr' := Hr.2 (by intro h; word)
      refine ⟨by word, by word, rfl⟩
  iintro %v ⟨%Hv, %ap0, %rf, applied, rafted, index, %Hap0⟩
  subst Hv
  try wp_auto
  wp_bind (If _ _ _)
  iapply (wp_wand_r (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ stats_ptr ↦ sp)))
  isplitl [stats]
  · wp_if_destruct
    · try wp_auto
      wp_apply wp_add sp (W64 12) (by decide) (by decide) $$ [$Hpkg $Hstats']
      try wp_auto
      iframe stats; try (ipureintro; first | rfl | trivial)
    · try wp_auto
      iframe stats; try (ipureintro; first | rfl | trivial)
  iintro %v ⟨%Hv, stats⟩
  subst Hv
  try wp_auto
  -- the transport, from the constructor
  ihave #Hpeers' := Hpeers
  iunfold kvPeerAddrs at Hpeers'
  iunfold ptCtor at Hctor
  ihave #Hctor1 := Hctor $$ %(cfg.Addrs') %M %sp
  wp_apply Hctor1 $$ [$Hpkg $HM $Hstats'] as %tv Hpt0
  · simp only [tcpAP]
    iexact Hpeers'
  iunfold ptFresh at Hpt0
  icases Hpt0 with ⟨%i, %Hi, Hpt0⟩
  subst Hi
  try wp_auto
  -- the configuration
  generalize «$a0_ptr» = cp
  ihave Hcv : iprop(∃ cv : Config, cp ↦ cv ∗ ⌜kvCfgOk cfg.ID' s ap0 cv⌝) $$ [«$a0»]
  · iexists _
    iframe «$a0»
    ipureintro
    unfold kvCfgOk ConfigValid
    refine ⟨rfl, rfl, rfl, ⟨?_, ?_, ?_, ⟨by simp only; decide, by simp only; decide⟩, ?_, HI0,
      Or.inl rfl, ?_, Or.inl rfl⟩, HI62, rfl, rfl, rfl, Hsz, rfl, rfl, rfl⟩
    · intro h; simp only at h; rw [h] at Hid1; simp at Hid1
    · intro h; simp only at h; have := Hidm; rw [h] at this; word
    · intro h; simp only at h; have := Hidm; rw [h] at this; word
    · simp [interface.mkOk, kdStorIface]
    · simp [interface.mkOk]
  icases Hcv with ⟨%cv, Hcv, %Hcfg⟩
  obtain ⟨HcID, HcSt, HcLg, HcV, HcM, HcDP, HcRO, HcDC, HcSz, HcAS, HcAp, HcTL⟩ := Hcfg
  -- the node restarted
  have Hsc : uint.nat F.snap.Metadata'.Index' ≤ uint.nat F.hs.Commit' := by
    by_cases h0 : F.snap.Metadata'.Index' = W64 0
    · rw [h0]; simp
    · exact (HFSH.2.2.2.2.2.2.2.2.1 F.snap (by simp only [kdContents]; rw [if_neg h0])).2
  ihave %Htr := kdCluster_untraced γ vs $$ Hcl
  have Hns : ¬ clusterNoSnap γ.r.cluster := fun h => by
    have := clusterNoSnap_boot _ h; omega
  ihave Hrs := kd_restartStorage wp_InitialState wp_Snapshot wp_LastIndex wp_FirstIndex wp_Term
    wp_Entries s ms bp γs F (raft_kvreconf.bootCS vs) e0 γ.r.cluster (uint.nat ap0)
    (fun K => iprop(memStorMeta ms γs F.hs ∗ memStorInvP ms γs (kdJ γ.r.cluster K))) Htr Hmd Hns HFok He0
    (by word) Hsc
    $$ Hpkg Hrec Hsb Hl Hfresh Hmeta Hd0 Hfro Hents Hend Hcmp Hval []
  · iintro %K Hm Hi; iframe Hm Hi
  ihave Hau := kv_restartAu (GF := GF) γ cfg.ID' fl (kdContents (some F)) S o' HFSH $$ [$HfInv Hwr]
  · unfold kdWriter; iexact Hwr
  ihave #Hlogger := qLogger_isLogger wp_Debugf wp_Errorf wp_Infof wp_Warningf
  have Hiface : kdStorIface s =
      GoInterface.ok ⟨go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Storage.ty, #s⟩ :=
    rfl
  have HA : uint.nat cv.Applied' = uint.nat ap0 := by rw [HcAp]
  ihave #Hcl' := Hcl
  iunfold kdCluster at Hcl'
  icases Hcl' with ⟨#HisC, -⟩
  wp_apply (wp_RestartNode γ.r.cluster kdRaftN cp cv qLogger
      ⟨go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Storage.ty, #s⟩
      (kdContents (some F)) (kdInitCS (raft_kvreconf.bootCS vs) F) (uint.nat F.snap.Metadata'.Index') m
      (fun S' => iprop(kdWriter fl S o' ∗ ⌜S' = S⌝))
      (fun K => iprop(memStorMeta ms γs F.hs ∗ memStorInvP ms γs (kdJ γ.r.cluster K)))
      (snapshotValid γ.r.cluster) (fun _ => by iintro H; iexact H)
      HcV HcLg HcSt HcM HcDP HcRO HcDC HcSz HcAS (fun h => absurd Hmd h)
      (by rw [HA]; simp only [kdContents_some_b, kdContents_some_commit]
          rcases Hap0 with ⟨h1, -⟩ | ⟨h1, h2, -⟩
          · left; rw [h1]; rfl
          · right; omega)
      (by rw [HA]; simp only [kdContents_some_b]
          rcases Hap0 with ⟨h1, -⟩ | ⟨h1, h2, -⟩
          · rw [h1]; simp; word
          · omega)
      (by simp only [kdContents_some_commit]; exact Hsc)
      (by rw [Hbl0]; omega) Hinit Hns HcTL Htr0 fl.x)
    $$ [$Hraft $Hcv $Hlogger $HisC $Hfits Hvac Hau Hrs]
    as %nd ⟨%n, %S', %l, %K, %Hnd, #HisNode, #Hl', %Hllen, %HS1b, Hdrv, Hncfg, Hrun, -, Harm, ⟨Hwr, %HS'⟩,
      ⟨Hmeta, #HmsInv⟩⟩
  · rw [HcID, ← Hiface, HA]
    iframe Hvac Hrs
    isplitl [Hau]
    · iexact Hau
    rw [← Haplen]; iexact Hcap
  subst Hnd HS'
  try wp_auto
  ihave #HisNode' : isNode n γ.r.cluster kdRaftN cfg.ID' $$ []
  · rw [← HcID]; iexact HisNode
  -- the transport started on the node
  wp_apply Hpt0 $$ %n Hpkg HisNode' as Hrun
  iunfold ptRunning at Hrun
  icases Hrun with ⟨#Hsend0, Hpstop⟩
  -- the tick
  wp_apply wp_below (W64 4) $$ [$Hpkg] as %rt %Hrt
  have Hrt' := Hrt.2 (by decide)
  try wp_auto
  -- the replica
  ihave #Hsend := kv_sendSpec_pt γ (fun _ => True) cfg.ID' i Hdup $$ Hsend0
  have Hl0 : l.length = max (uint.nat F.prev) (uint.nat ap0) := by
    rw [Hllen, HA]; rfl
  have Hlsi : l.length ≤ uint.nat F.snap.Metadata'.Index' := by
    rcases Hap0 with ⟨h1, -⟩ | ⟨h1, h2, -⟩
    · rw [h1] at Hl0; simp at Hl0; word
    · omega
  have Hrafted : uint.nat rf = l.length := by
    rcases Hap0 with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · rw [h1] at Hl0; rw [h2, Hl0]; simp
    · rw [h3, Hl0]; omega
  ihave #Hfz : memLog γs (uint.nat F.prev + 1) DFrac.discard (F.ents.take (l.length - uint.nat F.prev))
    $$ [Hfro]
  · iapply memLog_take_le γs _ F.ents _ _ (by omega) $$ Hfro
  ihave #Hfzt : raft_kvreconf.frozenTo γs (uint.nat F.prev) l $$ []
  · unfold raft_kvreconf.frozenTo
    have h := HS1b
    simp only [kdContents_some_b, kdContents_some_ents] at h
    rw [h]; iexact Hfz
  have Hsiw : F.snap.Metadata'.Index' = W64 ap.length := by rw [Haplen]; word
  rw [show (#(F.snap.Metadata'.Index') : val) = #(W64 ap.length) by rw [Hsiw]]
  rw [← Hiface]
  ihave Hncfg : nodeConfig n γ.r.cluster kdRaftN ⟨ap.length, m⟩ $$ [Hncfg]
  · rw [Haplen]; iexact Hncfg
  have Hl0' : uint.nat F.prev ≤ l.length := by rw [Hl0]; omega
  have Htk := tick_pos rt Hrt'
  rw [Hdfn]
  wp_apply (wp_newReplica γ vs cfg.Dir' cfg.ID' n s sp ms γs K mK mA csp Kv A ap l m
      ccs ip F.hs S' o' F rf _ _ fl qc Htk rfl HFok HFSH Hap61 Hrafted HFof (by omega) Hl0' (by omega)
      Hid1 Hidm Hmsz Haplen HKfit HAfit HdfOk Hdfn)
    $$ [$Hpkg $Hcci $Hcl $Hstats' $Hos $HosS $Hdi $HfInv $Hdh $Hcpm $Harm $HisNode' $Hdrv $Hncfg $Hrun
      $Hrec $HmsInv $Hmeta $Himg $Himage $Hcert $Hwr $Hcmp $Hfz $Hfzt $Hslb $HK $HA $Hcso $Hap $Hcap
      $Hsend]
    as %r ⟨⟨%st', %sts', %sq', %ρ, #Hr⟩, Hrs⟩
  · ipureintro; exact ⟨Hcfgm, HKv, HAok, Hmd, Hns⟩
  try wp_auto
  -- the incarnation, with its stopper
  ihave #Hr' := Hr
  iunfold isReplicaR at Hr'
  iNamed Hr'
  iunfold isReplica at Hrep
  iNamed Hrep
  iapply HΦ
  iexists n
  isplitr
  · iexact Hnode
  isplitr
  · imodintro
    unfold kvRep isRep
    iexists n, st', sts', sq', ρ
    iexact Hr
  isplitr
  · iexact HisNode'
  simp only [kvStp]
  isplitl [Hrs]
  · iexact Hrs
  isplitl [Hpstop]
  · iexact Hpstop
  isplitr
  · ipureintro; first | rfl | trivial
  isplitr
  · iexact Hglob0
  isplitr
  · iexact Hpeers
  ipureintro; exact Hopts0

end proof

end kvraft
end EtcdGrove
end Perennial
