/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/Cluster__start.lean`. Lean-first
(no Rocq counterpart).

The storage: `newStorage` always, then the file read (`durable.Read`, inside the file's invariant,
whose contents the writer's half pins) and, if there is one, `openStorage` of its bytes;
both give the storage of the contents `F = kdImgOf o` (`imgEmpty` for no file) detached, its log
split at the stored snapshot's index (frozen below, owned above). `MemoryStorage.Snapshot`, detached,
returns the stored snapshot (`kdFreshSnap F`); its index `si` is `F`'s snapshot's. The replicated
state: the snapshot's (`decodeState` of its data, its conf state; the certificate's committed prefix
`L` of length `si`), or the empty state at the bootstrap configuration at index `0`. `FirstIndex` is
`F.prev + 1` (detached: compacted at most there). `Applied`: `0`, or `F.prev + below(si - F.prev + 1)`.
`RestartNode` on the storage's `restartStorage` (from `kd_restartStorage`, frozen at the stored
snapshot's index), its update fired at once over the file invariant's durable state
(`kd_restartAu`, the invariant opened inside it), and `newReplica` gets the node, the storage attached at the driver's key, the frozen prefix up to the
delivered log (`memLog_take_le`, S1b for `frozenTo`), the replicated state and the transport.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__start
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__fileOf
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__config
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__tick
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__sender
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.newStorage
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.openStorage
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.newReplica
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.decodeState
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Stats__add
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.oneIn
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.below
public import Spec.github_com.mit_pdos.etcd_grove.examples.durable.Read
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Snapshot
public import Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata
public import Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetData
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetConfState
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.KdStorageApi
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.StartLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Config
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.ClusterLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.SnapMake

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [durable_sem : github_com.mit_pdos.etcd_grove.examples.durable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

/-- The stored snapshot's index is the file's snapshot's (the empty one's `0` at index `0`). -/
theorem kdFreshSnap_index (f : StorFile) :
    (kdFreshSnap f).Metadata'.Index' = f.snap.Metadata'.Index' := by
  unfold kdFreshSnap
  by_cases h : f.snap.Metadata'.Index' = W64 0
  · rw [if_pos h, h]; rfl
  · rw [if_neg h]

/-- No file restores the empty image's contents. -/
theorem kdContents_none : kdContents none = kdContents (some imgEmpty) := by
  simp [kdContents, kdEmpty, imgEmpty, memSnapEmpty]

/-- The empty image passes `openStorage`'s checks. -/
theorem kdFileOk_imgEmpty : KdFileOk imgEmpty := by
  simp [KdFileOk, StorWf, SnapWf, ConfWf, imgEmpty, memSnapEmpty, KdSnapTermOk, imgTermAt]
  word

/-- **The storage of the contents `F`, detached** (`openStorage`'s post, or `newStorage`'s for no
file): the variable `st` holding it, its log split at the stored snapshot's index. -/
def startStor (stp bp : Loc) (boot : ConfStateM) (F : StorFile) : IProp GF :=
  iprop(∃ (s ms ip : Loc) (γs : MemStorNames) (e0 : EntryM),
    stp ↦ s ∗ kdStorRec s ms γs ∗ kdStorBoot s bp boot ∗ memStorLock ms γs ∗
    memStorFresh ms γs (uint.nat F.prev) (kdFreshSnap F) ∗ memStorMeta ms γs F.hs ∗
    s.[KStorage, go!"img"] ↦□ ip ∗ ownImage ip F ∗ ⌜e0.Term' = F.prevTerm⌝ ∗
    memLog γs (uint.nat F.prev) DFrac.discard [e0] ∗
    memLog γs (uint.nat F.prev + 1) DFrac.discard
      (F.ents.take (uint.nat F.snap.Metadata'.Index' - uint.nat F.prev)) ∗
    memLog γs (uint.nat F.snap.Metadata'.Index' + 1) (DFrac.own 1)
      (F.ents.drop (uint.nat F.snap.Metadata'.Index' - uint.nat F.prev)) ∗
    memEnd γs (uint.nat F.prev + F.ents.length + 1) ∗
    memCompacted γs (uint.nat F.prev) ∗ memSnapLb γs (uint.nat F.snap.Metadata'.Index'))

theorem Cluster.start.wp_proof
    (wp_fileOf : Cluster.fileOf.spec (GF := GF) (hG := hG))
    (wp_Read : github_com.mit_pdos.etcd_grove.examples.durable.Read.spec (GF := GF) (hG := hG))
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
    (wp_config : Cluster.config.spec (GF := GF) (hG := hG))
    (wp_RestartNode : RestartNode.spec (GF := GF) (hG := hG))
    (wp_tick : Cluster.tick.spec (GF := GF) (hG := hG))
    (wp_sender : Cluster.sender.spec (GF := GF) (hG := hG))
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
    (wp_Warningf : quietLogger.Warningf.spec (GF := GF) (hG := hG)) :
    Cluster.start.spec (GF := GF) (hG := hG) := by
  intro γ vs dir c id S fo Hid1 Hid9
  wp_start as ⟨#Hc, #HfInv, Hvac, Hwr, #Hknown⟩
  ihave #Hc' := Hc
  iunfold isClusterC at Hc'
  iNamed Hc'
  ihave #Hcl' := Hcl
  iunfold kdCluster at Hcl'
  icases Hcl' with ⟨#HisC, -, #Hca0, -, -, #Hfiles⟩
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  ihave #Hinit := isInitialized_access $$ Hraft
  iunfold isInitialized at Hinit
  iNamed Hinit
  have Hvnd : vs.Nodup := by rw [Ho.2]; exact kvreconf.bootVoters_nodup _ (by have := Ho.1.2.1; word)
  try wp_auto
  wp_apply (lc := 2) wp_fileOf γ vs dir c id $$ [$Hc]
  try wp_auto
  wp_apply wp_newStorage bp $$ [$Hpkg] as %s0 ⟨%ms0, %ip0, %γs0, HmsF0, #Hsb0, #Himg0, Himage0,
    #Hl0, #Hd00, Hend0, Hsn0, Hmeta0, Hfresh0⟩
  try wp_auto
  wp_bind (App (Val (@! github_com.mit_pdos.etcd_grove.examples.durable.Read)) _)
  iapply github_com.mit_pdos.etcd_grove.examples.durable.Read.wp_file_au wp_Read γ.files kdFilesN
    _ _ $$ Hfiles
  -- the file read inside its invariant (the writer's half pins it): its contents `o'`, their facts
  -- and the stored snapshot's certificate
  ihave #HfInv' := HfInv
  iunfold kdFileInv at HfInv'
  iinv HfInv' with HI Hclose
  · exact kdRepN_files id
  imod lc_fupd_elim_later $$ Hlc1 HI with HI
  icases HI with ⟨%S0, %o', ⟨HrS, Hdf⟩, Hwv, %Hfacts, HcF⟩
  ihave %Hag := ghostVar_agree (γ.wr id) _ _ _ _ $$ [Hwr] Hwv
  · unfold kdWriter; iexact Hwr
  obtain ⟨h1, Hvalo⟩ := Prod.mk.inj Hag
  subst h1
  obtain ⟨HSHo, Hoko⟩ := Hfacts
  ihave #Hcert : kdSnapCert γ (kdImgOf o').snap $$ [HcF]
  · cases o' with
    | none =>
      unfold kdImgOf kdSnapCert
      ileft; ipureintro; rfl
    | some f =>
      unfold kdImgOf
      simp only [Option.getD_some]
      iapply HcF $$ %f %rfl
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists kdFileVal o'
  iframe Hdf
  iintro Hdf
  imod Hmask with -
  imod Hclose $$ [HrS Hdf Hwv HcF] with -
  · inext
    iexists S, o'
    iframe HrS Hdf Hwv HcF
    ipureintro; exact ⟨HSHo, Hoko⟩
  imodintro
  simp only [durableReadVal]
  try wp_auto
  ihave #Hsb0' : kdStorBoot s0 bp (kvreconf.bootCS vs) $$ []
  · unfold kdStorBoot; iframe Hsb0 HbootCS
  wp_bind (If _ _ _)
  iapply (wp_wand_r (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ c_ptr ↦ c ∗
    startStor st_ptr bp (kvreconf.bootCS vs) (kdImgOf o'))))
  isplitl [c st data HmsF0 Himage0 Hend0 Hsn0 Hmeta0 Hfresh0]
  · cases o' with
    | none =>
      simp only [kdFileVal, Option.isSome_none, Option.map_none]
      imod kdStor_register s0 ms0 γs0 ⊤ (fun _ _ => CoPset.mem_full) $$ HstorInv HmsF0 with #Hrec0
      imod memSnapNone_open γs0 $$ Hsn0 with #Hslb0
      try wp_auto
      isplitr
      · ipureintro; first | rfl | trivial
      iframe c
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
        · have := (HSHo.2.2.2.2.2.2.2.1 f.snap (by simp only [kdContents]; rw [if_neg h0])).2
          exact this
      wp_apply wp_openStorage bp (kvreconf.bootCS vs) sl f HfOk Hsc
        $$ [$Hpkg $HstorInv $HbootCS $Hsl] as %s %good ⟨%Hgood, %ms, %ip, %γs, %e0, #Hrec, #Hsb,
          #Hl, Hfresh, Hmeta, #Himg, Himage, %He0, #Hd0, #Hfro, Hents, Hend, #Hcmp, #Hslb⟩
      subst Hgood
      try wp_auto
      isplitr
      · ipureintro; first | rfl | trivial
      iframe c
      unfold startStor kdImgOf kdFreshSnap
      iexists s, ms, ip, γs, e0
      simp only [Option.getD_some]
      iframe st Hrec Hsb Hl Hfresh Hmeta Himg Himage Hd0 Hfro Hents Hend Hcmp Hslb
      ipureintro; exact He0
  iintro %v ⟨%Hv, c, Hstor⟩
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
  generalize HF : kdImgOf o' = F at HFok HFSH HFof ⊢
  iunfold startStor at Hstor
  icases Hstor with ⟨%s, %ms, %ip, %γs, %e0, st, #Hrec, #Hsb, #Hl, Hfresh, Hmeta, #Himg, Himage,
    %He0, #Hd0, #Hfro, Hents, Hend, #Hcmp, #Hslb⟩
  ihave #Hrec' := Hrec
  iunfold kdStorRec at Hrec'
  icases Hrec' with ⟨#Hmsf, -⟩
  try wp_auto
  wp_apply wp_MSnapshot ms γs (kdJ γ.r.cluster γ.files) (some (uint.nat F.prev, kdFreshSnap F))
    (uint.nat F.prev) false _ $$ [$Hraft Hfresh $Hcmp $ErrSnapUnavail]
    as %snap %err ⟨-, %Herr, %sv, Hsn, %Hsv, Hfr⟩
  · isplitl [Hfresh]
    · rw [memStorAt_some]; iframe Hl Hfresh
    · simp only [Bool.false_eq_true, ↓reduceIte]; iempintro
  icases Hfr with ⟨%Hsveq, Hfresh⟩
  subst Hsveq
  obtain ⟨HWf, Hp61, Hlen, Hidx, Hpsi, Hsil, Hpc, Hcl, Hterm⟩ := _root_.id HFok
  imod ownSnapW_persist snap _ _ $$ Hsn with ⟨%pm, %pc, %Hpmc, #Hsn, #Hpm, #Hpc, #Hcs⟩
  try wp_auto
  wp_apply wp_GetMetadata.1 snap DFrac.discard (kdFreshSnap F) $$ [$Hpb $Hsn] as %pm' ⟨#Hsm, -⟩
  wp_apply wp_GetIndex pm' _ _ $$ [$Hpb $Hsm] as -
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
      c_ptr ↦ c ∗ kv_ptr ↦ mK ∗ ops_ptr ↦ mA ∗ cs_ptr ↦ csp ∗ mK ↦$ Kv ∗ mA ↦$ A ∗
      csOpt csp DFrac.discard cfg ∗ isCommittedLogLb γ.r.cluster ap ∗ confAt γ.r.cluster ap.length m ∗
      ⌜confStateIs cfg m ∧ ap.length = uint.nat F.snap.Metadata'.Index' ∧
        (∀ k, (Kv !! k).getD [] = kvreconf.kvFold (kvreconf.logHist ap) k) ∧
        kvreconf.AppliedOk A (kvreconf.logHist ap) ∧ GMap.size m.ids < 2 ^ 61 ∧
        confStateIs (kdInitCS (kvreconf.bootCS vs) F) m ∧ (ap.length : Int) < 2 ^ 61⌝ ∗
      (⌜F.snap.Metadata'.Index' = W64 0⌝ ∨ snapshotValid γ.r.cluster F.snap))))
  isplitl [c kv ops cs HK0 HA0 snap]
  · wp_if_destruct
    · -- no snapshot
      try wp_auto
      isplitr
      · ipureintro; first | rfl | trivial
      iexists mK0, mA0, bp, ∅, ∅, kvreconf.bootCS vs, [], Membership.simple (GMap.listToSet vs)
      iframe c kv ops cs HK0 HA0 Hca0
      isplitr
      · iunfold csOpt; iright; iexact HbootCS
      isplitr
      · iapply isCommittedLogLb_nil
      isplitr
      · ipureintro
        refine ⟨kvreconf.bootCS_is vs Hvnd, by simp; word, ?_, ?_, ?_, ?_, by simp⟩
        · intro k; simp [kvreconf.logHist, kvreconf.histOf, kvreconf.kvFold, kvreconf.kvEmpty]
        · refine ⟨fun d => ?_, fun d v h => ?_⟩
          · simp [kvreconf.logHist, kvreconf.histOf]
          · simp at h
        · simp only [Membership.ids, Membership.simple, GMap.union_empty_r_L]
          rw [GMap.size_list_to_set vs Hvnd, Ho.2, kvreconf.bootVoters_length]
          have := Ho.1.2.1; word
        · unfold kdInitCS; rw [if_pos (by word)]; exact kvreconf.bootCS_is vs Hvnd
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
      wp_apply wp_GetData.1 snap _ F.snap $$ [$Hpb $Hsn] as %ds ⟨Hds, -⟩
      rw [Hdat, ← encState_eq]
      wp_apply wp_decodeState ds _ kvs ops Hwk Hwo $$ [$Hpkg $Hds]
        as %mK %mA ⟨-, %K', %A', HK', HA', %HKA⟩
      try wp_auto
      wp_apply wp_GetMetadata.1 snap DFrac.discard F.snap $$ [$Hpb $Hsn] as %pm2 ⟨#Hsm2, -⟩
      wp_apply wp_GetConfState pm2 _ _ $$ [$Hpb $Hsm2] as %pc2 ⟨#Hpc2, -⟩
      ihave #Hcso : csOpt pc2 DFrac.discard F.snap.Metadata'.ConfState' $$ []
      · iunfold csOptA at Hpc2
        iunfold csOpt
        icases Hpc2 with (%H | #H | #H)
        · ileft; ipureintro; exact H
        · iright; iexact H
        · iright; iapply csPts_weaken $$ H
      try wp_auto
      ihave #Hc1 := isStats_field (c.[KCluster, go!"Stats"]) go!"RestartsFromSnapshot" (by decide)
        $$ Hstats
      wp_apply wp_add (c.[KCluster, go!"Stats"]) _ $$ [$Hpkg $Hc1]
      try wp_auto
      isplitr
      · ipureintro; first | rfl | trivial
      iexists mK, mA, pc2, K', A', F.snap.Metadata'.ConfState', L, m
      iframe c kv ops cs HK' HA' Hcso HL HcaL
      isplitr
      · ipureintro
        refine ⟨HLcs, HLlen, ?_, ?_, HLsz, ?_, HL61⟩
        · intro k; rw [HKA.1 k]; exact Hkv k
        · unfold kvreconf.AppliedOk
          have : (fun d => A' !! d) = (fun o => List.lookup o ops) := funext HKA.2
          rw [this]; exact Hans
        · unfold kdInitCS; rw [if_neg Hif]; exact HLcs
      iright; iexact Hsv
  iintro %v ⟨%Hv, %mK, %mA, %csp, %Kv, %A, %cfg, %ap, %m, c, kv, ops, cs, HK, HA, #Hcso, #Hap, #Hcap,
    %Hrs, Hval⟩
  subst Hv
  obtain ⟨Hcfgm, Haplen, HKv, HAok, Hmsz, Hinit, Hap61⟩ := Hrs
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
  iapply (wp_wand_r (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ c_ptr ↦ c)))
  isplitl [c]
  · wp_if_destruct
    · ihave #Hc2 := isStats_field (c.[KCluster, go!"Stats"]) go!"RestartsAppliedBelow" (by decide)
        $$ Hstats
      try wp_auto
      wp_apply wp_add (c.[KCluster, go!"Stats"]) _ $$ [$Hpkg $Hc2]
      try wp_auto
      iframe c; try (ipureintro; first | rfl | trivial)
    · try wp_auto
      iframe c; try (ipureintro; first | rfl | trivial)
  iintro %v ⟨%Hv, c⟩
  subst Hv
  try wp_auto
  -- the node restarted
  have Hsc : uint.nat F.snap.Metadata'.Index' ≤ uint.nat F.hs.Commit' := by
    by_cases h0 : F.snap.Metadata'.Index' = W64 0
    · rw [h0]; simp
    · exact (HFSH.2.2.2.2.2.2.2.1 F.snap (by simp only [kdContents]; rw [if_neg h0])).2
  have Hnid0 : id ≠ W64 0 := by intro h; rw [h] at Hid1; simp at Hid1
  wp_apply wp_config γ vs dir c id s ap0 Hnid0 (by word) $$ [$Hc] as %cp ⟨%cv, Hcv, %Hcfg⟩
  obtain ⟨HcID, HcSt, HcLg, HcV, HcM, HcDP, HcRO, HcDC, HcSz, HcAS, HcAp⟩ := Hcfg
  ihave Hrs := kd_restartStorage wp_InitialState wp_Snapshot wp_LastIndex wp_FirstIndex wp_Term
    wp_Entries s ms bp γs F (kvreconf.bootCS vs) e0 γ.r.cluster (uint.nat ap0)
    (fun K => iprop(memStorMeta ms γs F.hs ∗ memStorInvP ms γs (kdJ γ.r.cluster K))) HFok He0
    (by word) Hsc
    $$ Hpkg Hrec Hsb Hl Hfresh Hmeta Hd0 Hfro Hents Hend Hcmp Hval []
  · iintro %K Hm Hi; iframe Hm Hi
  ihave Hau := kd_restartAu (GF := GF) γ dir id (kdContents (some F)) S fo HFSH $$ [$HfInv $Hwr]
  ihave #Hlogger := qLogger_isLogger wp_Debugf wp_Errorf wp_Infof wp_Warningf
  have Hiface : kdStorIface s =
      GoInterface.ok ⟨go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.kvdurable.Storage.ty, #s⟩ :=
    rfl
  have HA : uint.nat cv.Applied' = uint.nat ap0 := by rw [HcAp]
  wp_apply (wp_RestartNode γ.r.cluster kdRaftN cp cv qLogger
      ⟨go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.kvdurable.Storage.ty, #s⟩
      (kdContents (some F)) (kdInitCS (kvreconf.bootCS vs) F) (uint.nat F.snap.Metadata'.Index') m
      (fun S' => iprop(kdWriter γ id S fo ∗ ⌜S' = S⌝))
      (fun K => iprop(memStorMeta ms γs F.hs ∗ memStorInvP ms γs (kdJ γ.r.cluster K)))
      HcV HcLg HcSt HcM HcDP HcRO HcDC HcSz HcAS
      (by rw [HA]; simp only [kdContents_some_b, kdContents_some_commit]
          rcases Hap0 with ⟨h1, -⟩ | ⟨h1, h2, -⟩
          · left; rw [h1]; rfl
          · right; omega)
      (by rw [HA]; simp only [kdContents_some_b]
          rcases Hap0 with ⟨h1, -⟩ | ⟨h1, h2, -⟩
          · rw [h1]; simp; word
          · omega)
      (by simp only [kdContents_some_commit]; exact Hsc)
      (by rw [Hbl0]; omega) Hinit)
    $$ [$Hraft $Hcv $Hlogger $HisC Hvac Hau Hrs]
    as %nd ⟨%n, %S', %l, %K, %Hnd, #HisNode, #Hl', %Hllen, %HS1b, Hdrv, Hncfg, Hrun, ⟨Hwr, %HS'⟩,
      ⟨Hmeta, #HmsInv⟩⟩
  · rw [HcID, ← Hiface, HA]
    iframe Hvac Hrs
    isplitl [Hau]
    · iexact Hau
    rw [← Haplen]; iexact Hcap
  subst Hnd HS'
  try wp_auto
  wp_apply wp_tick γ vs dir c $$ [$Hc] as %tk %Htk
  -- the writer's half for the new incarnation, at the contents `o'` the file holds
  ihave Hwr : kdWriter γ id S' o' $$ [Hwr]
  · unfold kdWriter; rw [← Hvalo]; iexact Hwr
  try wp_auto
  wp_apply wp_sender γ vs dir c id $$ [$Hc $Hknown] as %fs #Hf
  try wp_auto
  -- the delivered log: frozen in the storage, the stored entries (S1b)
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
  ihave #Hfzt : kvreconf.frozenTo γs (uint.nat F.prev) l $$ []
  · unfold kvreconf.frozenTo
    have h := HS1b
    simp only [kdContents_some_b, kdContents_some_ents] at h
    rw [h]; iexact Hfz
  have Hsiw : F.snap.Metadata'.Index' = W64 ap.length := by rw [Haplen]; word
  rw [show (#(F.snap.Metadata'.Index') : val) = #(W64 ap.length) by rw [Hsiw]]
  ihave #HisNode' : isNode n γ.r.cluster kdRaftN id $$ []
  · rw [← HcID]; iexact HisNode
  rw [← Hiface] at *
  ihave Hncfg : nodeConfig n γ.r.cluster kdRaftN ⟨ap.length, m⟩ $$ [Hncfg]
  · rw [Haplen]; iexact Hncfg
  have Hl0' : uint.nat F.prev ≤ l.length := by rw [Hl0]; omega
  wp_apply (wp_newReplica γ vs dir id n s (c.[KCluster, go!"Stats"]) sq ms γs K mK mA csp Kv A ap l m
      cfg ip F.hs S' o' F rf tk fs Htk rfl HFok HFSH Hap61 Hrafted HFof (by omega) Hl0' (by omega)
      Hid1 Hid9 Hmsz Haplen)
    $$ [$Hpkg $Hcci $Hcl $Hstats $Hseqs $HfInv $HisNode' $Hdrv $Hncfg $Hrun $Hrec $HmsInv $Hmeta
      $Himg $Himage $Hcert $Hwr $Hcmp $Hfz $Hfzt $Hslb $HK $HA $Hcso $Hap $Hcap $Hf]
    as %r ⟨Hr, Hstop⟩
  · ipureintro; exact ⟨Hcfgm, HKv, HAok⟩
  try wp_auto
  iapply HΦ
  iframe Hr Hstop

end proof

end kvdurable
end EtcdGrove
end Perennial
