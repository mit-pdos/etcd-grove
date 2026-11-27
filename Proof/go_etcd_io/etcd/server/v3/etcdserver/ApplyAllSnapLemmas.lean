/-
The lemmas of `applyAll`'s snapshot case (`kvAppliedOn_sa`, `snapRecv_imageR`, `snapRecv_imageOnR`,
`srvSnapDir_of_RO`), moved unchanged out of its proof `ApplyAllSnap.lean` (import tiers, 2026-11-19:
the examples' definitions import them, and a proof file is imported by linking modules only).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applyAll
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applySnapshot
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applyEntries
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Backend
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__snapshotIfNeededAndCompactRaftLog
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.VerifyBackendConsistency
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapRecvFacts
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapRO
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTerm
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetSnapshot
public import Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__ReportSnapshot
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex__ConsistentIndex
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapSendBranch
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.MergedImageOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapAuthRecover
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapRecvOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyRDefs

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section kvsa
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The applied auth state is the applied log's** (`kvAppliedOn`'s model). -/
theorem kvAppliedOn_sa (γr : ReadNames) (A : List EntryModel) (x : apply.ApplyKV)
    (sa : auth.AuthState) :
    kvAppliedOn (GF := GF) γr.raft γr.kv srvAuthSt0 A x sa (kvLeasesOn γr.kv srvAuthSt0 A) ⊢
      kvAppliedOn γr.raft γr.kv srvAuthSt0 A x sa (kvLeasesOn γr.kv srvAuthSt0 A) ∗ ⌜sa = srvAuthAtLog γr.kv srvAuthSt0 A⌝ := by
  iintro H
  iunfold kvAppliedOn at H
  icases H with ⟨Hl, %Hch⟩
  iunfold kvAppliedLOn at Hl
  icases Hl with ⟨H1, H2, H3, %He⟩
  isplitl
  · iunfold kvAppliedOn; iunfold kvAppliedLOn; iframe H1 H2 H3; ipureintro; exact ⟨He, Hch⟩
  ipureintro
  unfold srvAuthAtLog
  rw [← He]

/-- **The applied auth state's revision is at least 1, with auth on** (auth-schema-srv A6's L-rev: the
lend's premise). -/
theorem kvAppliedM_rev (on : Bool) (γr : ReadNames) (A : List EntryModel) (x : apply.ApplyKV)
    (sa : auth.AuthState) :
    kvAppliedM (GF := GF) on γr.raft γr.kv srvAuthSt0 A x sa ⊢
      kvAppliedM on γr.raft γr.kv srvAuthSt0 A x sa ∗ ⌜on = true → 1 ≤ sa.revision⌝ := by
  cases on with
  | false =>
    iintro H; iframe H; ipureintro; intro h; cases h
  | true =>
    simp only [kvAppliedM]
    iintro H
    icases kvAppliedOn_sa γr A x sa $$ H with ⟨H, %hsa⟩
    iframe H
    ipureintro; intro _; rw [hsa]; exact srvAuthAtLog_rev_pos γr.kv A

end kvsa

section recvR
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
open go_etcd_io.raft.v3

/-! ### The snapshot receive inside the window (R2d'a task 4)

`snapRecv_image(On)` with the rest buckets at an image `r0` of the applied log `A`'s table
(`srvRestRp E γr A r0`) whose members have the model's ids (`hids`; inside the window `r0` is
`restReplay`, `restReplay_memKeys`), through the ids form of `membership.clusterImageOk_restModel`.
The proofs are the frozen ones with the rest opened and closed by `srvRestRp_open`/`srvRestRp_close`. -/

/-- **`snapRecv_image` inside the window** (R2d'a task 4): at an image `r0` with the model's ids. -/
theorem snapRecv_imageR (γ : SrvRaft) (γr : ReadNames) (E : apply.AEnv GF) (i ai : w64)
    (D : backend.Data) (d : mvcc.KBReal) (A : List EntryModel) (x : apply.ApplyKV) (cl : Loc)
    (H : IProp GF)
    (hraft : γr.raft = ⟨γ, [], W64 0⟩) (hc0 : γr.kv.c0 = W64 0)
    (hch : γr.kv.ch0 = apply.alarmChain false false false) (hlog0 : γr.kv.log0 = [[], []])
    (hai : uint.Z ai = uint.Z γr.raft.ai0 + A.length) (hi : uint.Z ai < uint.Z i)
    (hboot : (γ.boot.length : Int) ≤ uint.Z i)
    (hRO : E.RO = srvRestOwnH E.authMode d.γB cl H)
    (r0 : apply.RestM)
    (hids : ∀ k, (r0.mem !! k).isSome =
      ((restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)).mem !! k).isSome) :
    ⊢ srvKVInvs E γr -∗ srvImage γ i D -∗ kvApplied γr.raft γr.kv A x -∗ srvRestRp E γr A r0 -∗
      membership.isRaftCluster cl ={⊤}=∗
      kvApplied γr.raft γr.kv A x ∗ srvRestRp E γr A r0 ∗
      ∃ (A' : List EntryModel) (u : Bool), srvRLogLb γr.raft A' ∗
        ⌜SnapImageFacts γr d D cl i A A'
          (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A')).mem⌝ ∗
        mvcc.api.mvccImage D (kvModel γr.kv A') (crevOf γr.kv A') u ∗ E.Cp (crevOf γr.kv A') := by
  have hpre0 : γr.raft.pre = [] := by rw [hraft]
  have hai0 : γr.raft.ai0 = W64 0 := by rw [hraft]
  have hrr : γr.raft.raft = γ := by rw [hraft]
  iintro #Hinvs #Himg Hka Hrest #Hrc
  iunfold srvKVInvs at Hinvs
  icases Hinvs with ⟨#HkI, -, #HrI, -, %Hcm, -⟩
  ihave #Hdb0 := (dbImage_of_srvImage (γ := γ) (γk := γr.kv) (i := i) (D := D) hc0 hch hlog0)
    $$ Himg
  ihave #Hdb : dbImage γr.raft γr.kv i D $$ []
  · rw [hraft]; iexact Hdb0
  iunfold dbImage at Hdb
  icases Hdb with ⟨%A', %u, #HA', %hA', #Him⟩
  obtain ⟨hlen', himA, hst⟩ := hA'
  unfold imageRestAt at himA
  obtain ⟨hci, htm, hrestL⟩ := himA
  -- (R4, 2026-11-07, `lean`'s) the leased image: its `lease` bucket the log's live leases' records,
  -- its other buckets the plain image's (`bkRestAtL_other`)
  have hrest := bkRestAtL_other hrestL
  iunfold kvApplied at Hka
  icases Hka with ⟨Hal, %Hch'⟩
  iunfold kvAppliedL at Hal
  icases Hal with ⟨#HA, Hhi, #Hc, %Hl⟩
  ihave %Hcmp := srvRLogLb_prefix γr.raft A A' $$ [HA HA']
  · iframe HA HA'
  have hz : uint.Z (W64 0) = 0 := rfl
  rw [hai0, hz] at hai hlen'
  have hAA' : A <+: A' := by
    rcases Hcmp with h | h
    · exact h
    · have := h.length_le; omega
  imod kv_log_ccOk γr.raft γr.kv A' $$ HkI HrI HA' with %Hcc
  -- (sweep repairs 1, S4) the committed log's cluster requests
  imod kv_log_verOk γr.raft γr.kv A' $$ HkI HrI HA' with %Hver
  imod kv_log_plain γr.raft γr.kv A' $$ HkI HrI HA' with %Hpl0
  have Hpl : plainLogM γr.kv.cmp γr.kv.lm A' := Hpl0.1
  have hnl : mvcc.LogNoLease (kvModel γr.kv A') := by
    have hl0 : mvcc.LogNoLease γr.kv.log0 := by
      rw [hlog0]; intro cs hcs c hc; simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hcs
      rcases hcs with rfl | rfl <;> simp at hc
    unfold kvModel; exact (kvRaftOf_restorable _ _ _ A' Hpl hl0).1
  -- the compaction revision's permit
  imod crevOf_permit γr.raft γr.kv A' $$ HkI HrI HA' with Hp
  imod crevOf_offM γr.raft γr.kv A' $$ HkI HrI HA' with %Hoff
  -- the cluster's in-memory members, from the rest resource (S2–S4 Probe: in either lease mode,
  -- `srvRest_open`; the records leave the members, `restLeasesWith_mem`)
  ihave ⟨%f, %Hf, Hrest, HL, HG, #HRq, HU⟩ := srvRestRp_open E γr A r0 $$ Hrest
  rw [hRO]
  iunfold srvRestOwnH at Hrest
  icases Hrest with ⟨Hro, HH⟩
  iunfold srvRestOwn at Hro
  icases Hro with ⟨Hrb, Hrn, Hmem, %Hmi⟩
  rw [apply.restLeasesWith_mem]
  ihave #HA'' : srvRLogLb γr.raft (γr.raft.pre ++ A') $$ []
  · rw [hpre0, List.nil_append]; iexact HA'
  have hLL : γr.raft.pre ++ A <+: γr.raft.pre ++ A' := (List.prefix_append_right_inj _).2 hAA'
  have hbl : γr.raft.raft.boot.length ≤ (γr.raft.pre ++ A').length := by
    rw [hpre0, hrr, List.nil_append]; omega
  have hcc' : ∀ m ∈ γr.raft.pre ++ A', m.typ ≠ W32 0 → ccWideOk γr.raft.raft.cfg m.data := by
    rw [hpre0, List.nil_append]
    intro m hm ht
    exact ccPolOk_wide _ _ (Hcc m hm ht)
  -- (route B) the entries within the boot log's length the boot policy's
  ihave %hbcc' := srv_bootPrefix_ccBoot γr.raft (γr.raft.pre ++ A') $$ [HrI HA'']
  · iframe HrI HA''
  ihave Hax := membership.clusterImageOk_restModel.wp_proof cl γr.raft γr.kv.c0
    (γr.raft.pre ++ A) (γr.raft.pre ++ A') hpre0 hc0 hLL hbl hcc' hbcc'
    (by rw [hpre0, List.nil_append]; exact Hver) _ hids $$ Hrc HA'' Hmem
  icases Hax with ⟨Hmem, %Himg⟩
  imodintro
  isplitl [Hhi]
  · iunfold kvApplied
    iunfold kvAppliedL
    iframe HA Hhi Hc
    ipureintro; exact ⟨Hl, Hch'⟩
  isplitl [Hrb Hrn Hmem HH HL HG HU]
  · iapply srvRestRp_close
    iexists f
    iframe HL HG HRq HU
    isplitr
    · ipureintro; exact Hf
    rw [hRO]
    iunfold srvRestOwnH
    iframe HH
    iunfold srvRestOwn
    iframe Hrb Hrn
    rw [apply.restLeasesWith_mem]
    iframe Hmem
    ipureintro; rw [← apply.restLeasesWith_mem f (srvIds E (appliedTable γr A).ids)]; exact Hmi
  iexists A', u
  iframe HA' Him
  isplitr
  · ipureintro
    have hb := image_bootBucketsNL d hrest
    exact {
      pre := hAA'
      len := by omega
      hst := hst
      nolease := hnl
      hmetaI := by obtain ⟨t, ht⟩ := htm; exact ⟨t, hci, ht⟩
      hlease := imageLeasesAt_of_bkRestAtL d hrestL
      halarm := hb.1
      hauthb := hb.2
      hmemb := image_membBucketsNL d hrest
      himg := clusterImageOk_of_NL d cl _ hrest Himg
      hA' := ⟨restModel_bk_of_NL d hrest, rfl⟩ }
  rw [Hcm.2.2.2]
  iunfold kvCpOk
  iframe Hp
  ipureintro; exact Hoff

/-- **`snapRecv_imageOn` inside the window** (R2d'a task 4): at an image `r0` with the model's ids. -/
theorem snapRecv_imageOnR (γ : SrvRaft) (γr : ReadNames) (E : apply.AEnv GF) (i ai : w64)
    (D : backend.Data) (d : mvcc.KBReal) (A : List EntryModel) (x : apply.ApplyKV) (cl : Loc)
    (H : IProp GF) (sa : auth.AuthState) (_hkb : E.BkTie = srvBkTie d)
    (hraft : γr.raft = ⟨γ, [], W64 0⟩) (hc0 : γr.kv.c0 = W64 0)
    (hch : γr.kv.ch0 = apply.alarmChain true false false) (hlog0 : γr.kv.log0 = [[], []])
    (hai : uint.Z ai = uint.Z γr.raft.ai0 + A.length) (hi : uint.Z ai < uint.Z i)
    (hboot : (γ.boot.length : Int) ≤ uint.Z i)
    (hRO : E.RO = srvRestOwnH E.authMode d.γB cl H)
    (r0 : apply.RestM)
    (hids : ∀ k, (r0.mem !! k).isSome =
      ((restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)).mem !! k).isSome) :
    ⊢ srvKVInvsOn E γr srvAuthSt0 -∗ srvImageOn γ i D -∗
      kvAppliedOn γr.raft γr.kv srvAuthSt0 A x sa (kvLeasesOn γr.kv srvAuthSt0 A) -∗ srvRestRpM true E γr A r0 -∗
      membership.isRaftCluster cl ={⊤}=∗
      kvAppliedOn γr.raft γr.kv srvAuthSt0 A x sa (kvLeasesOn γr.kv srvAuthSt0 A) ∗ srvRestRpM true E γr A r0 ∗
      ∃ (A' : List EntryModel) (u : Bool), srvRLogLb γr.raft A' ∗
        ⌜SnapImageFactsOn γr d D cl i A A'
          (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A')).mem⌝ ∗
        mvcc.api.mvccImage D (kvModelOn γr.kv srvAuthSt0 A') (crevOf γr.kv A') u ∗
        E.Cp (crevOf γr.kv A') := by
  have hpre0 : γr.raft.pre = [] := by rw [hraft]
  have hai0 : γr.raft.ai0 = W64 0 := by rw [hraft]
  have hrr : γr.raft.raft = γ := by rw [hraft]
  have hz : uint.Z (W64 0) = 0 := rfl
  iintro #Hinvs #Himg Hka Hrest #Hrc
  ihave ⟨%f0, %Hf0, Hrest, HrL, HrG, HrQ, HrE⟩ := srvRestRpM_open true E γr A r0 $$ Hrest
  iunfold srvKVInvsOn at Hinvs
  icases Hinvs with ⟨#HkI, #HcI, #HrI, -, -, %Hw, %Hrows0, %Hrows1, -⟩
  have Hrows := And.intro Hrows0 Hrows1
  -- the certificate's KV names agree with the member's on the start values
  iunfold srvImageOn at Himg
  icases Himg with ⟨⟨%γk', %hk', #Hdb⟩, -⟩
  obtain ⟨h0', h1', h2'⟩ := hk'
  have hR : ∀ B, kvRaftOfOn γk'.c0 γk'.ch0 (srvAuthSt0, γk'.log0, []) B =
      kvRaftOfOn γr.kv.c0 γr.kv.ch0 (srvAuthSt0, γr.kv.log0, []) B := by
    intro B; rw [h0', h1', h2', hc0, hch, hlog0]
  have hk : ∀ B, kvModelOn γk' srvAuthSt0 B = kvModelOn γr.kv srvAuthSt0 B := by
    intro B; unfold kvModelOn; rw [hR]
  have hsa : ∀ B, srvAuthAtLog γk' srvAuthSt0 B = srvAuthAtLog γr.kv srvAuthSt0 B := by
    intro B; unfold srvAuthAtLog; rw [hR]
  have hcr : ∀ B, crevOf γk' B = crevOf γr.kv B := by
    intro B; simp only [crevOf, h0', h1', hc0, hch]
  iunfold dbImageOn at Hdb
  icases Hdb with ⟨%A', %u, #HA'0, %hA', #Him0⟩
  ihave #HA' : srvRLogLb γr.raft A' $$ []
  · rw [hraft]; iexact HA'0
  obtain ⟨hlen', himA, hst⟩ := hA'
  simp only at hlen'
  rw [hz] at hlen'
  rw [hk, hcr] at hst
  iunfold kvAppliedOn at Hka
  icases Hka with ⟨Hal, %Hch'⟩
  iunfold kvAppliedLOn at Hal
  icases Hal with ⟨#HA, Hhi, #Hc, %Hl⟩
  ihave %Hcmp := srvRLogLb_prefix γr.raft A A' $$ [HA HA']
  · iframe HA HA'
  rw [hai0, hz] at hai
  have hAA' : A <+: A' := by
    rcases Hcmp with h | h
    · exact h
    · have := h.length_le; omega
  imod kv_log_ccOkOn γr.raft γr.kv srvAuthSt0 A' $$ HkI HrI HA' with %Hcc
  -- (sweep repairs 1, S4) the committed log's cluster requests
  imod kv_log_verOkOn γr.raft γr.kv srvAuthSt0 A' $$ HkI HrI HA' with %Hver
  imod kv_log_plainOn γr.raft γr.kv srvAuthSt0 A' $$ HkI HrI HA' with %Hpl
  -- the cluster's in-memory members, from the rest resource
  rw [hRO]
  iunfold srvRestOwnH at Hrest
  icases Hrest with ⟨Hro, HH⟩
  iunfold srvRestOwn at Hro
  icases Hro with ⟨Hrb, Hrn, Hmem, %Hmi⟩
  ihave #HA'' : srvRLogLb γr.raft (γr.raft.pre ++ A') $$ []
  · rw [hpre0, List.nil_append]; iexact HA'
  have hLL : γr.raft.pre ++ A <+: γr.raft.pre ++ A' := (List.prefix_append_right_inj _).2 hAA'
  have hbl : γr.raft.raft.boot.length ≤ (γr.raft.pre ++ A').length := by
    rw [hpre0, hrr, List.nil_append]; omega
  have hcc' : ∀ m ∈ γr.raft.pre ++ A', m.typ ≠ W32 0 → ccWideOk γr.raft.raft.cfg m.data := by
    rw [hpre0, List.nil_append]
    intro m hm ht
    exact ccPolOk_wide _ _ (Hcc m hm ht)
  -- (route B) the entries within the boot log's length the boot policy's
  ihave %hbcc' := srv_bootPrefix_ccBoot γr.raft (γr.raft.pre ++ A') $$ [HrI HA'']
  · iframe HrI HA''
  ihave Hax := membership.clusterImageOk_restModel.wp_proof cl γr.raft γr.kv.c0
    (γr.raft.pre ++ A) (γr.raft.pre ++ A') hpre0 hc0 hLL hbl hcc' hbcc'
    (by rw [hpre0, List.nil_append]; exact Hver) _ (fun k => by rw [apply.restLeasesWith_mem]; exact hids k)
    $$ Hrc HA'' Hmem
  icases Hax with ⟨Hmem, %Himg⟩
  -- the image's clauses at the member's names
  obtain ⟨hci, htm, hrest, hauth⟩ := himA
  rw [hsa] at hauth
  have hrest' : bkRestAtNAL (appliedTableM true γr A') γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A') D := by
    obtain ⟨f, hf, hb⟩ := hrest
    simp only [List.nil_append] at hf hb
    have hT : kvLeasesOn γk' srvAuthSt0 A' = appliedTableM true γr A' := by
      rw [appliedTableM_true, hpre0]; unfold kvLeasesOn; simp only [List.nil_append]; rw [hR]
    rw [hT] at hf hb
    refine ⟨f, hf, fun n hn hna => ?_⟩
    rw [hb n hn hna, hpre0, hrr, hc0, h0', List.nil_append]
  have hcrev : crevOf γr.kv A' = -1 := crevOf_plainOn γr.kv A' Hpl
  -- (auth-lease S3a, Draft rev 5 §5) the image's leased keys' leases are live in the mode's table
  have hl0 : mvcc.LogNoLease ([[], []] : mvcc.Log) := by
    intro cs hcs c hc; simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hcs
    rcases hcs with rfl | rfl <;> simp at hc
  have hlive : keysLeasesLive (kvRaftOfOn γr.kv.c0 γr.kv.ch0 (srvAuthSt0, γr.kv.log0, []) A') := by
    rw [hlog0]; exact keysLeasesLive_kvRaftOfOn _ _ _ _ A' hl0
  imodintro
  isplitl [Hhi]
  · iunfold kvAppliedOn
    iunfold kvAppliedLOn
    iframe HA Hhi Hc
    ipureintro; exact ⟨Hl, Hch'⟩
  isplitl [Hrb Hrn Hmem HH HrL HrG HrQ HrE]
  · iapply srvRestRpM_close
    iexists f0
    iframe HrL HrG HrQ HrE
    isplitr
    · ipureintro; exact Hf0
    rw [hRO]
    iunfold srvRestOwnH
    iframe HH
    iunfold srvRestOwn
    iframe Hrb Hrn Hmem
    ipureintro; exact Hmi
  iexists A', u
  iframe HA'
  have hfacts : SnapImageFactsOn γr d D cl i A A'
      (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A')).mem := {
    pre := hAA'
    len := by omega
    hst := hst
    nolease := fun k id hk => by
      rw [appliedTableM_eq_model γr A' hpre0]
      exact hlive k id hk
    hmetaI := by obtain ⟨t, ht⟩ := htm; exact ⟨t, hci, ht⟩
    hlease := imageLeasesAtT_of_NAL d hrest'
    halarm := image_alarmNAL d hrest'
    hauthI := authBucketsAt_rbData d D _ hauth
    hmemb := image_membBucketsNAL d hrest'
    himg := clusterImageOk_of_NAL d cl _ hrest' Himg
    hA' := ⟨restModel_bk_of_NAL d hrest', rfl⟩ }
  isplitr
  · ipureintro; exact hfacts
  isplitr
  · rw [← hk, ← hcr]; iexact Him0
  -- the compaction revision's permit: `-1`
  rw [Hw.2, hcrev]
  iunfold kvCpOk
  isplitl
  · ileft; ipureintro; rfl
  ipureintro; intro _; rfl

end recvR

section snapDir
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- (restart S6a, 2026-11-13) **The disk snapshot's directory, from the snapshot path's bundle**: the
bundle's storage over its snapshotter, the member's directory invariant at the removal counter
`γm` (`snapRmM`). -/
theorem srvSnapDir_of_RO (s ci : Loc) (E : apply.AEnv GF) (γr : ReadNames) (γm : GName) :
    srvSnapRO (GF := GF) s ci E γr γm ⊢ srvSnapDir s γm := by
  iintro #Hro
  iunfold srvSnapRO at Hro
  icases Hro with ⟨%cfg, %ss, %hk, %lgh, %stp, %γd, %idm, %al, %ast, %lp, %cl, %ps, %dir, %d, %Hp,
    #HL, #Hzl, #HD, #HF, #HFg, #Hvo, #HQ, #HW, #HSs, #HSi, #HH, #HHi, #HSt, #HM, #Hinv,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hsws⟩
  iunfold srvSnapDir
  iexists stp, ss, config.snapDirOf cfg.DataDir', γd, srvImageM γr.raft.raft.authOn γr.raft.raft, snapRmM γm
  iframe HSt HSi Hinv Hsws
  iintro !> %j #Hj
  iunfold snapRmM
  iexact Hj

end snapDir

end EtcdGrove
end Perennial
