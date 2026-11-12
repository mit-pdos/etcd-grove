/-
Proof of `applyAll`'s snapshot case, `EtcdServer.applyAll.specSnapM`
(`Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__applyAll.lean`), in both auth modes and in
restart form. Lean-first (no Rocq counterpart).

(R2d'a swap batch 2, 2026-11-06; review F1, the swap the user approved) Until the swap this file held
the mode-off proof `wp_proofSnap` of `applyAll.specSnap`, `ApplyAllSnapOn.lean` the mode-generic
`wp_proofSnapM` over it, and `ApplyAllSnapR.lean` the restart form `specSnapMR` with its proof. The
restart form is now `specSnapM` and its proof `wp_proofSnapM` (generated from the two frozen proofs,
with the directory's file taken at the ghost index `g` (`snapDir_take`), the image's facts at `g` and
`r0` (`snapRecv_imageR`/`snapRecv_imageOnR`, below), `applySnapshot.specSnapM` at Go's `ai` and `r0`,
and the ghost index's jump from `g` (`applied_jump(M)`)); the two frozen proofs are deleted.
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
    kvAppliedOn (GF := GF) γr.raft γr.kv srvAuthSt0 A x sa ⊢
      kvAppliedOn γr.raft γr.kv srvAuthSt0 A x sa ∗ ⌜sa = srvAuthAtLog γr.kv srvAuthSt0 A⌝ := by
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
      rw [hlog0]; intro cs hcs c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hcs
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
  have hcc' : ∀ m ∈ γr.raft.pre ++ A', m.typ ≠ W32 0 → ccBootOk γr.raft.raft.cfg m.data := by
    rw [hpre0, List.nil_append]
    intro m hm ht
    exact ccPolOk_static _ _ (Hcc m hm ht)
  ihave Hax := membership.clusterImageOk_restModel.wp_proof cl γr.raft γr.kv.c0
    (γr.raft.pre ++ A) (γr.raft.pre ++ A') hpre0 hc0 hLL hbl hcc'
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
    (hRO : E.RO = srvRestOwnH E.authMode d.γB cl H) (hlg : E.lg = false)
    (r0 : apply.RestM)
    (hids : ∀ k, (r0.mem !! k).isSome =
      ((restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)).mem !! k).isSome) :
    ⊢ srvKVInvsOn E γr srvAuthSt0 -∗ srvImageOn γ i D -∗
      kvAppliedOn γr.raft γr.kv srvAuthSt0 A x sa -∗ srvRestRp E γr A r0 -∗
      membership.isRaftCluster cl ={⊤}=∗
      kvAppliedOn γr.raft γr.kv srvAuthSt0 A x sa ∗ srvRestRp E γr A r0 ∗
      ∃ (A' : List EntryModel) (u : Bool), srvRLogLb γr.raft A' ∗
        ⌜SnapImageFactsOn γr d D cl i A A'
          (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A')).mem⌝ ∗
        mvcc.api.mvccImage D (kvModelOn γr.kv srvAuthSt0 A') (crevOf γr.kv A') u ∗
        E.Cp (crevOf γr.kv A') := by
  have hpre0 : γr.raft.pre = [] := by rw [hraft]
  have hai0 : γr.raft.ai0 = W64 0 := by rw [hraft]
  have hrr : γr.raft.raft = γ := by rw [hraft]
  have hz : uint.Z (W64 0) = 0 := rfl
  rw [srvRestRp_false E γr A r0 hlg]
  iintro #Hinvs #Himg Hka Hrest #Hrc
  iunfold srvKVInvsOn at Hinvs
  icases Hinvs with ⟨#HkI, #HcI, #HrI, -, -, %Hw, -⟩
  -- the certificate's KV names agree with the member's on the start values
  iunfold srvImageOn at Himg
  icases Himg with ⟨%γk', %hk', #Hdb⟩
  obtain ⟨h0', h1', h2'⟩ := hk'
  have hR : ∀ B, kvRaftOfOn γk'.c0 γk'.ch0 (srvAuthSt0, γk'.log0) B =
      kvRaftOfOn γr.kv.c0 γr.kv.ch0 (srvAuthSt0, γr.kv.log0) B := by
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
  have hcc' : ∀ m ∈ γr.raft.pre ++ A', m.typ ≠ W32 0 → ccBootOk γr.raft.raft.cfg m.data := by
    rw [hpre0, List.nil_append]
    intro m hm ht
    exact ccPolOk_static _ _ (Hcc m hm ht)
  ihave Hax := membership.clusterImageOk_restModel.wp_proof cl γr.raft γr.kv.c0
    (γr.raft.pre ++ A) (γr.raft.pre ++ A') hpre0 hc0 hLL hbl hcc'
    (by rw [hpre0, List.nil_append]; exact Hver) _ hids $$ Hrc HA'' Hmem
  icases Hax with ⟨Hmem, %Himg⟩
  -- the image's clauses at the member's names
  obtain ⟨hci, htm, hrest, hauth⟩ := himA
  rw [hsa] at hauth
  have hrest' : bkRestAtNA γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A') D := by
    intro n hn hna
    rw [hrest n hn hna, hpre0, hrr, hc0, h0']
  have hcrev : crevOf γr.kv A' = -1 := crevOf_plainOn γr.kv A' Hpl
  have hnl : mvcc.LogNoLease (kvModelOn γr.kv srvAuthSt0 A') := by
    have hl0 : mvcc.LogNoLease ([[], []] : mvcc.Log) := by
      intro cs hcs c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hcs
      rcases hcs with rfl | rfl <;> simp at hc
    unfold kvModelOn; rw [hlog0]
    exact (kvRaftOfOn_restorable _ _ (srvAuthSt0, [[], []]) A' Hpl hl0).1
  imodintro
  isplitl [Hhi]
  · iunfold kvAppliedOn
    iunfold kvAppliedLOn
    iframe HA Hhi Hc
    ipureintro; exact ⟨Hl, Hch'⟩
  isplitl [Hrb Hrn Hmem HH]
  · iunfold srvRestOwnH
    iframe HH
    iunfold srvRestOwn
    iframe Hrb Hrn Hmem
    ipureintro; exact Hmi
  iexists A', u
  iframe HA'
  have hTnil : (appliedTable γr A').ids = [] := by
    unfold appliedTable kvLeases; rw [hpre0, List.nil_append, kvTableOf_plainOn _ _ A' Hpl]; rfl
  have hfacts : SnapImageFactsOn γr d D cl i A A'
      (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A')).mem := {
    pre := hAA'
    len := by omega
    hst := hst
    nolease := hnl
    hmetaI := by obtain ⟨t, ht⟩ := htm; exact ⟨t, hci, ht⟩
    hlease := imageLeasesAt_of_nil hTnil (image_leaseAlarmNA d hrest').1
    halarm := (image_leaseAlarmNA d hrest').2
    hauthI := authBucketsAt_rbData d D _ hauth
    hmemb := image_membBucketsNA d hrest'
    himg := clusterImageOk_of_bkRestAtNA d cl _ hrest' Himg
    hA' := ⟨restModel_bk_of_bkRestAtNA d hrest', rfl⟩ }
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

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`applyAll.specSnapM`** (F9; P6.3; R2d'a task 4 and swap batch 2, 2026-11-06): both auth
modes, at the split index (until the swap two proofs, `wp_proofSnap` off and `wp_proofSnapM` on,
over the first-start statement). -/
theorem EtcdServer.applyAll.wp_proofSnapM
    (hASnap : EtcdServer.applySnapshot.specSnapM (GF := GF) (hG := hG))
    (hAE : EtcdServer.applyEntries.specNil (GF := GF) (hG := hG))
    (hBk : EtcdServer.Backend.spec (GF := GF) (hG := hG))
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hV : backend.VerifyBackendConsistency.spec (GF := GF) (hG := hG))
    (hSINC : EtcdServer.snapshotIfNeededAndCompactRaftLog.specNoop (GF := GF) (hG := hG))
    -- the merge branch, as `wp_proofOn`'s
    (hGT : raftpb.Message.GetTerm.spec (GF := GF) (hG := hG))
    (hGS : raftpb.Message.GetSnapshot.spec (GF := GF) (hG := hG))
    (hGM : raftpb.Snapshot.GetMetadata.spec (GF := GF) (hG := hG))
    (hGI : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG))
    (hCM : EtcdServer.createMergedSnapshotMessage.spec (GF := GF) (hG := hG))
    (hSMS : EtcdServer.sendMergedSnap.spec (GF := GF) (hG := hG))
    [mvccSem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hPers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hReach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (hImg : mvcc.api.mvccImage_snapshot.law (GF := GF) (hG := hG))
    (hSnap : backend.backend.Snapshot.spec (GF := GF) (hG := hG))
    (hOn : storage.BackendHooks.OnPreCommitUnsafe.spec (GF := GF) (hG := hG))
    (hSave : consistentIndex.UnsafeSave.spec (GF := GF) (hG := hG))
    (hPut : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (hUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG)) :
    EtcdServer.applyAll.specSnapM (GF := GF) (hG := hG) := by
  intro s γ ci TM E ρ γr b ep ap es sn sv rac nc st ai at0 a t cs x A mst γs γp γnc w nid nk q γn rt n
    sa ag r0 hany hag hgi hi61 hboot hAL hcia hids hraft hc0 hch hlog0 hγn hnI
  have hai : uint.Z ai < uint.Z sv.Metadata'.Index' := by omega
  cases hM : E.authMode with
  | any => exact absurd hM hany
  | off =>
    have hon : E.authOn = false := by simp [apply.AEnv.authOn, hM]
    have hoffE : E.authMode = .off := hM
    rw [hon] at hch ⊢
    simp only [srvApplyKVM_false, kvAppliedM_false, isServerM_false]
    wp_start as ⟨#Hsrv, #Hsa, #Hnid, #Hes, #Hesl, #Hsnf, Hsnv, ⟨#Hcert, #Hsloc⟩, #Hncf, #Hnc2, Hnr0,
      #Hracf, #Hracc, #Hrtf, #Hrt, Hai, Hat, Hcs, Hss, Hst, Hbe, Happ, Hlr, Hgr, Hrdk, Hbr, HKV, Hao, #Hlog,
      #HW, HWA, Hka, HRS, HAR, #Hkv, HwalT, Hso, #HmetaSnap⟩
    ihave #Hsrv' := Hsrv
    iunfold isServer at Hsrv'
    icases Hsrv' with ⟨%Hρrd, -, ⟨%fv, #Hfl⟩, #Hatm, -, #HrnS, -⟩
    iunfold srvFieldsAt at Hfl
    icases Hfl with ⟨#Hlgf, #Hlgnn, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hmid, -⟩
    ihave Hinit : (srvInit : IProp GF) $$ []
    · iapply isPkgInit_access $$ Hpkg
    icases Hinit with ⟨-, -, ⟨%g, #Hg, #Hgs⟩, ⟨%bsl, #Hbsl⟩, -⟩
    ihave #Pbe : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
    · iPkgInit
    ihave #Hatm' := Hatm
    iunfold srvAtomics at Hatm'
    icases Hatm' with ⟨#Hainv, -, #Hkvi⟩
    ihave #Hkvi2 := Hkvi
    iunfold srvKVInvs at Hkvi2
    icases Hkvi2 with ⟨#HkI0, -, #Hrli, -, %Hkvp, -⟩
    obtain ⟨-, -, ⟨hw1, hw2, hw3, hw4⟩, -⟩ := Hkvp
    -- (the auth-on pair's F8) the cluster runs auth off, the member's KV invariant says
    imod (kvInv_authOn γr.raft γr.kv) $$ HkI0 with %hao
    -- the snapshot path's resources: the bundle, the counter, the backend's own
    iunfold srvSnapOwn at Hso
    icases Hso with ⟨%γt, %nt, #Hro, %Hnt, Hγt, Hsres⟩
    ihave #Hro' := Hro
    iunfold srvSnapRO at Hro'
    icases Hro' with ⟨%cfg, %ss, %hk, %lgh, %stp, %γd, %idm, %al, %ast, %lp, %cl, %ps, %dir, %d,
      %Hp, #Hcflg, #Hcfzl, #Hcfdd, #Hcffg, #Hfg, #Hvoff, #Hcfq, #Hcfw, #Hssf, #Hssi, #Hhkf, #Hhk, #Hstp, #Hidm,
      #Hdinv, #Half, #Hauf, #Hlpf, #Hclf, #Hal, #HalOk, #HauOk, #HauR, #HauSK, #HlpOk, #HlpCfg, #HlpL, #Hrc,
      #HclOk, #Hvc, #Hmd, #Hks, #HlpI, #HlpM, ⟨#Hkvaddr, #Hkvm⟩, #Hcfg, #Hclgz⟩
    obtain ⟨hkb, hstp, hdbo, hmm, hbuq, hsl, hdirps, hsop, hbr, hci, hhk, hwf, hlim, hlp,
      halbi, hRO, hrb⟩ := Hp
    -- (the lease-expiry plan's S2–S4 Probe, 2026-11-05: in either lease mode; until then the
    -- revocable lessor refuted the rest's leased arm, a cluster that grants none) the lessor at the
    -- environment's mode
    icases HlpM with ⟨%Hmo, #HlpE⟩
    icombine Hnid Hidm gives %Hidn
    subst Hidn
    -- the snapshot saved in the member's directory (`nodeSnapLocal` at the cluster's directories,
    -- the members')
    ihave #Hcok := Hrli
    iunfold srvRaftLogInv at Hcok
    icases Hcok with ⟨-, #Hcok, -⟩
    iunfold srvClusterOk at Hcok
    icases Hcok with ⟨-, -, -, -, -, -, -, %Hsloc'⟩
    ihave #Hsaved : snapSaved γd sv.Metadata'.Index' $$ []
    · iunfold snapSaved
      letI := srvStor (GF := GF) γr.raft.raft
      iapply (nodeSnapLocal_elem γr.raft.raft.cl nid γd (by rw [Hsloc'.1]; exact hsl))
      iexact Hsloc
    -- the snapshot's file out of the directory, the counter raised to its index (`snapDir_take`)
    have hnt' : nt < uint.nat sv.Metadata'.Index' := by
      have : uint.nat ai < uint.nat sv.Metadata'.Index' := by word
      omega
    wp_auto_lc 1
    ihave #Hdinv' : inv snapDirN (snapDirInv ss γd (srvImage γr.raft.raft) (srvSnapRm γt γr)) $$ []
    · rw [← srvImageM_off, ← hao]; iexact Hdinv
    imod snapDir_take ss γd γt γr (srvImage γr.raft.raft) sv.Metadata'.Index' ag nt hnt' hgi
      $$ Hlc1 Hdinv' Hsaved Hγt Hao with ⟨Hγt, Hao, %D, Hfile, #Himg⟩
    -- the image's facts (`snapRecv_image`): its committed log `A'` extending `A`
    have hai0 : uint.Z ag = uint.Z γr.raft.ai0 + A.length := by
      rw [hraft]; have := hAL; word
    imod snapRecv_imageR γr.raft.raft γr E sv.Metadata'.Index' ag D d A x cl _ hraft hc0 hch hlog0
        hai0 hgi hboot hRO r0 hids $$ Hkvi Himg Hka HRS Hrc
      with ⟨Hka, HRS, %A', %u, #HA', %Hif, #Him0, #HCp0⟩
    icases kvApplied_facts γr.raft γr.kv A x $$ Hka with ⟨Hka, %HxA⟩
    -- the auth mode off (the run's), the KV's ghost state jumps to the image's log
    imod authOn_false_of_off s γ ci TM E ρ γr ρ.wait x A $$ [$Hsrv $HKV $Hka] with ⟨%Hoff, HKV, Hka⟩
    have hoff := authMode_off_of E Hoff
    imod snapRecv_kv_jump E γr A A' x Hif.pre (by have := Hif.hst.2; omega) $$ Hkvi Hka HA'
      with ⟨%Hxch, HkaL⟩
    obtain ⟨tI, hmeta⟩ := Hif.hmetaI
    -- the backend's own resources
    iunfold srvSnapRes at Hsres
    icases Hsres with ⟨%d0, %al0, %dd, %Hkb0, Hstopc, Hbo, #Hal0, #Hdd, Hpath, -⟩
    obtain rfl := srvBkTie_inj d d0 (hkb.symm.trans Hkb0)
    icombine Half Hal0 gives %Hale
    subst Hale
    icombine Hcfdd Hdd gives %Hdde
    subst Hdde
    -- the apply thread's membership resources: the transport, the members' directory
    iunfold srvApRes at HAR
    icases HAR with ⟨%bh, %ix, %lgh', %tl, %lid, %cl', %lgc, %cid, %prs, #Hbhf, #Hbh, #Htrf, #Hmidf,
      #Hclf', #Hlgcf, #Hlgcnn, #Hcidf, Hmr, %Hpc, #Hdl⟩
    icombine Hclf Hclf' gives %Hcle
    subst Hcle
    icombine Hidm Hmidf gives %Hlide
    subst Hlide
    iunfold ccMembRes at Hmr
    icases Hmr with ⟨#Hrc', %γN, %c, %ps', %Hcl, Htlive, #Hmd', %Hdk⟩
    -- the snapshot state's indices
    iunfold srvSnapState at Hss
    icases Hss with ⟨%sd0, %sm0, %sf0, Hsd0, Hsm0, Hsf0, %Hdm0, #Hmst, #Hslb0⟩
    -- the configuration, rebuilt over `isServerApplyAll`'s two fields
    ihave #Hsa' := Hsa
    iunfold isServerApplyAll at Hsa'
    icases Hsa' with ⟨%wt, %msc, %sc, #Hwtf, #Hwt, #Hmscf, ⟨%γm, %Hγm, #Hmidm, #Hmscb⟩, #Hscf,
      ⟨%stg, #Hstgf, #Hstgc⟩, ⟨%scu, #Hscuf⟩, #Hinf, -,
      ⟨%tr, %γNt, %lidt, %SN, %TSN, #Htrf2, #Htr, %HγNt⟩, %Hkv0⟩
    ihave #Hcfg' := Hcfg $$ %sc %scu Hscf Hscuf
    -- `s.applySnapshot(ep, apply)`, (2026-11-02, the backend-auth-split stage) with the apply
    -- thread's token (`srvGoRes`'s)
    iunfold srvGoRes at Hgr
    icases Hgr with ⟨HgrW, HthT⟩
    -- (F9, 2026-11-03) `specSnapM` in the mode `off`: the auth store's `Recover` facts `authRecoverOk`
    ihave #HauS : snapAuthResM E.authMode s ast E.RD γr A' $$ []
    · rw [hoff]; simp only [snapAuthResM]; iapply HauR; ipureintro; first | trivial | rfl | exact hoff
    have hS := (hASnap s ep ap sn sv γ ci TM E ρ γr ai at0 sd0 nc
        { cfg with SnapshotCount' := sc, SnapshotCatchUpEntries' := scu } ss hk hai d D lgh hkb
        hdbo hsop ⟨hwf, hlim, hci, hhk⟩ hmm tI hmeta st b (by omega)
        al ast lp cl x A r0 hRO A' u (by rw [Hoff]; exact HxA) (by rw [Hoff]; exact Hif.hst)
        (by rw [Hoff]; exact Hif.nolease) hbr hlp γp
        hrb stp γd γt
        (srvImage γr.raft.raft) (uint.nat sv.Metadata'.Index') hstp (Nat.le_refl _) Hif.halarm halbi
        Hif.hmemb _ Hif.himg γN tl c prs γN.dir ps' _ rfl Hdk.1 Hdk.2.1 Hcl sm0 cs
        cfg.ServerFeatureGate' cfg.QuotaBackendBytes' cfg.WarningApplyDuration' hbuq
        Hif.pre (by rw [Hoff]; exact Hif.hA') Hif.hlease
        (by rw [hraft]) Hmo (by rw [hoff]; simp) (by rw [hoff]; exact Hif.hauthb) γnc)
    rw [Hoff] at hS
    simp only [srvApplyKVM_false, isServerM_false, srvSnapAppliedM, kvModelM_false] at hS
    -- (sweep repairs 1, W2) the payload at the storage's WAL (`rnWalTokA_loc`)
    icases rnWalTokA_loc γn (srvRAddr s) q _ $$ HwalT Hstp with ⟨HwalT, %Hwl⟩
    ihave #Hnc2' : isNotify2 γnc nc (walBaseLb (storage.walOf (interface.mkOk (go.GoType.PointerType
        go_etcd_io.etcd.server.v3.storage.storage.ty) #stp)) (uint.nat sv.Metadata'.Index'))
        iprop(True) $$ []
    · rw [← Hwl]; iexact Hnc2
    wp_apply hS
      $$ [Hsnv Hnr0 Hai Hat Hsd0 Hlr Hbr Hfile Hpath Hst Hbe HKV HRS Hγt Htlive Hsm0 Hcs Hstopc
        Hbo HthT]
      as ⟨Hsapp, Hnr1, HthT⟩
    · iframe #; iframe
    (try wp_auto)
    ihave Hgr : srvGoRes s $$ [HgrW HthT]
    · iunfold srvGoRes; iframe HgrW HthT
    iunfold srvSnapApplied at Hsapp
    icases Hsapp with ⟨%γ', %TM', %E', %b', %st', %d', %x', %cs', %L, %Hsa1, #Hsrv1, Hai, Hat, Hsd,
      Hsm, Hcs, #Hcso, Hst, Hbe, Hlr, Hbr, HKV, HRS, Hstopc, Hbo, Hγt, Hpath, #Hbf', Htlive,
      ⟨%kv', #Hkvf', #Hkvi', %Hkve⟩⟩
    obtain ⟨hbs, hkb', hP', hRO', hlo', hci', hxl, hxcr, hxch, hL⟩ := Hsa1
    -- the apply thread's reader token, at the new environment's store (`beSucc` keeps it)
    ihave Hrdk : mvcc.api.mvccReaders (GF := GF) E'.γ 1 $$ [Hrdk]
    · iapply (show mvcc.api.mvccReaders (GF := GF) E.γ 1 ⊢ mvcc.api.mvccReaders E'.γ 1 by
        obtain ⟨-, _, _, _, _, _, _, hE⟩ := hbs; rw [hE]; exact .rfl)
      iexact Hrdk
    have hoff' : E'.authMode = auth.AuthMode.off := by
      obtain ⟨-, _, _, _, _, _, _, hE⟩ := hbs; rw [hE]; exact hoff
    -- `s.applyEntries(ep, apply)`: no entries
    wp_apply hAE s ep ap es $$ []
    · iframe #
    (try wp_auto)
    -- `backend.VerifyBackendConsistency(s.Backend(), s.Logger(), true, schema.AllBuckets...)`
    wp_apply hBk s E.γbe $$ [Hbr] as %be ⟨Hbr, %dB, -, #HbRO⟩
    · iframe #; iframe Hbr
    -- (sweep repairs 1, B4) `ETCD_VERIFY` off, the backend's
    ihave #Hvoff := srvBeRO_envVerifyOff dB $$ HbRO
    wp_apply hLg s fv.lg $$ [Hlr] as ⟨-, Hlr⟩
    · iframe #; iframe Hlr
    (try wp_auto)
    wp_apply hV be fv.lg true bsl $$ []
    · iframe #
    (try wp_auto)
    -- `proposalsApplied.Set(float64(ep.appliedi))`
    iunfold gaugeSetSpec at Hgs
    wp_apply Hgs
    (try wp_auto)
    -- `s.applyWait.Trigger(ep.appliedi)`: the applied index jumps to the snapshot's (`applied_jump`)
    ihave #Hsrv1' := Hsrv1
    iunfold isServer at Hsrv1'
    icases Hsrv1' with ⟨-, -, -, #Hatm1, -, -⟩
    iunfold srvAtomics at Hatm1
    icases Hatm1 with ⟨#Hainv1, -, #Hkvi1⟩
    imod srvApplyKV_writer hPers hReach s E' γr ρ.wait x' $$ Hkvi1 HKV with ⟨HKV, #Hic, -, -, -⟩
    have hiL : uint.Z sv.Metadata'.Index' = uint.Z γr.raft.ai0 + A'.length := by
      rw [hraft]; have := Hif.len; word
    ihave #HkL : kvLogAt γr sv.Metadata'.Index' x'.log $$ []
    · iunfold kvLogAt; iexists A'; iframe HA'; ipureintro; exact ⟨hiL, hxl⟩
    imod applied_jump s E' γr ag sv.Metadata'.Index' x.log x'.log hgi
        (by rw [hxl, HxA.1]; exact kvRaftOf_prefix _ _ _ _ _ Hif.pre)
      $$ Hainv1 Hao Hlog HkL Hic with ⟨Hao, #Hlb, #Hlog1⟩
    iunfold isWaitTime at Hwt
    icases Hwt with ⟨%wi, %Hwi, -, #HTrig⟩
    subst Hwi
    wp_apply HTrig $$ []
    · iintro !>; iexact Hlb
    (try wp_auto)
    -- `<-apply.notifyc`: the payload's second receive
    wp_apply wp_notify2_receive2 γnc nc _ _ $$ [Hnr1] as ⟨Hnr2, -⟩
    · iframe Hnc2 Hnr1
    (try wp_auto)
    -- the post's facts: the KV at the image's log, the voters, the log's last term, the membership
    -- resource at `A'`, the snapshot path's resources at the new backend
    ihave Hka : kvApplied γr.raft γr.kv A' x' $$ [HkaL]
    · iapply kvApplied_of_jump γr.raft γr.kv A' x' hxl
        (by rw [hxch, Hoff, hch]) hxcr $$ HkaL
    have hpos : 0 < uint.Z sv.Metadata'.Index' := by have := hai; word
    have hρr : ρ.raft = γr.raft := by rw [← Hρrd]
    ihave #Hdl' := Hdl
    iunfold srvDynLog at Hdl'
    icases Hdl' with %Hlid
    imod epCsVoters_of_snap γr.raft sv cs' nid hpos hi61 Hlid $$ Hrli Hcert Hcso with #Hcv
    ihave #Hecs : epCsAt ρ.raft A' cs' $$ []
    · iunfold epCsAt; iright; rw [hρr]; iexact Hcv
    ihave %hltA := lastTermIs_of_snap γr.raft sv A' hpos hi61 (by rw [hraft]) Hif.len $$ Hrli Hcert HA'
    have hlenP : (γr.raft.pre ++ A').length = uint.nat sv.Metadata'.Index' := by
      rw [hraft]; simp only [List.nil_append]
      have := Hif.len; have := uint_nat_eq sv.Metadata'.Index'; omega
    ihave #Hkvi3 := Hkvi
    iunfold srvKVInvs at Hkvi3
    icases Hkvi3 with ⟨#Hkinv, -⟩
    imod kv_log_ccOk γr.raft γr.kv A' $$ Hkinv Hrli HA' with %Hcc
    have hmo : srvMemOk γr.raft γr.kv.c0 A' := by
      obtain ⟨B, hB⟩ := Hif.pre
      rw [← hB]
      exact srvMemOk_append _ _ A B Hpc.2
        (fun e he => Hcc e (by rw [← hB]; exact List.mem_append_right _ he))
    have hcov : srvPeersCover γr.raft nid A' L := fun f hf hne =>
      hL f ((netRh_member γN f).2 (Hdk.2.2 f hf)) hne
    ihave HAR' : srvApRes s γr A' $$ [Htlive]
    · iunfold srvApRes
      iexists bh, ix, lgh', tl, nid, cl, lgc, cid, L
      iframe Hbhf Hbh Htrf Hmidf Hclf' Hlgcf Hcidf Hdl
      isplitr
      · iexact Hlgcnn
      isplitl [Htlive]
      · iunfold ccMembRes
        iframe Hrc'
        iexists γN, c, ps'
        iframe Htlive Hmd'
        ipureintro; exact ⟨Hcl, Hdk⟩
      ipureintro; exact ⟨hcov, hmo⟩
    ihave #Hro1 := srvSnapRO_succ s ci γr γt d d' al ast lp cl hbs hkb hkb' hP'
      hRO' $$ [Hro Half Hauf Hlpf Hclf]
    · iframe Hro Half Hauf Hlpf Hclf
    ihave Hbo : backend.bOpen (GF := GF) d'.γB (srvOpenQ E'.authMode) $$ [Hbo]
    · rw [hoff', srvOpenQ_off]; iexact Hbo
    -- MERGE-TODO(close): `lean`'s `srvSnapRes` also held the KV's closer (`HKC`)
    ihave Hso' : srvSnapOwn s ci E' γr γ' sv.Metadata'.Index' $$ [Hγt Hstopc Hbo Hpath]
    · iunfold srvSnapOwn
      iexists γt, uint.nat sv.Metadata'.Index'
      iframe Hro1 Hγt
      isplitr
      · ipureintro; exact Nat.le_refl _
      iunfold srvSnapRes
      iexists d', al, cfg.DataDir'
      iframe Hstopc Hbo Half Hcfdd Hpath
      isplitr
      · ipureintro; exact hkb'
      iexact Hbf'
    iunfold epConfState at Hcs
    icases Hcs with ⟨Hcs, #Hcsok⟩
    -- the step's end, shared by the selects' branches: the apply thread at a state `stF` of the
    -- same consistent index
    ihave Hfin : iprop(∀ stF : ApplyState, ⌜loopOk γ' stF sv.Metadata'.Index' ∧
          ciEff γ' stF.k = sv.Metadata'.Index'⌝ -∗
        epAppliedIAddr ep ↦ sv.Metadata'.Index' -∗ epAppliedTAddr ep ↦ sv.Metadata'.Term' -∗
        epConfStateAddr ep ↦ cs' -∗ srvSnapState s ep mst γs sv.Metadata'.Index' (W64 0) -∗
        applyThread γ' stF -∗ applyBackend γ' ci b' -∗ ciApplying ci a t -∗ srvLgReader s -∗
        srvGoRes s -∗ mvcc.api.mvccReaders E'.γ 1 -∗ srvApplyKV s E' ρ.wait x' -∗
        kvApplied γr.raft γr.kv A' x' -∗
        srvRest E' γr A' -∗ Φ #()) $$ [HΦ Hbr HAR' Hao HWA HwalT Hso']
    · iintro %stF %HF Hai Hat Hcs Hss Hst Hbe Happ Hlr Hgr Hrdk HKV Hka HRS
      ihave Hcs : epConfState ep cs' $$ [Hcs]
      · iunfold epConfState; iframe Hcs Hcsok
      iapply HΦ
      iexists γ', TM', E', b', stF, A', cs'
      isplitr
      · ipureintro; exact hbs
      iframe Hsrv1 HAR' HA' Hai Hat Hcs Hecs Hss Hst Hbe Happ Hlr Hgr Hrdk Hbr Hao Hlb HWA HwalT Hso'
      isplitl [HKV Hka HRS]
      · iexists x'; iframe HKV Hlog1 Hka HRS
      isplitr
      · iexists kv'; iframe Hkvf' Hkvi'; ipureintro; exact Hkve
      ipureintro; exact ⟨HF.1, HF.2, Hif.pre, hlenP, hltA⟩
    -- `select { case <-apply.raftAdvancedC: case <-s.stopping: return }`
    iunfold rnAdvChan at Hracc
    icases Hracc with ⟨%γac, #Hracc⟩
    ihave #HstgS := Hstgc
    iunfold stopChan at Hstgc
    icases Hstgc with ⟨%γsg, #Hstgc⟩
    wp_apply_core chan.wp_select_blocking_nil
    iapply BigAndL.bigAndL_cons.2
    isplit
    rotate_left
    · iapply BigAndL.bigAndL_cons.2
      isplit
      · ileft
        simp only [chan.blockingClausePre]
        iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, stg, γsg
        isplitr
        · ipureintro; rfl
        isplitr
        · iapply ownStopChan_is_chan $$ Hstgc
        iapply stop_chan_receive _ _ _ _ _ $$ Hstgc
        iintro ⟨-, -⟩
        (try wp_auto)
        ihave Hss : srvSnapState s ep mst γs sv.Metadata'.Index' (W64 0) $$ [Hsd Hsm Hsf0]
        · iunfold srvSnapState; iexists _, _, _; iframe Hsd Hsm Hsf0 Hmst Hslb0
          ipureintro; constructor <;> word
        have hF : loopOk γ' st' sv.Metadata'.Index' ∧ ciEff γ' st'.k = sv.Metadata'.Index' :=
          ⟨hlo', hci'⟩
        iapply Hfin $$ %st' %hF Hai Hat Hcs Hss Hst Hbe Happ Hlr Hgr Hrdk HKV Hka HRS
      iapply BigAndL.bigAndL_nil.2
      itrivial
    ileft
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, rac, γac
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ownStopChan_is_chan $$ Hracc
    iapply stop_chan_receive _ _ _ _ _ $$ Hracc
    iintro ⟨-, -⟩
    (try wp_auto)
    -- `s.snapshotIfNeededAndCompactRaftLog(ep)`: nothing to do at the snapshot's index
    ihave Hfs : srvFS s $$ [Hsf0]
    · iunfold srvFS; iexists _; iexact Hsf0
    wp_apply hSINC s γr ep sv.Metadata'.Index' (by word) $$ [Hfs Hai Hsd Hsm]
      as ⟨Hfs, Hai, Hsd, Hsm⟩
    · iframe #; iframe
    (try wp_auto)
    iunfold srvFS at Hfs
    icases Hfs with ⟨%sf1, Hsf1⟩
    ihave Hss : srvSnapState s ep mst γs sv.Metadata'.Index' (W64 0) $$ [Hsd Hsm Hsf1]
    · iunfold srvSnapState; iexists _, _, _; iframe Hsd Hsm Hsf1 Hmst Hslb0
      ipureintro; constructor <;> word
    -- `select { case m := <-s.r.msgSnapC: ...; default: }`, as `wp_proof`'s at the snapshot's index
    have hF : loopOk γ' st' sv.Metadata'.Index' ∧ ciEff γ' st'.k = sv.Metadata'.Index' := ⟨hlo', hci'⟩
    have hlenZ : uint.Z sv.Metadata'.Index' = (A'.length : Int) := Hif.len
    iunfold isRNMsgSnapC at Hmscb
    icases Hmscb with ⟨%γc, #Hmscb⟩
    ihave #Hmscch := is_bag_is_chan γc msc _ $$ Hmscb
    ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
    · iPkgInit
    wp_apply_core chan.wp_select_nonblocking
    isplit
    · iapply BigAndL.bigAndL_cons.2
      isplit
      · simp only [chan.nonblockingClausePre]
        iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, msc, γc
        isplitr
        · ipureintro; rfl
        isplitr
        · iexact Hmscch
        unfold nonblockingRecvAu
        isplit
        · iapply chanBag_nbRecv γc msc _ _ $$ Hmscb
          iintro %m HP
          iunfold rnSnapMsg at HP
          icases HP with ⟨%sm, Hm, %Htyb, #Hsm, -, #Huf⟩
          obtain ⟨Hty, -⟩ := Htyb
          rw [Hγm]
          letI := srvStor (GF := GF) γr.raft.raft
          ihave %Hsh := sentMsg_shape _ _ _ _ $$ Hsm
          obtain ⟨sn, hsn, -⟩ := Hsh.2 Hty
          ihave %Hsnp := srv_sentSnap_pos γr γm.id sm sn Hty hsn $$ [Hrli Hsm]
          · iframe Hrli Hsm
          -- two Go steps' time receipts (`m`'s zero value, `GetTerm`'s method value), for the merge
          -- window's write tokens
          repeat (
            fail_if_success wp_bind (App (Val (GoInstruction _)) (Val _))
            wp_pure)
          wp_bind (App (Val (GoInstruction _)) (Val _))
          iapply wp_go_step_receipt'
          case hv => first | rfl | simp [val.isPanic]
          inext
          iintro Hr1 Hl1
          iapply wp_value'
          repeat (
            fail_if_success wp_bind (App (Val (GoInstruction (MethodResolve _ _))) (Val _))
            first | wp_pure | wp_load | wp_store | wp_alloc_auto)
          wp_bind (App (Val (GoInstruction (MethodResolve _ _))) (Val _))
          iapply wp_go_step_receipt'
          case hv => first | rfl | simp [val.isPanic]
          inext
          iintro Hr2 Hl2
          iapply wp_value'
          (try wp_auto)
          wp_apply (hGT.1 m (DFrac.own 1) DFrac.discard false sm) $$ [Hm] as Hm
          · iframe #; iframe Hm
          (try wp_auto)
          wp_if_destruct
          · -- the batch's term: the snapshot's index
            wp_apply (hGS.1 m (DFrac.own 1) DFrac.discard false sm) $$ [Hm] as %ps ⟨Hsn, Hmb⟩
            · iframe #; iframe Hm
            rw [hsn]
            iunfold snapOpt at Hsn
            wp_apply (hGM.1 ps (DFrac.own 1) sn) $$ [Hsn] as %pm ⟨Hmd, Hsnb⟩
            · iframe #; iframe Hsn
            wp_apply (hGI pm (DFrac.own 1) sn.Metadata') $$ [Hmd] as Hmd
            · iframe #; iframe Hmd
            ihave Hsn := Hsnb $$ Hmd
            ihave Hm := Hmb $$ [Hsn]
            · iunfold snapOpt; iexact Hsn
            (try wp_auto)
            wp_if_destruct
            · -- the merge: the snapshot at most the applied index (the guard)
              (try wp_auto)
              -- (S2's `mergedCreate_window`) the commit's and the snapshot's contracts
              ihave #HsrvM : isServerM false s γ' ci TM' E' ρ γr $$ []
              · rw [isServerM_false]; iexact Hsrv1
              ihave #HW' : srvWTPool E' γp $$ []
              · obtain ⟨-, p, P, f, cc, RO, RW, hE⟩ := hbs
                rw [hE]
                iunfold srvWTPool at HW
                unfold srvWTPool
                rw [show (E.onBe p P f cc RO RW).γbe = E.γbe from rfl]
                iexact HW
              icases srvApplyKV_core s E' ρ.wait x' $$ HKV with ⟨%ua, HKVc, HKVk⟩
              -- the apply goroutine's token, lent to the commit
              ihave HthT : apply.applyTok (GF := GF) E' $$ [Hrdk]
              · iunfold apply.applyTok; iexact Hrdk
              imod mergedCreate_window hsh hPers hReach hImg hSnap hOn hSave hPut hUR hID hName hSafe false s
                  γ' ci TM' E' ρ γr b' st' sv.Metadata'.Index' a t A' x' ρ.wait γp ua kv' hlo' hci'
                  (fun _ => False) (fun _ => True) emp (fun _ h => h.elim)
                $$ [Hst Hbe Happ HKVc HRS Hr1 Hl1 HthT]
                with ⟨%be, %dq, %RC, %RC', %RS, %RS', %Qd, Hkc, HRC, Hbeo, Hbs, HRCS, Hback⟩
              · iframe Hpkg HsrvM Hkvf' Hkvi' HW' Hr1 Hl1 HthT Hst Hbe Happ HKVc HRS
                iapply bkLendW_none
              -- (2026-11-06, `notes/begin-tok-plan.md`) the apply thread's token (`srvGoRes`'s) pays for
              -- the snapshot's reader slot; the reader goroutine's fork token comes back
              iunfold srvGoRes at Hgr
              icases Hgr with ⟨HgrW, HgT⟩
              wp_apply (hCM s m sm sv.Metadata'.Term' sv.Metadata'.Index' cs' fv.lg kv' be dq RC RC'
                  RS RS' Qd γr.raft hmo.2.1
                (by have h := Hsh.1.2.2.2.2.2.2.1 (Or.inr (Or.inr Hty)); exact ⟨h.1, h.2, Hsh.1.2.2.2.2.2.2.2⟩))
                $$ [Hlr Hkc HRC Hbeo Hbs HRCS Hm HgT]
                as %mg ⟨Hlr, HRS', Hbeo, HgT, %rc, %Dm, %cm, #Hmg, #Hml, #HszC, #Hcsom, %Hcml, Hrs, HQd⟩
              · iframe #; iframe Hlr Hkc HRC Hbeo Hbs HRCS Hm HgT
              ihave Hgr : srvGoRes s $$ [HgrW HgT]
              · iunfold srvGoRes; iframe HgrW HgT
              imod Hback $$ %Dm HRS' HQd Hbeo
                with ⟨%st3, HthT, Hst, Hbe, Happ, HKVc, HRS, #Hmimg, -, %Hst3⟩
              ihave HKV := HKVk $$ HKVc
              iunfold apply.applyTok at HthT
              irename HthT => Hrdk
              -- the merged message sent: of a term committed through the applied index (the batch's
              -- term, `rnRtOk`; not `0`, a `MsgSnap`'s term), certified at the voters' conf state
              iunfold rnRtOk at Hrt
              rw [hγn]
              icases Hrt with (%Hrt0 | ⟨%ct, #Hct, %Hnct⟩)
              · exfalso
                exact (Hsh.1.2.2.2.1 (by rw [Hty]; simp [MsgSnap, MsgProp, MsgReadIndex,
                  MsgTransferLeader])) Hrt0
              ihave #Hcv2 := Hcv
              iunfold epCsVoters at Hcv2
              icases Hcv2 with ⟨%c0, #Hc0, %Hcs0⟩
              ihave %Hcc := csOpt_agree cs' cm c0 $$ [Hcsom Hc0]
              · iframe Hcsom Hc0
              subst Hcc
              imod srv_merged_sent γr A' sv.Metadata'.Index' sv.Metadata'.Term' cm γm.id ct sm sn hpos
                  hi61 (by have := hmo.2.1; omega) hlenZ hltA Hcs0 Hty hsn (by word)
                  (by have := hnI; have := uint_nat_eq sv.Metadata'.Index'; omega)
                $$ [Hrli HA' Hsm Hct] with #Hsm'
              · iframe Hrli HA' Hsm Hct
              -- (S2's `merged_image`) the image's certificate
              imod merged_image s γ' ci TM' E' ρ γr sv.Metadata'.Index' A' x' Dm hoff' hlenZ ⟨hc0, hlog0⟩
                $$ [Hka] with ⟨Hka, #Himg'⟩
              · iframe Hsrv1 Hka Hmimg
              imod srvMerged_bundle γr.raft.raft m rc sm γm.id cm sv.Metadata'.Index'
                  sv.Metadata'.Term' Dm Hty
                $$ [Hml HszC Hsm' Hrs Himg'] with Hbun
              · iframe Hml HszC Hsm' Hrs Himg'
              (try wp_auto)
              wp_apply (hSMS s mg m rc fv.lg fv.memberID stg tr γNt SN TSN lidt) $$ [Hgr Hlr Hbun]
                as ⟨Hgr, Hlr⟩
              · iframe #; iframe Hgr Hlr; rw [HγNt]; iframe Hbun
              (try wp_auto)
              have hF3 : loopOk γ' st3 sv.Metadata'.Index' ∧ ciEff γ' st3.k = sv.Metadata'.Index' :=
                ⟨Hst3.2.1, by rw [Hst3.2.2]; exact hci'⟩
              iapply Hfin $$ %st3 %hF3 Hai Hat Hcs Hss Hst Hbe Happ Hlr Hgr Hrdk HKV Hka HRS
            · (try wp_auto)
              iapply Hfin $$ %st' %hF Hai Hat Hcs Hss Hst Hbe Happ Hlr Hgr Hrdk HKV Hka HRS
          · (try wp_auto)
            iapply Hfin $$ %st' %hF Hai Hat Hcs Hss Hst Hbe Happ Hlr Hgr Hrdk HKV Hka HRS
        · itrivial
      iapply BigAndL.bigAndL_nil.2
      itrivial
    · -- `default`
      (try wp_auto)
      iapply Hfin $$ %st' %hF Hai Hat Hcs Hss Hst Hbe Happ Hlr Hgr Hrdk HKV Hka HRS
  | on γa =>
  have hon : E.authOn = true := by simp [apply.AEnv.authOn, hM, auth.AuthMode.isOn]
  rw [hon] at hch ⊢
  simp only [srvApplyKVM_true, kvAppliedM_true]
  wp_start as ⟨#Hsrv, #Hsa, #Hnid, #Hes, #Hesl, #Hsnf, Hsnv, ⟨#Hcert, #Hsloc⟩, #Hncf, #Hnc2, Hnr0,
    #Hracf, #Hracc, #Hrtf, #Hrt, Hai, Hat, Hcs, Hss, Hst, Hbe, Happ, Hlr, Hgr, Hrdk, Hbr, HKV, Hao, #Hlog,
    #HW, HWA, Hka, HRS, HAR, #Hkv, HwalT, Hso, #HmetaSnap⟩
  ihave #Hsrv' := Hsrv
  iunfold isServerM at Hsrv'
  icases Hsrv' with ⟨%Hρrd, -, ⟨%fv, #Hfl⟩, #Hatm, -, #HrnS, -⟩
  iunfold srvFieldsAtM at Hfl
  icases Hfl with ⟨#Hlgf, #Hlgnn, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hmid, -⟩
  ihave Hinit : (srvInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, -, ⟨%g, #Hg, #Hgs⟩, ⟨%bsl, #Hbsl⟩, -⟩
  ihave #Pbe : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
  ihave #Hatm' := Hatm
  iunfold srvAtomicsM at Hatm'
  icases Hatm' with ⟨#Hainv, -, #HkiM⟩
  ihave #Hkvi := srvKVInvsM_true s E γr $$ HkiM
  ihave #Hkvi2 := Hkvi
  iunfold srvKVInvsOn at Hkvi2
  icases Hkvi2 with ⟨#HkI0, -, #Hrli, -, -, %Hkvp, -, %Hcmlg⟩
  obtain ⟨⟨hw1, hw2, hw3, hw4⟩, -⟩ := Hkvp
  have Hcmf := Hcmlg.1
  -- (the lease-expiry plan's S2–S4, 2026-11-05: until then the spec's premise) auth on, the
  -- cluster grants none (`srvKVInvsOn`'s)
  have hlgk : γr.kv.lg = false := Hcmlg.2
  -- the cluster runs auth on, the member's KV invariant says
  imod (kvInvOn_authOn γr.raft γr.kv srvAuthSt0) $$ HkI0 with %hao
  -- the applied auth state is the applied log's
  icases kvAppliedOn_sa γr A x sa $$ Hka with ⟨Hka, %hsa⟩
  subst hsa
  -- the snapshot path's resources: the bundle, the counter, the backend's own
  iunfold srvSnapOwn at Hso
  icases Hso with ⟨%γt, %nt, #Hro, %Hnt, Hγt, Hsres⟩
  ihave #Hro' := Hro
  iunfold srvSnapRO at Hro'
  icases Hro' with ⟨%cfg, %ss, %hk, %lgh, %stp, %γd, %idm, %al, %ast, %lp, %cl, %ps, %dir, %d,
    %Hp, #Hcflg, #Hcfzl, #Hcfdd, #Hcffg, #Hfg, #Hvoff, #Hcfq, #Hcfw, #Hssf, #Hssi, #Hhkf, #Hhk, #Hstp, #Hidm,
    #Hdinv, #Half, #Hauf, #Hlpf, #Hclf, #Hal, #HalOk, #HauOk, #HauR, #HauSK, #HlpOk, #HlpCfg, #HlpL, #Hrc,
    #HclOk, #Hvc, #Hmd, #Hks, #HlpI, #HlpM, ⟨#Hkvaddr, #Hkvm⟩, #Hcfg, #Hclgz⟩
  obtain ⟨hkb, hstp, hdbo, hmm, hbuq, hsl, hdirps, hsop, hbr, hci, hhk, hwf, hlim, hlp,
    halbi, hRO, hrb⟩ := Hp
  -- (the lease-grant stage, 2.9) the lessor revocable refutes the rest's leased arm
  -- (the lease-expiry plan's X2) the mode of a cluster that grants none: `none`
  icases HlpM with ⟨%Hmo, #HlpM⟩
  have hEm : E.lm = .none := by
    have h := hlgk; rw [KVNames.lg_eq, ← Hmo] at h; simpa using h
  ihave #HlpM : lease.lessorModeIs (mvcc.api.mvccLeases E.γ) (decide (lease.Mode.none = .mono)) $$ []
  · iExactEq HlpM <;> rw [hEm]
  ihave #Hlrev : lease.lessorModeIs (mvcc.api.mvccLeases E.γ) false $$ []
  · iExactEq HlpM <;> rfl
  -- (R2d'a task 4) the cluster grants none: the rest is its image's `E.RO` (`srvRestRp_false`)
  have HElg : E.lg = false := by
    have h : E.lg = decide (lease.Mode.none ≠ .none) := by rw [apply.AEnv.lg_eq, hEm]
    simpa using h
  ihave #HlpE : lease.lessorModeIs (mvcc.api.mvccLeases E.γ) (decide (E.lm = .mono)) $$ []
  · rw [hEm]; iexact HlpM
  icombine Hnid Hidm gives %Hidn
  subst Hidn
  -- the snapshot saved in the member's directory
  ihave #Hcok := Hrli
  iunfold srvRaftLogInv at Hcok
  icases Hcok with ⟨-, #Hcok, -⟩
  iunfold srvClusterOk at Hcok
  icases Hcok with ⟨-, -, -, -, -, -, -, %Hsloc'⟩
  ihave #Hsaved : snapSaved γd sv.Metadata'.Index' $$ []
  · iunfold snapSaved
    letI := srvStor (GF := GF) γr.raft.raft
    iapply (nodeSnapLocal_elem γr.raft.raft.cl nid γd (by rw [Hsloc'.1]; exact hsl))
    iexact Hsloc
  -- the snapshot's file out of the directory, the counter raised to its index (`snapDir_take`), its
  -- image certified in the mode `on` (`srvImageOn`)
  have hnt' : nt < uint.nat sv.Metadata'.Index' := by
    have : uint.nat ai < uint.nat sv.Metadata'.Index' := by word
    omega
  wp_auto_lc 1
  ihave #Hdinv' : inv snapDirN (snapDirInv ss γd (srvImageOn γr.raft.raft) (srvSnapRm γt γr)) $$ []
  · rw [← srvImageM_on, ← hao]; iexact Hdinv
  imod snapDir_take ss γd γt γr (srvImageOn γr.raft.raft) sv.Metadata'.Index' ag nt hnt' hgi
    $$ Hlc1 Hdinv' Hsaved Hγt Hao with ⟨Hγt, Hao, %D, Hfile, #Himg⟩
  -- the image's facts (`snapRecv_imageOn`): its committed log `A'` extending `A`
  have hai0 : uint.Z ag = uint.Z γr.raft.ai0 + A.length := by
    rw [hraft]; have := hAL; word
  imod snapRecv_imageOnR γr.raft.raft γr E sv.Metadata'.Index' ag D d A x cl _ _ hkb hraft hc0 hch
      hlog0 hai0 hgi hboot hRO HElg r0 hids $$ Hkvi Himg Hka HRS Hrc
    with ⟨Hka, HRS, %A', %u, #HA', %Hif, #Him0, #HCp0⟩
  -- the applied log's model and compaction revision (`-1`, a mode-on log compacts nothing; the
  -- apply thread's too, `srvApplyKVOn_crev`)
  iunfold kvAppliedOn at Hka
  icases Hka with ⟨HkaL0, %Hch0⟩
  iunfold kvAppliedLOn at HkaL0
  icases HkaL0 with ⟨#HA0, Hhi0, #Hc0, %He0⟩
  ihave Hka : kvAppliedOn γr.raft γr.kv srvAuthSt0 A x (srvAuthAtLog γr.kv srvAuthSt0 A) $$ [Hhi0]
  · iunfold kvAppliedOn; iunfold kvAppliedLOn; iframe HA0 Hhi0 Hc0
    ipureintro; exact ⟨He0, Hch0⟩
  imod kv_log_plainOn γr.raft γr.kv srvAuthSt0 A $$ HkI0 Hrli HA0 with %HplA
  imod srvApplyKVOn_crev s E γr srvAuthSt0 ρ.wait x _ $$ Hkvi HKV with ⟨HKV, %Hxc⟩
  have HxA : x.log = kvModelOn γr.kv srvAuthSt0 A ∧ x.crev = crevOf γr.kv A := by
    refine ⟨?_, by rw [Hxc, crevOf_plainOn γr.kv A HplA]⟩
    unfold kvModelOn; rw [← He0]
  -- the KV's ghost state jumps to the image's log
  imod snapRecv_kv_jumpOn E γr A A' x _ Hif.pre (by have := Hif.hst.2; omega) $$ Hkvi Hka HA'
    with ⟨%Hxch, HkaL⟩
  obtain ⟨tI, hmeta⟩ := Hif.hmetaI
  -- the auth store's `Recover` facts at the image's log
  ihave #HauS : snapAuthResM E.authMode s ast E.RD γr A' $$ []
  · iapply snapAuthResM_on s ast E γr A' γa hM; iframe Hauf HauSK
  -- the backend's own resources
  iunfold srvSnapRes at Hsres
  icases Hsres with ⟨%d0, %al0, %dd, %Hkb0, Hstopc, Hbo, #Hal0, #Hdd, Hpath, -⟩
  obtain rfl := srvBkTie_inj d d0 (hkb.symm.trans Hkb0)
  icombine Half Hal0 gives %Hale
  subst Hale
  icombine Hcfdd Hdd gives %Hdde
  subst Hdde
  -- the apply thread's membership resources: the transport, the members' directory
  iunfold srvApRes at HAR
  icases HAR with ⟨%bh, %ix, %lgh', %tl, %lid, %cl', %lgc, %cid, %prs, #Hbhf, #Hbh, #Htrf, #Hmidf,
    #Hclf', #Hlgcf, #Hlgcnn, #Hcidf, Hmr, %Hpc, #Hdl⟩
  icombine Hclf Hclf' gives %Hcle
  subst Hcle
  icombine Hidm Hmidf gives %Hlide
  subst Hlide
  iunfold ccMembRes at Hmr
  icases Hmr with ⟨#Hrc', %γN, %c, %ps', %Hcl, Htlive, #Hmd', %Hdk⟩
  -- the snapshot state's indices
  iunfold srvSnapState at Hss
  icases Hss with ⟨%sd0, %sm0, %sf0, Hsd0, Hsm0, Hsf0, %Hdm0, #Hmst, #Hslb0⟩
  -- the configuration, rebuilt over `isServerApplyAll`'s two fields
  ihave #Hsa' := Hsa
  iunfold isServerApplyAll at Hsa'
  icases Hsa' with ⟨%wt, %msc, %sc, #Hwtf, #Hwt, #Hmscf, ⟨%γm, %Hγm, #Hmidm, #Hmscb⟩, #Hscf,
    ⟨%stg, #Hstgf, #Hstgc⟩, ⟨%scu, #Hscuf⟩, #Hinf, -,
    ⟨%tr, %γNt, %lidt, %SN, %TSN, #Htrf2, #Htr, %HγNt⟩, %Hkv0⟩
  ihave #Hcfg' := Hcfg $$ %sc %scu Hscf Hscuf
  -- `s.applySnapshot(ep, apply)`, in the mode `on`
  iunfold srvGoRes at Hgr
  icases Hgr with ⟨HgrW, HthT⟩
  have hS := hASnap s ep ap sn sv γ ci TM E ρ γr ai at0 sd0 nc
      { cfg with SnapshotCount' := sc, SnapshotCatchUpEntries' := scu } ss hk hai d D lgh hkb
      hdbo hsop ⟨hwf, hlim, hci, hhk⟩ hmm tI hmeta st b (by omega)
      al ast lp cl x A r0 hRO A' u (by rw [hon]; exact HxA) (by rw [hon]; exact Hif.hst)
      (by rw [hon]; exact Hif.nolease) hbr hlp γp hrb stp γd γt
      (srvImageOn γr.raft.raft) (uint.nat sv.Metadata'.Index') hstp (Nat.le_refl _) Hif.halarm
      halbi Hif.hmemb _ Hif.himg γN tl c prs γN.dir ps' _ rfl Hdk.1 Hdk.2.1 Hcl sm0 cs
      cfg.ServerFeatureGate' cfg.QuotaBackendBytes' cfg.WarningApplyDuration' hbuq
      Hif.pre (by rw [hon]; exact Hif.hA') Hif.hlease (by rw [hraft]) Hmo hany
      (by rw [hM]; exact ⟨⟨halbi.2.1, halbi.2.2.1, halbi.2.2.2⟩, Hif.hauthI,
        by have := Hif.len; omega⟩)
      γnc
  rw [hon] at hS
  simp only [srvApplyKVM_true, kvModelM_true] at hS
  -- (sweep repairs 1, W2) the payload at the storage's WAL (`rnWalTokA_loc`)
  icases rnWalTokA_loc γn (srvRAddr s) q _ $$ HwalT Hstp with ⟨HwalT, %Hwl⟩
  ihave #Hnc2' : isNotify2 γnc nc (walBaseLb (storage.walOf (interface.mkOk (go.GoType.PointerType
      go_etcd_io.etcd.server.v3.storage.storage.ty) #stp)) (uint.nat sv.Metadata'.Index'))
      iprop(True) $$ []
  · rw [← Hwl]; iexact Hnc2
  wp_apply hS
    $$ [Hsnv Hnr0 Hai Hat Hsd0 Hlr Hbr Hfile Hpath Hst Hbe HKV HRS Hγt Htlive Hsm0 Hcs Hstopc
      Hbo HthT]
    as ⟨Hsapp, Hnr1, HthT⟩
  · iframe #; iframe
  (try wp_auto)
  ihave Hgr : srvGoRes s $$ [HgrW HthT]
  · iunfold srvGoRes; iframe HgrW HthT
  iunfold srvSnapAppliedM at Hsapp
  iunfold srvSnapAppliedOn at Hsapp
  iunfold srvSnapAppliedG at Hsapp
  icases Hsapp with ⟨%γ', %TM', %E', %b', %st', %d', %x', %cs', %L, %Hsa1, #Hsrv1, Hai, Hat, Hsd,
    Hsm, Hcs, #Hcso, Hst, Hbe, Hlr, Hbr, HKV, HRS, Hstopc, Hbo, Hγt, Hpath, #Hbf', Htlive,
    ⟨%kv', #Hkvf', #Hkvi', %Hkve⟩⟩
  obtain ⟨hbs, hkb', hP', hRO', hlo', hci', hxl, hxcr, hxch, hL⟩ := Hsa1
  -- the apply thread's reader token, at the new environment's store (`beSucc` keeps it)
  ihave Hrdk : mvcc.api.mvccReaders (GF := GF) E'.γ 1 $$ [Hrdk]
  · iapply (show mvcc.api.mvccReaders (GF := GF) E.γ 1 ⊢ mvcc.api.mvccReaders E'.γ 1 by
      obtain ⟨-, _, _, _, _, _, _, hE⟩ := hbs; rw [hE]; exact .rfl)
    iexact Hrdk
  have hM' : E'.authMode = auth.AuthMode.on γa := by
    obtain ⟨-, _, _, _, _, _, _, hE⟩ := hbs; rw [hE]; exact hM
  ihave HKV : srvApplyKVOn s E' ρ.wait x' (srvAuthAtLog γr.kv srvAuthSt0 A') $$ [HKV]
  · rw [← srvApplyKVM_true]; iexact HKV
  -- `s.applyEntries(ep, apply)`: no entries
  wp_apply hAE s ep ap es $$ []
  · iframe #
  (try wp_auto)
  -- `backend.VerifyBackendConsistency(s.Backend(), s.Logger(), true, schema.AllBuckets...)`
  wp_apply hBk s E.γbe $$ [Hbr] as %be ⟨Hbr, %dB, -, #HbRO⟩
  · iframe #; iframe Hbr
  -- (sweep repairs 1, B4) `ETCD_VERIFY` off, the backend's
  ihave #Hvoff := srvBeRO_envVerifyOff dB $$ HbRO
  wp_apply hLg s fv.lg $$ [Hlr] as ⟨-, Hlr⟩
  · iframe #; iframe Hlr
  (try wp_auto)
  wp_apply hV be fv.lg true bsl $$ []
  · iframe #
  (try wp_auto)
  -- `proposalsApplied.Set(float64(ep.appliedi))`
  iunfold gaugeSetSpec at Hgs
  wp_apply Hgs
  (try wp_auto)
  -- `s.applyWait.Trigger(ep.appliedi)`: the applied index jumps to the snapshot's, the auth state
  -- after the image's log published (`applied_jumpM`)
  ihave #Hsrv1' := Hsrv1
  iunfold isServerM at Hsrv1'
  icases Hsrv1' with ⟨-, -, -, #Hatm1, -, -⟩
  iunfold srvAtomicsM at Hatm1
  icases Hatm1 with ⟨#Hainv1, -, #HkiM1⟩
  ihave #Hkvi1 := srvKVInvsM_true s E' γr $$ HkiM1
  imod srvApplyKVOn_writer hPers hReach s E' γr srvAuthSt0 ρ.wait x' _ $$ Hkvi1 HKV
    with ⟨HKV, #Hic, -, -, -⟩
  have hiL : uint.Z sv.Metadata'.Index' = uint.Z γr.raft.ai0 + A'.length := by
    rw [hraft]; have := Hif.len; word
  have hxm : x'.log = kvModelOn γr.kv srvAuthSt0 A' := by rw [hxl]; rfl
  ihave #HkL : kvLogAtM true γr sv.Metadata'.Index' x'.log $$ []
  · iunfold kvLogAtM; iexists A'; iframe HA'; ipureintro; exact ⟨hiL, hxm⟩
  ihave Hka : kvAppliedOn γr.raft γr.kv srvAuthSt0 A' x' (srvAuthAtLog γr.kv srvAuthSt0 A')
    $$ [HkaL]
  · iunfold kvAppliedOn
    isplitl
    · rw [hxm]; iexact HkaL
    ipureintro; rw [hxch, hon, hch]
  imod srvApplyKVOn_appliedPub s E' ρ.wait x' _ γa hM' γr A' sv.Metadata'.Index' hiL $$ HKV Hka
    with ⟨HKV, Hka, #Hpub⟩
  imod applied_jumpM true s E' γr ag sv.Metadata'.Index' x.log x'.log hgi
      (by rw [hxm, HxA.1]; exact kvModelOn_prefix γr.kv srvAuthSt0 Hif.pre)
    $$ Hainv1 Hao Hlog HkL Hic Hpub with ⟨Hao, #Hlb, #Hlog1⟩
  iunfold isWaitTime at Hwt
  icases Hwt with ⟨%wi, %Hwi, -, #HTrig⟩
  subst Hwi
  wp_apply HTrig $$ []
  · iintro !>; iexact Hlb
  (try wp_auto)
  -- `<-apply.notifyc`: the payload's second receive
  wp_apply wp_notify2_receive2 γnc nc _ _ $$ [Hnr1] as ⟨Hnr2, -⟩
  · iframe Hnc2 Hnr1
  (try wp_auto)
  -- the post's facts: the voters, the log's last term, the membership resource at `A'`, the
  -- snapshot path's resources at the new backend
  have hpos : 0 < uint.Z sv.Metadata'.Index' := by have := hai; word
  have hρr : ρ.raft = γr.raft := by rw [← Hρrd]
  ihave #Hdl' := Hdl
  iunfold srvDynLog at Hdl'
  icases Hdl' with %Hlid
  imod epCsVoters_of_snap γr.raft sv cs' nid hpos hi61 Hlid $$ Hrli Hcert Hcso with #Hcv
  ihave #Hecs : epCsAt ρ.raft A' cs' $$ []
  · iunfold epCsAt; iright; rw [hρr]; iexact Hcv
  ihave %hltA := lastTermIs_of_snap γr.raft sv A' hpos hi61 (by rw [hraft]) Hif.len $$ Hrli Hcert HA'
  have hlenP : (γr.raft.pre ++ A').length = uint.nat sv.Metadata'.Index' := by
    rw [hraft]; simp only [List.nil_append]
    have := Hif.len; have := uint_nat_eq sv.Metadata'.Index'; omega
  imod kv_log_ccOkOn γr.raft γr.kv srvAuthSt0 A' $$ HkI0 Hrli HA' with %Hcc
  have hmo : srvMemOk γr.raft γr.kv.c0 A' := by
    obtain ⟨B, hB⟩ := Hif.pre
    rw [← hB]
    exact srvMemOk_append _ _ A B Hpc.2
      (fun e he => Hcc e (by rw [← hB]; exact List.mem_append_right _ he))
  have hcov : srvPeersCover γr.raft nid A' L := fun f hf hne =>
    hL f ((netRh_member γN f).2 (Hdk.2.2 f hf)) hne
  ihave HAR' : srvApRes s γr A' $$ [Htlive]
  · iunfold srvApRes
    iexists bh, ix, lgh', tl, nid, cl, lgc, cid, L
    iframe Hbhf Hbh Htrf Hmidf Hclf' Hlgcf Hcidf Hdl
    isplitr
    · iexact Hlgcnn
    isplitl [Htlive]
    · iunfold ccMembRes
      iframe Hrc'
      iexists γN, c, ps'
      iframe Htlive Hmd'
      ipureintro; exact ⟨Hcl, Hdk⟩
    ipureintro; exact ⟨hcov, hmo⟩
  ihave #Hro1 := srvSnapRO_succ s ci γr γt d d' al ast lp cl hbs hkb hkb' hP'
    hRO' $$ [Hro Half Hauf Hlpf Hclf]
  · iframe Hro Half Hauf Hlpf Hclf
  ihave Hso' : srvSnapOwn s ci E' γr γ' sv.Metadata'.Index' $$ [Hγt Hstopc Hbo Hpath]
  · iunfold srvSnapOwn
    iexists γt, uint.nat sv.Metadata'.Index'
    iframe Hro1 Hγt
    isplitr
    · ipureintro; exact Nat.le_refl _
    iunfold srvSnapRes
    iexists d', al, cfg.DataDir'
    iframe Hstopc Hbo Half Hcfdd Hpath
    isplitr
    · ipureintro; exact hkb'
    iexact Hbf'
  iunfold epConfState at Hcs
  icases Hcs with ⟨Hcs, #Hcsok⟩
  -- the step's end, shared by the selects' branches: the apply thread at a state `stF` of the
  -- same consistent index
  ihave Hfin : iprop(∀ stF : ApplyState, ⌜loopOk γ' stF sv.Metadata'.Index' ∧
        ciEff γ' stF.k = sv.Metadata'.Index'⌝ -∗
      epAppliedIAddr ep ↦ sv.Metadata'.Index' -∗ epAppliedTAddr ep ↦ sv.Metadata'.Term' -∗
      epConfStateAddr ep ↦ cs' -∗ srvSnapState s ep mst γs sv.Metadata'.Index' (W64 0) -∗
      applyThread γ' stF -∗ applyBackend γ' ci b' -∗ ciApplying ci a t -∗ srvLgReader s -∗
      srvGoRes s -∗ mvcc.api.mvccReaders E'.γ 1 -∗
      srvApplyKVOn s E' ρ.wait x' (srvAuthAtLog γr.kv srvAuthSt0 A') -∗
      kvAppliedOn γr.raft γr.kv srvAuthSt0 A' x' (srvAuthAtLog γr.kv srvAuthSt0 A') -∗
      srvRest E' γr A' -∗ Φ #()) $$ [HΦ Hbr HAR' Hao HWA HwalT Hso']
  · iintro %stF %HF Hai Hat Hcs Hss Hst Hbe Happ Hlr Hgr Hrdk HKV Hka HRS
    ihave Hcs : epConfState ep cs' $$ [Hcs]
    · iunfold epConfState; iframe Hcs Hcsok
    iapply HΦ
    iexists γ', TM', E', b', stF, A', cs'
    isplitr
    · ipureintro; exact hbs
    iframe Hsrv1 HAR' HA' Hai Hat Hcs Hecs Hss Hst Hbe Happ Hlr Hgr Hrdk Hbr Hao Hlb HWA HwalT Hso'
    isplitl [HKV Hka HRS]
    · iexists x'; iframe HKV Hlog1 Hka HRS
    isplitr
    · iexists kv'; iframe Hkvf' Hkvi'; ipureintro; exact Hkve
    ipureintro; exact ⟨HF.1, HF.2, Hif.pre, hlenP, hltA⟩
  -- `select { case <-apply.raftAdvancedC: case <-s.stopping: return }`
  iunfold rnAdvChan at Hracc
  icases Hracc with ⟨%γac, #Hracc⟩
  ihave #HstgS := Hstgc
  iunfold stopChan at Hstgc
  icases Hstgc with ⟨%γsg, #Hstgc⟩
  wp_apply_core chan.wp_select_blocking_nil
  iapply BigAndL.bigAndL_cons.2
  isplit
  rotate_left
  · iapply BigAndL.bigAndL_cons.2
    isplit
    · ileft
      simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, stg, γsg
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply ownStopChan_is_chan $$ Hstgc
      iapply stop_chan_receive _ _ _ _ _ $$ Hstgc
      iintro ⟨-, -⟩
      (try wp_auto)
      ihave Hss : srvSnapState s ep mst γs sv.Metadata'.Index' (W64 0) $$ [Hsd Hsm Hsf0]
      · iunfold srvSnapState; iexists _, _, _; iframe Hsd Hsm Hsf0 Hmst Hslb0
        ipureintro; constructor <;> word
      have hF : loopOk γ' st' sv.Metadata'.Index' ∧ ciEff γ' st'.k = sv.Metadata'.Index' :=
        ⟨hlo', hci'⟩
      iapply Hfin $$ %st' %hF Hai Hat Hcs Hss Hst Hbe Happ Hlr Hgr Hrdk HKV Hka HRS
    iapply BigAndL.bigAndL_nil.2
    itrivial
  ileft
  simp only [chan.blockingClausePre]
  iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, rac, γac
  isplitr
  · ipureintro; rfl
  isplitr
  · iapply ownStopChan_is_chan $$ Hracc
  iapply stop_chan_receive _ _ _ _ _ $$ Hracc
  iintro ⟨-, -⟩
  (try wp_auto)
  -- `s.snapshotIfNeededAndCompactRaftLog(ep)`: nothing to do at the snapshot's index
  ihave Hfs : srvFS s $$ [Hsf0]
  · iunfold srvFS; iexists _; iexact Hsf0
  wp_apply hSINC s γr ep sv.Metadata'.Index' (by word) $$ [Hfs Hai Hsd Hsm]
    as ⟨Hfs, Hai, Hsd, Hsm⟩
  · iframe #; iframe
  (try wp_auto)
  iunfold srvFS at Hfs
  icases Hfs with ⟨%sf1, Hsf1⟩
  ihave Hss : srvSnapState s ep mst γs sv.Metadata'.Index' (W64 0) $$ [Hsd Hsm Hsf1]
  · iunfold srvSnapState; iexists _, _, _; iframe Hsd Hsm Hsf1 Hmst Hslb0
    ipureintro; constructor <;> word
  -- `select { case m := <-s.r.msgSnapC: ...; default: }`, as `wp_proofOn`'s at the snapshot's index
  have hF : loopOk γ' st' sv.Metadata'.Index' ∧ ciEff γ' st'.k = sv.Metadata'.Index' := ⟨hlo', hci'⟩
  have hlenZ : uint.Z sv.Metadata'.Index' = (A'.length : Int) := Hif.len
  iunfold isRNMsgSnapC at Hmscb
  icases Hmscb with ⟨%γc, #Hmscb⟩
  ihave #Hmscch := is_bag_is_chan γc msc _ $$ Hmscb
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  wp_apply_core chan.wp_select_nonblocking
  isplit
  · iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.nonblockingClausePre]
      iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, msc, γc
      isplitr
      · ipureintro; rfl
      isplitr
      · iexact Hmscch
      unfold nonblockingRecvAu
      isplit
      · iapply chanBag_nbRecv γc msc _ _ $$ Hmscb
        iintro %m HP
        iunfold rnSnapMsg at HP
        icases HP with ⟨%sm, Hm, %Htyb, #Hsm, -, #Huf⟩
        obtain ⟨Hty, -⟩ := Htyb
        rw [Hγm]
        letI := srvStor (GF := GF) γr.raft.raft
        ihave %Hsh := sentMsg_shape _ _ _ _ $$ Hsm
        obtain ⟨sn, hsn, -⟩ := Hsh.2 Hty
        ihave %Hsnp := srv_sentSnap_pos γr γm.id sm sn Hty hsn $$ [Hrli Hsm]
        · iframe Hrli Hsm
        -- two Go steps' time receipts (`m`'s zero value, `GetTerm`'s method value), for the merge
        -- window's write tokens
        repeat (
          fail_if_success wp_bind (App (Val (GoInstruction _)) (Val _))
          wp_pure)
        wp_bind (App (Val (GoInstruction _)) (Val _))
        iapply wp_go_step_receipt'
        case hv => first | rfl | simp [val.isPanic]
        inext
        iintro Hr1 Hl1
        iapply wp_value'
        repeat (
          fail_if_success wp_bind (App (Val (GoInstruction (MethodResolve _ _))) (Val _))
          first | wp_pure | wp_load | wp_store | wp_alloc_auto)
        wp_bind (App (Val (GoInstruction (MethodResolve _ _))) (Val _))
        iapply wp_go_step_receipt'
        case hv => first | rfl | simp [val.isPanic]
        inext
        iintro Hr2 Hl2
        iapply wp_value'
        (try wp_auto)
        wp_apply (hGT.1 m (DFrac.own 1) DFrac.discard false sm) $$ [Hm] as Hm
        · iframe #; iframe Hm
        (try wp_auto)
        wp_if_destruct
        · -- the batch's term: the snapshot's index
          wp_apply (hGS.1 m (DFrac.own 1) DFrac.discard false sm) $$ [Hm] as %ps ⟨Hsn, Hmb⟩
          · iframe #; iframe Hm
          rw [hsn]
          iunfold snapOpt at Hsn
          wp_apply (hGM.1 ps (DFrac.own 1) sn) $$ [Hsn] as %pm ⟨Hmd, Hsnb⟩
          · iframe #; iframe Hsn
          wp_apply (hGI pm (DFrac.own 1) sn.Metadata') $$ [Hmd] as Hmd
          · iframe #; iframe Hmd
          ihave Hsn := Hsnb $$ Hmd
          ihave Hm := Hmb $$ [Hsn]
          · iunfold snapOpt; iexact Hsn
          (try wp_auto)
          wp_if_destruct
          · -- the merge: the snapshot at most the applied index (the guard)
            (try wp_auto)
            ihave #HW' : srvWTPool E' γp $$ []
            · obtain ⟨-, p, P, f, cc, RO, RW, hE⟩ := hbs
              rw [hE]
              iunfold srvWTPool at HW
              unfold srvWTPool
              rw [show (E.onBe p P f cc RO RW).γbe = E.γbe from rfl]
              iexact HW
            icases srvApplyKVOn_coreA s E' ρ.wait x' _ $$ HKV with ⟨%ua, HKVc, HAr, HKVk⟩
            -- (#7-on) the auth row lends the auth buckets to the window
            ihave HL := srvAuthApplyResB_lend s E' _ γa hM' $$ HAr
            -- the apply goroutine's tokens (`apply.applyTok`), lent to the commit
            ihave HthT : apply.applyTok (GF := GF) E' $$ [Hrdk]
            · iunfold apply.applyTok; iexact Hrdk
            imod mergedCreate_window hsh hPers hReach hImg hSnap hOn hSave hPut hUR hID hName hSafe true
                s γ' ci TM' E' ρ γr b' st' sv.Metadata'.Index' a t A' x' ρ.wait γp ua kv' hlo' hci'
                auth.authBkts (authBucketsAt (srvAuthAtLog γr.kv srvAuthSt0 A'))
                (srvAuthApplyResB s E' (srvAuthAtLog γr.kv srvAuthSt0 A')) authBkts_rest
              $$ [Hst Hbe Happ HKVc HRS Hr1 Hl1 HthT HL]
              with ⟨%be, %dq, %RC, %RC', %RS, %RS', %Qd, Hkc, HRC, Hbeo, Hbs, HRCS, Hback⟩
            · iframe Hpkg Hsrv1 Hkvf' Hkvi' HW' Hr1 Hl1 HthT Hst Hbe Happ HKVc HRS HL
            -- (2026-11-06, `notes/begin-tok-plan.md`) the apply thread's token (`srvGoRes`'s) pays for
            -- the snapshot's reader slot; the reader goroutine's fork token comes back
            iunfold srvGoRes at Hgr
            icases Hgr with ⟨HgrW, HgT⟩
            wp_apply (hCM s m sm sv.Metadata'.Term' sv.Metadata'.Index' cs' fv.lg kv' be dq RC RC'
                RS RS' Qd γr.raft hmo.2.1
                (by have h := Hsh.1.2.2.2.2.2.2.1 (Or.inr (Or.inr Hty)); exact ⟨h.1, h.2, Hsh.1.2.2.2.2.2.2.2⟩))
              $$ [Hlr Hkc HRC Hbeo Hbs HRCS Hm HgT]
              as %mg ⟨Hlr, HRS', Hbeo, HgT, %rc, %Dm, %cm, #Hmg, #Hml, #HszC, #Hcsom, %Hcml, Hrs, HQd⟩
            · iframe #; iframe Hlr Hkc HRC Hbeo Hbs HRCS Hm HgT
            ihave Hgr : srvGoRes s $$ [HgrW HgT]
            · iunfold srvGoRes; iframe HgrW HgT
            imod Hback $$ %Dm HRS' HQd Hbeo
              with ⟨%st3, HthT, Hst, Hbe, Happ, HKVc, HRS, #Hmimg, HAr, %Hst3⟩
            ihave HKV := HKVk $$ HKVc HAr
            iunfold apply.applyTok at HthT
            irename HthT => Hrdk
            -- the apply thread's compaction revision `-1` (the image's log's, a mode-on one)
            imod kv_log_plainOn γr.raft γr.kv srvAuthSt0 A' $$ HkI0 Hrli HA' with %HplA'
            have hcr : x'.crev = -1 := by rw [hxcr]; exact crevOf_plainOn γr.kv A' HplA'
            -- the merged message sent: of a term committed through the applied index (the batch's
            -- term, `rnRtOk`; not `0`, a `MsgSnap`'s term), certified at the voters' conf state
            iunfold rnRtOk at Hrt
            rw [hγn]
            icases Hrt with (%Hrt0 | ⟨%ct, #Hct, %Hnct⟩)
            · exfalso
              exact (Hsh.1.2.2.2.1 (by rw [Hty]; simp [MsgSnap, MsgProp, MsgReadIndex,
                MsgTransferLeader])) Hrt0
            ihave #Hcv2 := Hcv
            iunfold epCsVoters at Hcv2
            icases Hcv2 with ⟨%c0, #Hc0, %Hcs0⟩
            ihave %Hcc := csOpt_agree cs' cm c0 $$ [Hcsom Hc0]
            · iframe Hcsom Hc0
            subst Hcc
            imod srv_merged_sent γr A' sv.Metadata'.Index' sv.Metadata'.Term' cm γm.id ct sm sn hpos
                hi61 (by have := hmo.2.1; omega) hlenZ hltA Hcs0 Hty hsn (by word)
                (by have := hnI; have := uint_nat_eq sv.Metadata'.Index'; omega)
              $$ [Hrli HA' Hsm Hct] with #Hsm'
            · iframe Hrli HA' Hsm Hct
            -- (#7-on's `merged_imageOn`) the image's certificate: the auth buckets the lent part's
            ihave Hmi : |={⊤}=> kvAppliedOn γr.raft γr.kv srvAuthSt0 A' x'
                  (srvAuthAtLog γr.kv srvAuthSt0 A') ∗
                □ (srvNet (GF := GF) γr.raft.raft).img sv.Metadata'.Index' Dm $$ [Hka]
            · iapply (merged_imageOn s γ' ci TM' E' ρ γr γa sv.Metadata'.Index' A' x' _ Dm hM'
                hlenZ ⟨hc0, hlog0⟩ hcr)
              iframe Hsrv1 Hka Hmimg; ipureintro
              obtain ⟨r0, hQ, hr⟩ := Hst3.1
              exact authBucketsAt_congr _ Dm r0 hr hQ
            imod Hmi with ⟨Hka, #Himg'⟩
            imod srvMerged_bundle γr.raft.raft m rc sm γm.id cm sv.Metadata'.Index'
                sv.Metadata'.Term' Dm Hty
              $$ [Hml HszC Hsm' Hrs Himg'] with Hbun
            · iframe Hml HszC Hsm' Hrs Himg'
            (try wp_auto)
            wp_apply (hSMS s mg m rc fv.lg fv.memberID stg tr γNt SN TSN lidt) $$ [Hgr Hlr Hbun]
              as ⟨Hgr, Hlr⟩
            · iframe #; iframe Hgr Hlr; rw [HγNt]; iframe Hbun
            (try wp_auto)
            have hF3 : loopOk γ' st3 sv.Metadata'.Index' ∧ ciEff γ' st3.k = sv.Metadata'.Index' :=
              ⟨Hst3.2.1, by rw [Hst3.2.2]; exact hci'⟩
            iapply Hfin $$ %st3 %hF3 Hai Hat Hcs Hss Hst Hbe Happ Hlr Hgr Hrdk HKV Hka HRS
          · (try wp_auto)
            iapply Hfin $$ %st' %hF Hai Hat Hcs Hss Hst Hbe Happ Hlr Hgr Hrdk HKV Hka HRS
        · (try wp_auto)
          iapply Hfin $$ %st' %hF Hai Hat Hcs Hss Hst Hbe Happ Hlr Hgr Hrdk HKV Hka HRS
      · itrivial
    iapply BigAndL.bigAndL_nil.2
    itrivial
  · -- `default`
    (try wp_auto)
    iapply Hfin $$ %st' %hF Hai Hat Hcs Hss Hst Hbe Happ Hlr Hgr Hrdk HKV Hka HRS
end proof

end EtcdGrove
end Perennial
