/-
**The receiver's image facts with auth on** (the auth-on snapshot plan's P6, 2026-11-03): the
mode-on twin of `SnapRecvFacts.lean`'s `snapRecv_image`, over the cluster's mode-on image
certificate (`srvImageOn`, `ImageOn.lean`) and the member's mode-on KV invariants (`srvKVInvsOn`).

* the mode-on log, pure: its compaction revision `-1` (`crevOf_plainOn`: a mode-on log has no
  compaction), its model restorable (`kvRaftOfOn_restorable`, `restoreLogOk_kvRaftOfOn`: an admin
  entry writes no revision);
* an image's buckets but the auth ones (`bkRestAtNA`, `imageAtOn`'s clause): the lease and alarm
  buckets empty, the membership buckets the model's, the rest model at them (`*_NA`);
* the KV invariant's facts of a committed prefix (`kv_log_plainOn`, `kv_log_ccOkOn`);
* `snapRecv_imageOn`: `SnapImageFactsOn` (the facts `applySnapshot.specSnapM` takes in the mode
  `on`), the restored log's receipt and the two permits (both `-1`'s: no compaction).

Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapRecvFacts
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ImageOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVApplyOn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## The mode-on log (pure) -/

/-- An admitted admin request writes no revision and compacts nothing. -/
theorem adminKindOk_kind [GooseExts] (rq : apply.IRRModel) (h : apply.adminKindOk rq) :
    ¬ writeKind (apply.dispatchKind rq) ∧ apply.dispatchKind rq ≠ .compaction := by
  unfold apply.adminKindOk at h
  split at h <;> simp_all [writeKind]

/-- A mode-on plain entry compacts nothing. -/
theorem kvCrevEntry_plainOn [GooseExts] (c₀ : w64) (ch : apply.Chain) (crev : Int)
    (m : EntryModel) (h : plainEntryOn m) : kvCrevEntry c₀ ch crev m = crev := by
  unfold kvCrevEntry
  split
  · split
    · rfl
    · rename_i ht hd
      split
      · rename_i rq hrq
        apply apply.dispatchCrev_nonCmp
        rcases h ht hd rq hrq with hp | ⟨ha, -⟩
        · exact plainReq_nonCmp rq hp.1
        · exact (adminKindOk_kind rq ha).2
      · rfl
  · rfl

/-- **A mode-on log has no compaction**: its compaction revision is the start's `-1`. -/
theorem crevOf_plainOn [GooseExts] (γk : KVNames) (A : List EntryModel) (h : plainLogOn A) :
    crevOf γk A = -1 := by
  unfold crevOf kvCrevOf
  generalize hc : (-1 : Int) = c₀
  have key : ∀ (B : List EntryModel), plainLogOn B →
      ∀ c, B.foldl (kvCrevEntry γk.c0 γk.ch0) c = c := by
    intro B
    induction B with
    | nil => intro _ c; rfl
    | cons m B ih =>
      intro hB c
      simp only [List.foldl_cons]
      rw [kvCrevEntry_plainOn _ _ _ _ (hB m (List.mem_cons_self))]
      exact ih (fun m' hm' => hB m' (List.mem_cons_of_mem _ hm')) c
  exact key A h c₀

/-- A mode-on plain entry's write is restorable (`kvEntry_growsOk`'s, an admin entry writing
nothing). -/
theorem kvEntry_growsOkOn [GooseExts] (c₀ : w64) (ch : apply.Chain) (lt : LeaseTable)
    (log : mvcc.Log) (m : EntryModel) (hm : plainEntryOn m) (hl : mvcc.LogNoLease log) :
    growsOk log (kvEntry c₀ ch lt log m) := by
  unfold kvEntry
  split
  · rename_i ht
    split
    · exact growsOk_refl _
    · rename_i hd
      split
      · rename_i rq hdec
        unfold dispatchLog
        split
        · exact growsOk_refl _
        · split
          · rcases hm ht hd rq hdec with hp | ⟨ha, -⟩
            · exact chainLog_growsOk rq lt log hp.1.1 hl ch
            · rw [chainLog_nonwrite rq lt log (adminKindOk_kind rq ha).1 ch]
              exact growsOk_refl _
          · exact growsOk_refl _
      · exact growsOk_refl _
  · exact growsOk_refl _

/-- A mode-on plain entry's step of the mode-on model is restorable. -/
theorem kvEntryOn_growsOk [GooseExts] (c₀ : w64) (ch : apply.Chain)
    (s : auth.AuthState × mvcc.Log) (m : EntryModel) (hm : plainEntryOn m)
    (hl : mvcc.LogNoLease s.2) : growsOk s.2 (kvEntryOn c₀ ch s m).2 := by
  unfold kvEntryOn
  split
  · split
    · split
      · exact growsOk_refl _
      · split
        · exact growsOk_refl _
        · exact kvEntry_growsOkOn c₀ ch [] s.2 m hm hl
    · exact growsOk_refl _
  · exact kvEntry_growsOkOn c₀ ch [] s.2 m hm hl

/-- **The mode-on model of a mode-on log, from a lease-free start, is restorable**
(`kvRaftSt_restorable`'s). -/
theorem kvRaftOfOn_restorable [GooseExts] (c₀ : w64) (ch : apply.Chain) :
    ∀ (s₀ : auth.AuthState × mvcc.Log) (A : List EntryModel), plainLogOn A →
      mvcc.LogNoLease s₀.2 →
      mvcc.LogNoLease (kvRaftOfOn c₀ ch s₀ A).2 ∧
        ∀ cs ∈ (kvRaftOfOn c₀ ch s₀ A).2.drop s₀.2.length, cs ≠ []
  | s₀, [], _, hl => ⟨hl, by simp [kvRaftOfOn_nil]⟩
  | s₀, m :: A, hA, hl => by
    have hm : plainEntryOn m := hA m (by simp)
    have hA' : plainLogOn A := fun m' h => hA m' (by simp [h])
    have hk : kvRaftOfOn c₀ ch s₀ (m :: A) = kvRaftOfOn c₀ ch (kvEntryOn c₀ ch s₀ m) A := rfl
    rw [hk]
    rcases kvEntryOn_growsOk c₀ ch s₀ m hm hl with he | ⟨cs, ⟨hne, hcs⟩, he⟩
    · have h := kvRaftOfOn_restorable c₀ ch (kvEntryOn c₀ ch s₀ m) A hA' (by rw [he]; exact hl)
      rw [he] at h; exact h
    · have hl' : mvcc.LogNoLease (s₀.2 ++ [cs]) := by
        intro cs' h
        rcases List.mem_append.1 h with h | h
        · exact hl cs' h
        · simp only [List.mem_singleton] at h; subst h; exact hcs
      obtain ⟨h1, h2⟩ := kvRaftOfOn_restorable c₀ ch (kvEntryOn c₀ ch s₀ m) A hA'
        (by rw [he]; exact hl')
      rw [he] at h2
      refine ⟨h1, ?_⟩
      obtain ⟨T, hT⟩ := kvRaftOfOn_extends c₀ ch (kvEntryOn c₀ ch s₀ m) A
      rw [he] at hT
      rw [← hT] at h2 ⊢
      intro cs' h
      rw [List.drop_append_of_le_length (by simp)] at h
      rcases List.mem_append.1 h with h | h
      · rw [List.drop_append_of_le_length (Nat.le_refl _), List.drop_length] at h
        simp only [List.nil_append, List.mem_singleton] at h
        subst h; exact hne
      · apply h2
        rw [List.drop_append_of_le_length (Nat.le_refl _), List.drop_length]
        simpa using h

/-- **`restoreLogOk` of the mode-on model's tail** (`restoreLogOk_kvRaftOf`'s). -/
theorem restoreLogOk_kvRaftOfOn [GooseExts] (c₀ : w64) (ch : apply.Chain) (st : auth.AuthState)
    (A : List EntryModel) (hA : plainLogOn A)
    (hwf : mvcc.IdxWf (kvRaftOfOn c₀ ch (st, [[], []]) A).2 []) :
    mvcc.restoreLogOk ((kvRaftOfOn c₀ ch (st, [[], []]) A).2.drop 2) := by
  have hl0 : mvcc.LogNoLease ([[], []] : mvcc.Log) := by
    intro cs hcs c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hcs
    rcases hcs with rfl | rfl <;> simp at hc
  obtain ⟨hnl, hne⟩ := kvRaftOfOn_restorable c₀ ch (st, [[], []]) A hA hl0
  obtain ⟨T, hT⟩ := kvRaftOfOn_extends c₀ ch (st, [[], []]) A
  have hsplit : [[], []] ++ (kvRaftOfOn c₀ ch (st, [[], []]) A).2.drop 2 =
      (kvRaftOfOn c₀ ch (st, [[], []]) A).2 := by
    rw [← hT]; simp
  refine ⟨fun cs hcs => hne cs (by simpa using hcs), by rw [hsplit]; exact hwf, ?_⟩
  intro cs hcs c hc k v l hcl
  exact hnl cs (List.mem_of_mem_drop hcs) c hc k v l hcl

/-- The mode-on model at a prefix is a prefix of the model at the log. -/
theorem kvModelOn_prefix [GooseExts] (γk : KVNames) (st₀ : auth.AuthState) {A A' : List EntryModel}
    (h : A <+: A') : kvModelOn γk st₀ A <+: kvModelOn γk st₀ A' := by
  obtain ⟨t, rfl⟩ := h
  unfold kvModelOn
  rw [kvRaftOfOn_append]
  exact kvRaftOfOn_extends _ _ _ t

/-- The restored log's tail of a mode-on model from `[[], []]`. -/
theorem kvModelOn_split [GooseExts] (γk : KVNames) (st₀ : auth.AuthState) (A : List EntryModel)
    (h : γk.log0 = [[], []]) :
    [[], []] ++ (kvModelOn γk st₀ A).drop 2 = kvModelOn γk st₀ A := by
  have hp : γk.log0 <+: kvModelOn γk st₀ A := kvRaftOfOn_extends γk.c0 γk.ch0 (st₀, γk.log0) A
  rw [h] at hp
  obtain ⟨t, ht⟩ := hp
  rw [← ht]
  simp

/-! ## An image's buckets but the auth ones (pure) -/

/-- **`D` holds the rest model's buckets but the auth ones** (`imageAtOn`'s clause). -/
def bkRestAtNA [GooseExts] (c0 : w64) (bootLog : List EntryM) (L : List EntryModel)
    (D : backend.Data) : Prop :=
  ∀ n ∈ restBuckets, ¬ auth.authBkts n → D.lookup n = bkRestOf c0 bootLog L n

/-- The lease and alarm buckets of such an image are the boot state's. -/
theorem bkRestAtNA_boot [GooseExts] {c0 : w64} {bootLog : List EntryM} {L : List EntryModel}
    {D : backend.Data} (h : bkRestAtNA c0 bootLog L D) :
    D.lookup go!"lease" = some ∅ ∧ D.lookup go!"alarm" = some ∅ := by
  refine ⟨?_, ?_⟩ <;>
    (rw [h _ (by decide) (by simp [auth.authBkts]), bkRestOf,
        restModel_keep _ _ _ _ (by decide) (by decide) (by decide)]
     simp [restBoot, restBootBk])

/-- `restModel_bk_of_bkRestAt` but the auth buckets (`specSnapM`'s `hA'`, first half). -/
theorem restModel_bk_of_bkRestAtNA [GooseExts] (d : mvcc.KBReal) {c0 : w64}
    {bootLog : List EntryM} {L : List EntryModel} {D : backend.Data} (h : bkRestAtNA c0 bootLog L D) :
    ∀ n, ¬ auth.authBkts n → (restModel c0 bootLog L).bk.lookup n =
      (<[go!"alarm" := ∅]> (<[go!"lease" := ∅]> (backend.rbData d.P D))).lookup n := by
  obtain ⟨hl, ha⟩ := bkRestAtNA_boot h
  intro n hna
  by_cases hn : n ∈ mvcc.restBuckets
  · have e1 : (restModel c0 bootLog L).bk.lookup n = D.lookup n := by rw [h n hn hna, bkRestOf]
    rw [e1, GMap.lookup_insert_eq_iff, GMap.lookup_insert_eq_iff, rbData_real_lookup d D n hn]
    split
    · next he => subst he; exact ha
    · split
      · next he => subst he; exact hl
      · rfl
  · rw [restModel_bk_none _ _ _ _ hn, GMap.lookup_insert_eq_iff, GMap.lookup_insert_eq_iff,
      backend.rbData_lookup]
    have hrb : d.P.RB n = false := by
      show decide (n ∈ mvcc.restBuckets) = false; simpa using hn
    have ha' : go!"alarm" ≠ n := fun e => hn (e ▸ by decide)
    have hl' : go!"lease" ≠ n := fun e => hn (e ▸ by decide)
    simp [ha', hl', hrb]

/-- An image's lease and alarm buckets are empty (`specSnapM`'s `hlease`, `halarm`). -/
theorem image_leaseAlarmNA [GooseExts] (d : mvcc.KBReal) {c0 : w64} {bootLog : List EntryM}
    {L : List EntryModel} {D : backend.Data} (h : bkRestAtNA c0 bootLog L D) :
    ((backend.rbData d.P D).lookup go!"lease").getD ∅ = ∅ ∧
    ((backend.rbData d.P D).lookup go!"alarm").getD ∅ = ∅ := by
  obtain ⟨hl, ha⟩ := bkRestAtNA_boot h
  rw [rbData_real_lookup d D go!"lease" (by decide), rbData_real_lookup d D go!"alarm" (by decide),
    hl, ha]
  exact ⟨rfl, rfl⟩

/-- `image_membBuckets` but the auth buckets. -/
theorem image_membBucketsNA [GooseExts] (d : mvcc.KBReal) {c0 : w64} {bootLog : List EntryM}
    {L : List EntryModel} {D : backend.Data} (h : bkRestAtNA c0 bootLog L D) :
    ((backend.rbData d.P D).lookup go!"members").isSome ∧
    ((backend.rbData d.P D).lookup go!"members_removed").isSome ∧
    ((backend.rbData d.P D).lookup go!"cluster").isSome := by
  rw [rbData_real_lookup d D go!"members" (by decide),
    rbData_real_lookup d D go!"members_removed" (by decide),
    rbData_real_lookup d D go!"cluster" (by decide),
    h go!"members" (by decide) (by simp [auth.authBkts]),
    h go!"members_removed" (by decide) (by simp [auth.authBkts]),
    h go!"cluster" (by decide) (by simp [auth.authBkts])]
  simp only [bkRestOf]
  refine ⟨restModel_isSome _ _ _ _ ?_, restModel_isSome _ _ _ _ ?_, restModel_isSome _ _ _ _ ?_⟩ <;>
    simp [restBoot, restBootBk]

/-- `clusterImageOk_of_bkRestAt` but the auth buckets. -/
theorem clusterImageOk_of_bkRestAtNA [GooseExts] (d : mvcc.KBReal) (c : Loc)
    (mem : GMap w64 apply.MemberM) {c0 : w64} {bootLog : List EntryM} {L : List EntryModel}
    {D : backend.Data} (h : bkRestAtNA c0 bootLog L D)
    (hc : membership.clusterImageOk c (restModel c0 bootLog L).bk mem) :
    membership.clusterImageOk c (backend.rbData d.P D) mem := by
  unfold membership.clusterImageOk at hc ⊢
  rw [rbData_real_lookup d D go!"members" (by decide),
    rbData_real_lookup d D go!"members_removed" (by decide),
    rbData_real_lookup d D go!"cluster" (by decide),
    h go!"members" (by decide) (by simp [auth.authBkts]),
    h go!"members_removed" (by decide) (by simp [auth.authBkts]),
    h go!"cluster" (by decide) (by simp [auth.authBkts])]
  exact hc

/-- The auth buckets of a real backend's tracked view are the data's. -/
theorem authBucketsAt_rbData [GooseExts] (d : mvcc.KBReal) (D : backend.Data) (st : auth.AuthState)
    (h : authBucketsAt st D) : authBucketsAt st (backend.rbData d.P D) := by
  have e : authDataOf (backend.rbData d.P D) = authDataOf D := by
    unfold authDataOf
    rw [rbData_real_lookup d D go!"auth" (by decide),
      rbData_real_lookup d D go!"authUsers" (by decide),
      rbData_real_lookup d D go!"authRoles" (by decide)]
  unfold authBucketsAt at h ⊢
  rw [e]; exact h

/-- **The facts `specSnapM` takes of a mode-on image** (`SnapImageFacts`', its auth buckets the
state after the image's log, its KV log the mode-on model's; the image's compaction records `r`). -/
structure SnapImageFactsOn [GooseExts] (γr : ReadNames) (d : mvcc.KBReal) (D : backend.Data)
    (cl : Loc) (i : w64) (A A' : List EntryModel) (x : apply.ApplyKV) (R : mvcc.Log)
    (r : mvcc.CmpRecs) (memI : GMap w64 apply.MemberM) : Prop where
  pre : A <+: A'
  len : uint.Z i = A'.length
  log : [[], []] ++ R = kvModelOn γr.kv srvAuthSt0 A'
  hpre : x.log <+: [[], []] ++ R
  hkI : mvcc.keyImageM d.cm ([[], []] ++ R) r D
  /-- the records at the image's committed log's compaction revision -/
  crev : r.crev = crevOf γr.kv A'
  hmetaI : ∃ t : w64, metaIs D (i, t)
  hRok : mvcc.restoreLogOk R
  /-- the image's KV model short enough (the KV jump's bound; review round 1's F7) -/
  hlen : (kvModelOn γr.kv srvAuthSt0 A').length < 2 ^ 63
  /-- (the lease-expiry plan's S2–S4, 2026-11-05: until then the bucket empty) -/
  hlease : imageLeasesAt γr d.P D A'
  halarm : ((backend.rbData d.P D).lookup go!"alarm").getD ∅ = ∅
  /-- the auth buckets hold the state after the image's log -/
  hauthI : authBucketsAt (srvAuthAtLog γr.kv srvAuthSt0 A') (backend.rbData d.P D)
  hmemb : ((backend.rbData d.P D).lookup go!"members").isSome ∧
    ((backend.rbData d.P D).lookup go!"members_removed").isSome ∧
    ((backend.rbData d.P D).lookup go!"cluster").isSome
  /-- the image's membership buckets the model's (review round 2's F5, as `SnapImageFacts`') -/
  himg : membership.clusterImageOk cl (backend.rbData d.P D) memI
  /-- the rest model's buckets the image's but the auth ones, its members `memI` (`specSnapM`'s
  `hA'`) -/
  hA' : (∀ n, ¬ auth.authBkts n →
      (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A')).bk.lookup n =
      (<[go!"alarm" := ∅]> (<[go!"lease" := ∅]> (backend.rbData d.P D))).lookup n) ∧
    (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A')).mem = memI

/-- **A mode-on entry changes no lease table** (`kvTable_plainM`'s twin: an auth-on log's entries are
plain KV requests or auth admin ones, none a lease's). -/
theorem kvTable_plainOn (c₀ : w64) (ch : apply.Chain) (lt : LeaseTable) (m : EntryModel)
    (hp : plainEntryOn m) : kvTable c₀ ch lt m = lt := by
  unfold kvTable
  split
  · rename_i ht
    split
    · rfl
    · rename_i hd
      split
      · rename_i rq hdec
        unfold dispatchTable
        split
        · rfl
        · rcases hp ht hd rq hdec with h | ⟨hk, -⟩
          · exact chainTable_plain rq lt h.1.1 ch
          · refine chainTable_nonwrite rq lt (fun hw => ?_) ch
            unfold apply.adminKindOk at hk
            rcases hw with hw | hw | hw | hw | hw <;> simp [hw] at hk
      · rfl
  · rfl

/-- **A mode-on log grants no lease** (`kvTableOf_plainM`'s twin). -/
theorem kvTableOf_plainOn (c₀ : w64) (ch : apply.Chain) (A : List EntryModel)
    (hp : plainLogOn A) : ∀ lt, kvTableOf c₀ ch lt A = lt := by
  induction A with
  | nil => intro lt; rfl
  | cons m A ih =>
    intro lt
    show kvTableOf c₀ ch (kvTable c₀ ch lt m) A = lt
    rw [kvTable_plainOn c₀ ch lt m (hp m (List.mem_cons_self ..))]
    exact ih (fun m' hm' => hp m' (List.mem_cons_of_mem _ hm')) lt

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **A committed prefix is a mode-on log** (`kv_log_plain`'s, of the mode-on KV invariant). -/
theorem kv_log_plainOn (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState)
    (B : List EntryModel) :
    ⊢ kvInvOn (GF := GF) γ γk st₀ -∗ srvRaftLogInv γ -∗ srvRLogLb γ B ={⊤}=∗ ⌜plainLogOn B⌝ := by
  iintro #Hinv #Hr #HB
  iunfold kvInvOn at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%L, HL, Hσ, Hh, %Hok, #Hw⟩
  imod srvRLog_lb γ (⊤ \ ↑kvN) (mask_ndot_ne' nroot "raft_commit" "server_kv" (by decide))
    L B $$ Hr HL HB with ⟨HL, %Hp⟩
  ihave %HBi := srvRLogLb_idx γ B $$ HB
  imod Hclose $$ [HL Hσ Hh] with -
  · inext; iexists L; iframe HL Hσ Hh Hw; ipureintro; exact Hok
  imodintro
  ipureintro
  refine srv_entry_transfer γ.ai0 B L plainEntryOn ?_ ?_ ?_ HBi Hp.2.2 Hok.1
  · intro m m' he h ht hd rq hdec
    have h1 := congrArg LogEntry.type he
    have h2 := congrArg LogEntry.data he
    simp only [EntryModel.toLE] at h1 h2
    exact h (h1 ▸ ht) (h2 ▸ hd) rq (h2 ▸ hdec)
  · intro m _ hd _ h; exact absurd hd h
  · intro m ht _ h0; rw [ht] at h0; exact absurd h0 (by decide)

/-- **Every conf change of a committed prefix is one the server's `applyConfChange` takes**
(`kv_log_ccOk`'s, of the mode-on KV invariant's workload facts). -/
theorem kv_log_ccOkOn (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState)
    (B : List EntryModel) :
    ⊢ kvInvOn (GF := GF) γ γk st₀ -∗ srvRaftLogInv γ -∗ srvRLogLb γ B ={⊤}=∗
      ⌜ccLogOk γ.raft B⌝ := by
  iintro #Hinv #Hr #HB
  ihave #HBc : isCommittedLogLb γ.raft.cl (srvLE γ B) $$ []
  · iunfold srvRLogLb at HB; icases HB with ⟨#H, -⟩; iexact H
  imod (srv_committed_noV2 γ (srvLE γ B) ⊤ CoPset.subseteq_top CoPset.subseteq_top)
    $$ [] with %Hv2
  · iframe Hr HBc
  have hnv : ∀ m ∈ B, ¬ (m.typ = W32 2 ∧ m.data = []) := by
    rintro m hm ⟨ht, hd⟩
    apply Hv2 m.toLE (by unfold srvLE; exact List.mem_map_of_mem (List.mem_append_right _ hm))
    exact ⟨hd, ht⟩
  iunfold kvInvOn at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%L, HL, Hσ, Hh, %Hok, #Hw⟩
  imod srvRLog_lb γ (⊤ \ ↑kvN) (mask_ndot_ne' nroot "raft_commit" "server_kv" (by decide))
    L B $$ Hr HL HB with ⟨HL, %Hp⟩
  ihave %HBi := srvRLogLb_idx γ B $$ HB
  ihave %Hcc : iprop(⌜ccLogOk γ.raft L⌝) $$ []
  · iunfold kvWorkOn at Hw; icases Hw with ⟨%h, -⟩; ipureintro; exact h.2.1
  imod Hclose $$ [HL Hσ Hh] with -
  · inext; iexists L; iframe HL Hσ Hh Hw; ipureintro; exact Hok
  imodintro
  ipureintro
  have := srv_entry_transfer γ.ai0 B L
    (fun m => ¬ (m.typ = W32 2 ∧ m.data = []) → m.typ ≠ W32 0 → ccPolOk γ.raft m.data)
    (fun m m' he h hn => by
      have h1 := congrArg LogEntry.type he
      have h2 := congrArg LogEntry.data he
      simp only [EntryModel.toLE] at h1 h2
      rw [h1, h2]; rw [h1, h2] at hn; exact h hn)
    (fun m ht _ _ h => absurd ht h) (fun m ht hd hn => absurd ⟨ht, hd⟩ hn) HBi Hp.2.2
    (fun m hm _ => Hcc m hm)
  exact fun m hm => this m hm (hnv m hm)

/-- **The image facts with auth on, from the cluster's mode-on image certificate**
(`snapRecv_image`'s): for the receiver at the fresh cluster's start with the mode-on start values,
its applied raft log `A` at the applied index `ai` below the snapshot's `i`, at least the boot
log's length, and its rest resource on the real backend `d` of the cluster `cl` (`hRO`): a
committed `A'` with `SnapImageFactsOn` at `memI` the model's members and the image's records `r`,
`kvAppliedOn` and `srvRest` given back, the restored log's receipt and the two permits (the
records empty: a mode-on log has no compaction, `crevOf_plainOn`). -/
theorem snapRecv_imageOn (γ : SrvRaft) (γr : ReadNames) (E : apply.AEnv GF) (i ai : w64)
    (D : backend.Data) (d : mvcc.KBReal) (A : List EntryModel) (x : apply.ApplyKV) (cl : Loc)
    (H : IProp GF) (sa : auth.AuthState) (_hkb : E.γ.kb = some d)
    (hraft : γr.raft = ⟨γ, [], W64 0⟩) (hc0 : γr.kv.c0 = W64 0)
    (hch : γr.kv.ch0 = apply.alarmChain true false false) (hlog0 : γr.kv.log0 = [[], []])
    (hai : uint.Z ai = uint.Z γr.raft.ai0 + A.length) (hi : uint.Z ai < uint.Z i)
    (hboot : (γ.boot.length : Int) ≤ uint.Z i)
    (hRO : E.RO = srvRestOwnH E.authMode d.γB cl H) (hlg : E.lg = false) :
    ⊢ srvKVInvsOn E γr srvAuthSt0 -∗ srvImageOn γ i D -∗
      kvAppliedOn γr.raft γr.kv srvAuthSt0 A x sa -∗ srvRest E γr A -∗
      membership.isRaftCluster cl ={⊤}=∗
      kvAppliedOn γr.raft γr.kv srvAuthSt0 A x sa ∗ srvRest E γr A ∗
      ∃ (A' : List EntryModel) (R : mvcc.Log) (r : mvcc.CmpRecs), srvRLogLb γr.raft A' ∗
        ⌜SnapImageFactsOn γr d D cl i A A' x R r
          (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A')).mem⌝ ∗
        mvcc.restoreRcptM d ([[], []] ++ R) ∗ mvcc.crevPermAt E.γ r.finRev ∗
        mvcc.crevPermAt E.γ r.crev := by
  have hpre0 : γr.raft.pre = [] := by rw [hraft]
  have hai0 : γr.raft.ai0 = W64 0 := by rw [hraft]
  have hrr : γr.raft.raft = γ := by rw [hraft]
  have hz : uint.Z (W64 0) = 0 := rfl
  rw [srvRest_false E γr A hlg]
  iintro #Hinvs #Himg Hka Hrest #Hrc
  iunfold srvKVInvsOn at Hinvs
  icases Hinvs with ⟨#HkI, #HcI, #HrI, -, %Hcok, #Hcp, -⟩
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
  icases Hdb with ⟨%A', #HA'0, %hA', #Hrcp0⟩
  ihave #HA' : srvRLogLb γr.raft A' $$ []
  · rw [hraft]; iexact HA'0
  obtain ⟨hlen', himA⟩ := hA'
  simp only at hlen'
  rw [hz] at hlen'
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
    (γr.raft.pre ++ A) (γr.raft.pre ++ A') hpre0 hc0 hLL hbl hcc' $$ Hrc HA'' Hmem
  icases Hax with ⟨Hmem, %Himg⟩
  -- the image's clauses at the member's names
  obtain ⟨⟨r, hkI, hr⟩, hci, htm, hrest, hauth, hwf⟩ := himA
  rw [hk] at hkI hwf
  rw [hcr] at hr
  rw [hsa] at hauth
  have hrest' : bkRestAtNA γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A') D := by
    intro n hn hna
    rw [hrest n hn hna, hpre0, hrr, hc0, h0']
  have hcrev : crevOf γr.kv A' = -1 := crevOf_plainOn γr.kv A' Hpl
  have hb : mvcc.LogB (kvModelOn γr.kv srvAuthSt0 A') := ⟨by have := hwf.2.1; omega, hwf.2.2.2⟩
  have hkI' : mvcc.keyImageM d.cm (kvModelOn γr.kv srvAuthSt0 A') r D :=
    mvcc.keyImageM_mode _ _ _ r D hb hkI (fun _ _ => by rw [hr, hcrev])
  have hre : r = mvcc.CmpRecs.empty := by
    cases hdm : d.cm with
    | false =>
      rw [hdm] at hkI'
      exact ((mvcc.keyImageM_off _ _ D).1 hkI').2
    | true =>
      rw [hdm] at hkI'
      exact mvcc.CmpRecs.empty_of_crev r (mvcc.keyImageM_recsPos _ _ _ hkI') (by rw [hr, hcrev])
  have hsplit := kvModelOn_split γr.kv srvAuthSt0 A' hlog0
  have hrok : mvcc.restoreLogOk ((kvModelOn γr.kv srvAuthSt0 A').drop 2) := by
    unfold kvModelOn at hwf ⊢
    rw [hlog0] at hwf ⊢
    exact restoreLogOk_kvRaftOfOn _ _ _ A' Hpl hwf
  ihave #Hrcp : ⧖ (mvcc.logCh (kvModelOn γr.kv srvAuthSt0 A')) $$ []
  · rw [← hk]; iexact Hrcp0
  ihave #Hrcpt : mvcc.restoreRcptM (GF := GF) d (kvModelOn γr.kv srvAuthSt0 A') $$ []
  · unfold mvcc.restoreRcptM
    split
    · iexact Hrcp
    · itrivial
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
  iexists A', (kvModelOn γr.kv srvAuthSt0 A').drop 2, r
  iframe HA'
  rw [hsplit]
  iframe Hrcpt
  have hxl : x.log = kvModelOn γr.kv srvAuthSt0 A := by
    unfold kvModelOn; rw [← Hl]
  have hTnil : (appliedTable γr A').ids = [] := by
    unfold appliedTable kvLeases; rw [hpre0, List.nil_append, kvTableOf_plainOn _ _ A' Hpl]; rfl
  have hfacts : SnapImageFactsOn γr d D cl i A A' x ((kvModelOn γr.kv srvAuthSt0 A').drop 2) r
      (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A')).mem := {
    pre := hAA'
    len := by omega
    log := hsplit
    hpre := by rw [hsplit, hxl]; exact kvModelOn_prefix _ _ hAA'
    hkI := by rw [hsplit]; exact hkI'
    crev := hr
    hmetaI := by obtain ⟨t, ht⟩ := htm; exact ⟨t, hci, ht⟩
    hRok := hrok
    hlen := by
      rw [← hsplit]
      have := hrok.2.1.2.1
      omega
    hlease := imageLeasesAt_of_nil hTnil (image_leaseAlarmNA d hrest').1
    halarm := (image_leaseAlarmNA d hrest').2
    hauthI := authBucketsAt_rbData d D _ hauth
    hmemb := image_membBucketsNA d hrest'
    himg := clusterImageOk_of_bkRestAtNA d cl _ hrest' Himg
    hA' := ⟨restModel_bk_of_bkRestAtNA d hrest', rfl⟩ }
  isplitr
  · ipureintro; exact hfacts
  subst hre
  rw [mvcc.CmpRecs.finRev_empty, mvcc.CmpRecs.crev_empty]
  isplitr <;> iapply mvcc.crevPermAt_none

/-- **The apply thread's KV ghost state jumps to a longer committed log, in the mode `on`**
(`kv_cert_jump`'s counterpart): certified, at the mode-on model's state after `A'`. -/
theorem kv_cert_jumpOn (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState) (E : CoPset)
    (hE : ↑kvcN ⊆ E) (A A' : List EntryModel) (s : auth.AuthState × mvcc.Log) (hA : A <+: A')
    (hlen : (kvModelOn γk st₀ A').length < 2 ^ 63) :
    ⊢ kvCertInvOn (GF := GF) γ γk st₀ -∗ kvAppliedLOn γ γk st₀ A s -∗ srvRLogLb γ A' ={E}=∗
      kvAppliedLOn γ γk st₀ A' (srvAuthAtLog γk st₀ A', kvModelOn γk st₀ A') := by
  iintro #Hinv Ha #Hlb
  iunfold kvAppliedLOn at Ha
  icases Ha with ⟨#HA, Hhi, #Hc, %Hl⟩
  have hs2 : s.2 = kvModelOn γk st₀ A := by unfold kvModelOn; rw [Hl]
  have hq : (srvAuthAtLog γk st₀ A', kvModelOn γk st₀ A') = kvRaftOfOn γk.c0 γk.ch0 (st₀, γk.log0) A' :=
    rfl
  rw [hs2]
  have hpre : kvModelOn γk st₀ A <+: kvModelOn γk st₀ A' := kvModelOn_prefix γk st₀ hA
  by_cases heq : (kvModelOn γk st₀ A).length = (kvModelOn γk st₀ A').length
  · have he : kvModelOn γk st₀ A = kvModelOn γk st₀ A' := hpre.eq_of_length heq
    imodintro
    iunfold kvAppliedLOn
    simp only
    rw [← he]
    iframe Hlb Hhi Hc
    ipureintro; rw [he]; exact hq
  · have hlt : (kvModelOn γk st₀ A).length < (kvModelOn γk st₀ A').length := by
      have := hpre.length_le; omega
    iunfold kvCertInvOn at Hinv
    iinv Hinv with >Hi Hclose
    icases Hi with ⟨%C, %hi, %Lb, HC, Hhi', #HLb, %Hok⟩
    ihave %Hhe := ghostVar_agree γk.hi _ _ _ _ $$ Hhi Hhi'
    have hfresh : C.lookup (W64 ((kvModelOn γk st₀ A').length : Int)) = none := by
      cases h : C.lookup (W64 ((kvModelOn γk st₀ A').length : Int)) with
      | none => rfl
      | some l'' =>
        obtain ⟨h1, h2, h3, -⟩ := Hok.1 _ _ h
        have := w64_len_inj _ _ hlen h3 h2
        omega
    imod ghost_map_insert_persist _ (kvModelOn γk st₀ A') hfresh $$ HC with ⟨HC, #He⟩
    imod ghostVar_update_halves (kvModelOn γk st₀ A').length γk.hi _ _ $$ Hhi Hhi' with ⟨Hhi, Hhi'⟩
    ihave %Hcmp := srvRLogLb_prefix γ A' Lb $$ [Hlb HLb]
    · iframe Hlb HLb
    have hold : ∀ n l2, C.lookup n = some l2 → l2.length ≤ (kvModelOn γk st₀ A').length := by
      intro n l2 hn
      have := (Hok.1 n l2 hn).1
      omega
    imod Hclose $$ [HC Hhi'] with -
    · inext
      rcases Hcmp with h | h
      · iexists C.insert (W64 ((kvModelOn γk st₀ A').length : Int)) (kvModelOn γk st₀ A'),
          (kvModelOn γk st₀ A').length, Lb
        iframe HC Hhi' HLb
        ipureintro
        refine ⟨?_, Hok.2⟩
        intro n l2 hn
        rw [GMap.lookup_insert_Some] at hn
        rcases hn with ⟨rfl, rfl⟩ | ⟨-, hn⟩
        · exact ⟨Nat.le_refl _, rfl, hlen, A', h, rfl⟩
        · obtain ⟨-, h2, h3, A'', h4, h5⟩ := Hok.1 n l2 hn
          exact ⟨hold n l2 hn, h2, h3, A'', h4, h5⟩
      · iexists C.insert (W64 ((kvModelOn γk st₀ A').length : Int)) (kvModelOn γk st₀ A'),
          (kvModelOn γk st₀ A').length, A'
        iframe HC Hhi' Hlb
        ipureintro
        refine ⟨?_, Hok.2⟩
        intro n l2 hn
        rw [GMap.lookup_insert_Some] at hn
        rcases hn with ⟨rfl, rfl⟩ | ⟨-, hn⟩
        · exact ⟨Nat.le_refl _, rfl, hlen, A', List.prefix_refl _, rfl⟩
        · obtain ⟨-, h2, h3, A'', h4, h5⟩ := Hok.1 n l2 hn
          exact ⟨hold n l2 hn, h2, h3, A'', h4.trans h, h5⟩
    imodintro
    iunfold kvAppliedLOn
    simp only
    iframe Hlb Hhi
    isplitr
    · iunfold kvCert; iright; iexact He
    ipureintro; exact hq

/-- **The receiver's KV ghost state jumps to the image's log, in the mode `on`**
(`snapRecv_kv_jump`'s counterpart). -/
theorem snapRecv_kv_jumpOn (E : apply.AEnv GF) (γr : ReadNames) (A A' : List EntryModel)
    (x : apply.ApplyKV) (sa : auth.AuthState) (hA : A <+: A')
    (hlen : (kvModelOn γr.kv srvAuthSt0 A').length < 2 ^ 63) :
    ⊢ srvKVInvsOn (GF := GF) E γr srvAuthSt0 -∗ kvAppliedOn γr.raft γr.kv srvAuthSt0 A x sa -∗
      srvRLogLb γr.raft A' ={⊤}=∗
      ⌜x.chain = γr.kv.ch0⌝ ∗ mvcc.certOk E.γ (kvModelOn γr.kv srvAuthSt0 A') ∗
      kvAppliedLOn γr.raft γr.kv srvAuthSt0 A'
        (srvAuthAtLog γr.kv srvAuthSt0 A', kvModelOn γr.kv srvAuthSt0 A') := by
  iintro #Hinvs Ha #Hlb
  iunfold srvKVInvsOn at Hinvs
  icases Hinvs with ⟨-, #HcI, -, -, %Hcok, -⟩
  iunfold kvAppliedOn at Ha
  icases Ha with ⟨Ha, %Hch⟩
  imod kv_cert_jumpOn γr.raft γr.kv srvAuthSt0 ⊤ (fun _ _ => CoPset.mem_full) A A' (sa, x.log) hA hlen
    $$ HcI Ha Hlb with Ha
  iunfold kvAppliedLOn at Ha
  icases Ha with ⟨#HB, Hhi, #Hc, %Hl⟩
  imodintro
  isplitr
  · ipureintro; exact Hch
  isplitr
  · iapply kvCert_certOk γr.kv E.γ Hcok $$ Hc
  iunfold kvAppliedLOn
  iframe HB Hhi Hc
  ipureintro; exact Hl

end lemmas

end EtcdGrove
end Perennial
