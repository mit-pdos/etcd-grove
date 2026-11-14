/-
**The restart construction's sub-facts** (restart S6 B2, 2026-11-14): the lemmas `NewServer.wp_proofR`
(`NewServerR.lean`) uses that no other proof provides yet, each stated here so that the main proof
stays a copy of `NewServer.wp_proofG`'s with the boot steps replaced. Lean-first.

STATUS: done (no `sorry`, 2026-11-14). The copy of `authStoreKit` that was here (`authStoreKitR`) went
with restart S5's leftovers: `authStoreKit` itself takes a restart's auth bucket.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BuiltRestart
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ImageLeases
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthSrv
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyRest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyKVLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RestReplay

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- The restarted names' compaction revision of a log is the stopped one's. -/
theorem restartNames_crevOf {ρ ρ' : ReqNames} (h : restartNames ρ ρ') (A : List EntryModel) :
    crevOf ρ'.rd.kv A = crevOf ρ.rd.kv A := by
  obtain ⟨-, h2, h3, -⟩ := h.2.1
  unfold crevOf; rw [h2, h3]

/-- The leased rest image reads only the KV names' start values (`c0`, `ch0`): the restarted names'
is the stopped one's. -/
theorem restartNames_bkRestAtL {ρ ρ' : ReqNames} (h : restartNames ρ ρ') (b : List EntryM)
    (L : List EntryModel) (D : backend.Data) :
    bkRestAtL ρ'.rd.kv b L D ↔ bkRestAtL ρ.rd.kv b L D := by
  obtain ⟨-, h2, h3, -⟩ := h.2.1
  unfold bkRestAtL kvLeases; rw [h2, h3]

/-- (The restarted lessor's requested TTLs) **`tableReq` of a table is at most the records' TTLs**,
for records whose ids are the table's (`imageLeasesAt_recs`'s facts): `NewLessor.spec`'s premise at
`reqOf := tableReq T`. -/
theorem tableReq_le_recs (T : LeaseTable) (recs : List (w64 × w64 × w64)) (hn : T.ids.Nodup)
    (hperm : (recs.map (·.1)).Perm T.ids)
    (hge : ∀ x ∈ recs, ∀ p ∈ T, p.1 = x.1 → sint.Z p.2 ≤ sint.Z x.2.1) :
    ∀ x ∈ recs, sint.Z (tableReq T x.1) ≤ sint.Z x.2.1 := by
  intro x hx
  have hm : x.1 ∈ T.ids := hperm.subset (List.mem_map.2 ⟨x, hx, rfl⟩)
  obtain ⟨p, hp, hp1⟩ := List.mem_map.1 hm
  rw [← hp1, tableReq_of_mem hn hp]
  exact hge x hx p hp hp1

/-- (The restarted lessor's guard) **A cluster that grants no lease has an empty applied table**:
the image's lease bucket holds no record unless `lg`: with `lg = false` the committed log is plain in
the lease mode `none` (`kv_log_plain`), which leaves the table (`kvTableOf_plainM`). -/
theorem restart_noGrant (γr : ReadNames) (A : List EntryModel) (hpre : γr.raft.pre = []) :
    ⊢ kvInv (GF := GF) γr.raft γr.kv -∗ srvRaftLogInv γr.raft -∗ srvRLogLb γr.raft A ={⊤}=∗
      ⌜γr.kv.lg = false → (appliedTable γr A).ids = []⌝ := by
  iintro #Hkv #Hr #HA
  imod kv_log_plain γr.raft γr.kv A $$ Hkv Hr HA with %Hpl
  imodintro
  ipureintro
  intro hlg
  have hlm : γr.kv.lm = .none := by
    rw [KVNames.lg_eq] at hlg; simpa using hlg
  have hp := Hpl.1
  rw [hlm] at hp
  unfold appliedTable kvLeases
  rw [hpre, List.nil_append, kvTableOf_plainM _ _ _ A hp]
  rfl

/-! ### P5: the members' peer URLs at a committed log -/

/-- The boot fold leaves a key no saved boot member has. -/
theorem memBootFold_notin (l : List EntryM) (acc : GMap w64 apply.MemberM) (k : w64)
    (hk : k ∉ (bootSaved l).map (·.id)) :
    (l.foldl (fun mem e => match ccDecodeV1 e.Data' with
        | some cc => mem.insert cc.nodeId (membership.ccMemberAt cc)
        | none => mem) acc).lookup k = acc.lookup k := by
  induction l generalizing acc with
  | nil => rfl
  | cons e l ih =>
    rw [List.foldl_cons]
    cases hd : ccDecodeV1 e.Data' with
    | none =>
      have hk' : k ∉ (bootSaved l).map (·.id) := by simpa [bootSaved, hd] using hk
      exact ih _ hk'
    | some cc =>
      have hk' : k ∉ (bootSaved l).map (·.id) ∧ cc.nodeId ≠ k := by
        simp only [bootSaved, List.filterMap_cons, hd, Option.map_some, List.map_cons,
          List.mem_cons, not_or] at hk
        exact ⟨hk.2, fun h => hk.1 (by rw [← h]; rfl)⟩
      simp only
      rw [ih _ hk'.1, GMap.lookup_insert_ne _ _ hk'.2]

/-- **A boot entry's member is the boot members' at its node**, the saved ids distinct. -/
theorem memBoot_lookup (boot : List EntryM) (hnd : ((bootSaved boot).map (·.id)).Nodup)
    (e : EntryM) (he : e ∈ boot) (cc : ConfChangeM) (hd : ccDecodeV1 e.Data' = some cc) :
    (memBoot boot).lookup cc.nodeId = some (membership.ccMemberAt cc) := by
  unfold memBoot
  generalize (∅ : GMap w64 apply.MemberM) = acc
  induction boot generalizing acc with
  | nil => cases he
  | cons e' l ih =>
    rw [List.foldl_cons]
    have hsplit := bootSaved_append [e'] l
    simp only [List.singleton_append] at hsplit
    have hnd' : ((bootSaved l).map (·.id)).Nodup := by
      rw [hsplit, List.map_append] at hnd; exact (List.nodup_append.1 hnd).2.1
    by_cases hl : e ∈ l
    · exact ih hnd' hl _
    · have he' : e = e' := by
        rcases List.mem_cons.1 he with h | h
        · exact h
        · exact absurd h hl
      subst he'
      have hsv : bootSaved (e :: l) = membership.ccMemberAt cc :: bootSaved l := by
        simp [bootSaved, hd]
      rw [hsv, List.map_cons, List.nodup_cons] at hnd
      refine (memBootFold_notin l _ cc.nodeId (by exact hnd.1)).trans ?_
      simp only [hd]
      rw [GMap.lookup_insert]

/-- **The boot entries keep the boot members**: each boot `AddNode` puts back the member the boot
members already hold at its node. -/
theorem bootFold_mem (boot : List EntryM) (hnd : ((bootSaved boot).map (·.id)).Nodup)
    (Q : List EntryM)
    (hQ : ∀ e ∈ Q, e ∈ boot ∧ e.Type' = W32 1 ∧ ∀ cc, ccDecodeV1 e.Data' = some cc → cc.type = W32 0)
    (r : apply.RestM) (h : ∀ f, r.mem.lookup f = (memBoot boot).lookup f) :
    ∀ f, (Q.foldl (fun r e => restEntry (W64 0) (EntryModel.ofM e) r) r).mem.lookup f =
      (memBoot boot).lookup f := by
  induction Q generalizing r with
  | nil => exact h
  | cons e Q ih =>
    rw [List.foldl_cons]
    apply ih (fun e' he' => hQ e' (List.mem_cons_of_mem _ he')) _
    obtain ⟨heb, hty, hcc⟩ := hQ e List.mem_cons_self
    have htyne : (EntryModel.ofM e).typ ≠ W32 0 := by
      simp only [EntryModel.ofM, hty]; decide
    unfold restEntry
    rw [if_neg htyne]
    simp only [EntryModel.ofM]
    cases hd : ccDecodeV1 e.Data' with
    | none => exact h
    | some cc =>
      simp only
      unfold ccRest
      split
      · split
        · rw [apply.RestM.putIn_mem]
          intro f
          simp only [GMap.lookup_insert_eq_iff]
          split
          · next he => rw [← he, memBoot_lookup boot hnd e heb cc hd]
          · exact h f
        · next hne => exact absurd (hcc cc hd) hne
      · exact h

/-- Attribute writes keep every member's peer URLs. -/
theorem foldMem_peerURLs (S : List EntryModel) (mem : GMap w64 apply.MemberM) (f : w64) :
    ((foldMem S mem).lookup f).map apply.MemberM.peerURLs =
      (mem.lookup f).map apply.MemberM.peerURLs := by
  induction S generalizing mem with
  | nil => rfl
  | cons m S ih =>
    show ((foldMem S (memStep m mem)).lookup f).map _ = _
    rw [ih]
    unfold memStep
    cases attrOf m with
    | none => rfl
    | some a =>
      simp only
      unfold memUpd
      cases hl : mem.lookup a.memberID with
      | none => simp only
      | some mm =>
        simp only
        by_cases hf : a.memberID = f
        · subst hf; rw [GMap.lookup_insert, hl]; rfl
        · rw [GMap.lookup_insert_ne _ _ hf]

/-- (Probe P5; the restart contract's clause (G)) **The members' peer URLs at a committed log are the
boot log's**: no committed conf change adds a member (every `AddNode` names a present id) and the
attribute updates keep peer URLs (`withAttrs`). Past the bootstrap log, `RestReplay`'s phase-2
invariant (`memSync_boot`, `fold_sync`) makes the members the boot members overwritten by attribute
writes (`foldMem`), which keep peer URLs (`foldMem_peerURLs`); the boot entries put back the members
`memBoot` already holds (`bootFold_mem`, `memBoot_lookup`: the saved ids distinct). -/
theorem restart_peerURLs (γ : ServerRaftNames) (γk : KVNames) (A : List EntryModel)
    (hpre : γ.pre = []) :
    ⊢ kvInv (GF := GF) γ γk -∗ srvRaftLogInv γ -∗ srvRLogLb γ A ={⊤}=∗
      ⌜∀ f, ((restModel (W64 0) γ.raft.boot A).mem.lookup f).map apply.MemberM.peerURLs =
        ((memBoot γ.raft.boot).lookup f).map apply.MemberM.peerURLs⌝ := by
  iintro - #Hinv #HA
  ihave #Hinv' := Hinv
  iunfold srvRaftLogInv at Hinv'
  icases Hinv' with ⟨-, #Hcl, -, -, -, #Hb, %Hvs0⟩
  have hvs := Hvs0.2
  iunfold srvClusterOk at Hcl
  icases Hcl with ⟨-, -, -, -, -, -, -, -, -, %Hurl, -⟩
  ihave %Hpfx := srvRLogLb_prefix γ _ A $$ [Hb HA]
  · iframe Hb HA
  ihave #HA' := HA
  iunfold srvRLogLb at HA'
  icases HA' with ⟨#Hl, %Hidx⟩
  imod srv_committed_ccBoot γ (srvLE γ A) ⊤ (fun _ _ => CoPset.mem_full) $$ [Hinv Hl] with %Hcc
  · iframe Hinv Hl
  imodintro
  ipureintro
  intro f
  have hps := hvs.2
  have hnd : ((bootSaved γ.raft.boot).map (·.id)).Nodup := by
    rw [bootSaved_ids _ _ hps]; exact hvs.1
  have hbt : ∀ e ∈ γ.raft.boot, e ∈ γ.raft.boot ∧ e.Type' = W32 1 ∧
      ∀ cc, ccDecodeV1 e.Data' = some cc → cc.type = W32 0 := by
    intro e he
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
    obtain ⟨-, -, hkk⟩ := hps
    obtain ⟨-, -, hty, m, hd, hmt, -⟩ := hkk k _ (List.getElem?_eq_getElem hk)
    exact ⟨he, hty, fun cc hd' => by rw [hd] at hd'; cases hd'; exact hmt⟩
  rcases Hpfx with hR | hR
  · -- past the bootstrap log: the boot members, overwritten by attribute writes
    obtain ⟨R, hR⟩ := hR
    have hcfg : γ.raft.cfg = GMap.listToSet γ.raft.vs := rfl
    have hmem : ∀ m ∈ A, m.typ = W32 1 → ccBootOk γ.raft.cfg m.data := fun m hm ht =>
      Hcc m.toLE (by simp only [srvLE, hpre, List.nil_append]; exact List.mem_map_of_mem hm) ht
    have hbcc : ∀ e ∈ γ.raft.boot, ∀ cc, ccDecodeV1 e.Data' = some cc →
        ccApplyOk (GMap.listToSet γ.raft.vs) cc := by
      intro e he cc hd
      have hin : EntryModel.ofM e ∈ A := by
        rw [← hR]; exact List.mem_append_left _ (List.mem_map_of_mem he)
      exact hmem _ hin (by simpa [EntryModel.ofM] using (hbt e he).2.1) cc
        (by simpa [EntryModel.ofM] using hd)
    have hcc : ∀ e ∈ R, e.typ ≠ W32 0 → ∀ cc, ccDecodeV1 e.data = some cc →
        ccApplyOk (GMap.listToSet γ.raft.vs) cc := by
      intro e he hne cc hd
      have hin : e ∈ A := by rw [← hR]; exact List.mem_append_right _ he
      obtain ⟨k, hk, hke⟩ := List.getElem_of_mem hin
      obtain ⟨-, hty⟩ := Hidx k e (by rw [← hke]; exact List.getElem?_eq_getElem hk)
      rcases hty with h0 | ⟨h1, -⟩
      · exact absurd h0 hne
      · exact hmem e hin h1 cc hd
    have hsync := memSync_boot γ.raft.vs γ.raft.boot hps hvs.1 Hurl hbcc
    have hfold : restModel (W64 0) γ.raft.boot A =
        R.foldl (fun r m => restEntry (W64 0) m r)
          (γ.raft.boot.foldl (fun r e => restEntry (W64 0) (EntryModel.ofM e) r)
            (restBoot γ.raft.boot)) := by
      rw [← hR]; simp [restModel, List.foldl_append, List.foldl_map]
    rw [hfold, fold_sync γ.raft.vs (W64 0) R _ hsync hcc, foldMem_peerURLs,
      bootFold_mem γ.raft.boot hnd γ.raft.boot hbt (restBoot γ.raft.boot) (fun _ => rfl)]
  · -- within the bootstrap log
    have hA : A = (γ.raft.boot.take A.length).map EntryModel.ofM := by
      rw [List.map_take]; exact (List.prefix_iff_eq_take.1 hR)
    have hfold : restModel (W64 0) γ.raft.boot A =
        (γ.raft.boot.take A.length).foldl (fun r e => restEntry (W64 0) (EntryModel.ofM e) r)
          (restBoot γ.raft.boot) := by
      have h1 : restModel (W64 0) γ.raft.boot A = restModel (W64 0) γ.raft.boot
          ((γ.raft.boot.take A.length).map EntryModel.ofM) := congrArg _ hA
      rw [h1]; unfold restModel; rw [List.foldl_map]
    rw [hfold, bootFold_mem γ.raft.boot hnd _ (fun e he => hbt e (List.mem_of_mem_take he))
      (restBoot γ.raft.boot) (fun _ => rfl)]

open srvApi mvcc.api in
/-- (The restart's store invariant; `srvApi.bootStore_holds`' restart form) **The store invariant at
the image's state**: the fresh store-state names moved to the image's history `kvModel A` and
compaction revision `c` (the history extends the boot's `[[], []]`), its witness the committed `A`,
its permit `c`'s, its receipt `New`'s. -/
theorem restartStore_holds (Hp : mvcc.api.persistent.law (GF := GF)) (kv : GoInterface)
    (γ : MvccName) (γr : ReadNames) (γs : KVSNames) (A : List EntryModel) (c : Int)
    (h0 : ([[], []] : mvcc.Log) <+: kvModel γr.kv A)
    (hk : mvcc.LogPutsLe etcdKeyMax (kvModel γr.kv A)) (hc : γr.kv.cmp = false → c = -1) :
    isMvcc (GF := GF) kv γ ∗ mvccState γ (stAt (kvModel γr.kv A) c) ∗ newServerStoreFreshA γs ∗
      srvRLogLb γr.raft A ∗ (⌜c = -1⌝ ∨ kvCmpPermit γr.kv c) ∗ ⧖ (mvcc.logCh (kvModel γr.kv A))
      ={⊤}=∗ kvStoreInv kv γ γr false γs ∗ wSt γs (kvModel γr.kv A) c ∗ crOwn γs c := by
  haveI := Hp.1 kv γ
  rw [kvStoreInv_eq]
  iintro ⟨#Hm, Hs, Hf, #Hlb, #Hcp, #Hr⟩
  iunfold newServerStoreFreshA at Hf
  icases Hf with ⟨Hst, Hcr, Hsl, Hnl⟩
  imod (ghostVar_update (kvModel γr.kv A, (none : Option (List mvcc.Change))) γs.st _) $$ Hst with Hst
  imod (ghostVar_update c γs.cr _) $$ Hcr with Hcr
  imod (monoListAuthOwn_update (kvModel γr.kv A) h0) $$ Hsl with ⟨Hsl, -⟩
  imod (monoListAuthOwn_update (kvModel γr.kv A) h0) $$ Hnl with ⟨Hnl, -⟩
  ihave ⟨Hst, Hw1⟩ := (ghostVar_split_half γs.st 1 _).1 $$ Hst
  ihave ⟨Hcr, Hq⟩ := (ghostVar_split_half γs.cr 1 _).1 $$ Hcr
  ihave ⟨Hw2, Hc⟩ := (ghostVar_split_half γs.cr (1 : Qp).half _).1 $$ Hq
  ihave #Hnx : kvNx γr false (kvModel γr.kv A) $$ []
  · iunfold kvNx
    iexists A
    iframe Hlb
    ipureintro; rw [kvModelM_false]; exact ⟨rfl, hk⟩
  imod inv_alloc kvsN ⊤ iprop(∃ σ : MvccState, mvccState γ σ ∗
    ghostVar γs.st (1 : Qp).half (σ.log, σ.pending) ∗ ghostVar γs.cr (1 : Qp).half σ.crev ∗
    monoListAuthOwn γs.slog 1 σ.log ∗ monoListAuthOwn γs.nlog 1 σ.notifiedLog ∗
    kvNx γr false σ.log ∗ kvNx γr false σ.notifiedLog ∗ ⧖ (mvcc.logCh σ.notifiedLog) ∗ crevOk γr σ.crev)
    $$ [Hs Hst Hcr Hsl Hnl] with #Hinv
  · inext
    iexists (stAt (kvModel γr.kv A) c)
    simp only [show (stAt (kvModel γr.kv A) c).log = kvModel γr.kv A from rfl,
      show (stAt (kvModel γr.kv A) c).crev = c from rfl,
      show (stAt (kvModel γr.kv A) c).pending = none from rfl,
      show (stAt (kvModel γr.kv A) c).notifiedLog = kvModel γr.kv A from rfl]
    iframe Hs Hst Hcr Hsl Hnl Hnx Hr
    iunfold crevOk
    iframe Hcp
    ipureintro; exact hc
  imodintro
  iunfold kvStoreInvG
  iunfold wSt
  iunfold crOwn
  iframe Hm Hinv Hw1 Hw2 Hc

open backend go_etcd_io.etcd.server.v3.storage in
/-- (Probe P7) **The image's auth buckets are a first start's leftovers**: `auth` at `authBoot`,
`authUsers` and `authRoles` empty, at every committed log (`restModel_keep`). -/
theorem imageRestAt_auth (γk : KVNames) (bootLog : List EntryM) (i : w64)
    (L : List EntryModel) (D : Data) (h : imageRestAt γk bootLog i L D) :
    (D.lookup go!"auth").getD ∅ = authBoot ∧ (D.lookup go!"authUsers").getD ∅ = ∅ ∧
      (D.lookup go!"authRoles").getD ∅ = ∅ := by
  obtain ⟨-, -, f, -, hb⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;>
  (rw [hb _ (by decide), restLeasesWith_lookup_other _ _ _ _ (by decide),
    restModel_keep _ _ _ _ (by decide) (by decide) (by decide)]
   simp [restBoot, restBootBk])

open backend go_etcd_io.etcd.server.v3.storage in
/-- (Probe P7) **The image's alarm bucket is empty**, at every committed log. -/
theorem imageRestAt_alarm (γk : KVNames) (bootLog : List EntryM) (i : w64)
    (L : List EntryModel) (D : Data) (h : imageRestAt γk bootLog i L D) :
    (D.lookup go!"alarm").getD ∅ = ∅ := by
  obtain ⟨-, -, f, -, hb⟩ := h
  rw [hb go!"alarm" (by decide), restLeasesWith_lookup_other _ _ _ _ (by decide),
    restModel_keep _ _ _ _ (by decide) (by decide) (by decide)]
  simp [restBoot, restBootBk]

open backend go_etcd_io.etcd.server.v3.storage in
/-- (Restart S6 B2, the post's `srvRest`) **The tracked buckets after the constructors at a restart
are the leased image's**: the backend's tracked buckets `rbData d.P D` with the constructors' writes
(the lessor's `lease` bucket created, the auth store's buckets at `authBoot`/`∅`/`∅`, the alarm
store's `∅`) agree on every bucket with the image's rest state (`bkRestAtL`'s, at its TTLs `f`): the
constructors' writes are what the image already holds (`restModel_keep`: no committed entry changes
them), the other tracked buckets are the image's, the untracked ones absent from both. -/
theorem restartBk_eq (d : mvcc.KBReal) (D : Data) (c0 : w64) (bootLog : List EntryM)
    (L : List EntryModel) (f : w64 → w64) (ids : List w64)
    (hb : ∀ n ∈ mvcc.restBuckets,
      D.lookup n = (apply.restLeasesWith f ids (restModel c0 bootLog L)).bk.lookup n) (n : GoString) :
    ((((((rbData d.P D).insert go!"lease" ((D.lookup go!"lease").getD ∅)).insert go!"auth"
      authBoot).insert go!"authUsers" ∅).insert go!"authRoles" ∅).insert go!"alarm" ∅).lookup n =
      (apply.restLeasesWith f ids (restModel c0 bootLog L)).bk.lookup n := by
  have hother : ∀ n, mvcc.leaseName ≠ n → go!"members" ≠ n → go!"cluster" ≠ n →
      go!"members_removed" ≠ n →
      (apply.restLeasesWith f ids (restModel c0 bootLog L)).bk.lookup n = restBootBk.lookup n := by
    intro n h0 h1 h2 h3
    rw [restLeasesWith_lookup_other _ _ _ _ h0, restModel_keep _ _ _ _ h1 h2 h3]; rfl
  by_cases hn : n ∈ mvcc.restBuckets
  · have hn' := hn
    simp only [mvcc.restBuckets, List.mem_cons, List.not_mem_nil, or_false] at hn'
    rcases hn' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · -- `lease`: present in the image
      have hp := restPresent_restLeasesWith f ids _ (restPresent_restModel c0 bootLog L)
        go!"lease" (by simp [restBootBk])
      rw [← hb _ hn] at hp ⊢
      simp only [GMap.lookup_insert_eq_iff]
      simp only [show (go!"alarm" = go!"lease") = False by decide,
        show (go!"authRoles" = go!"lease") = False by decide,
        show (go!"authUsers" = go!"lease") = False by decide,
        show (go!"auth" = go!"lease") = False by decide, if_false, if_true]
      cases h : D.lookup go!"lease" with
      | none => rw [h] at hp; cases hp
      | some x => rfl
    all_goals first
      | (rw [hother _ (by decide) (by decide) (by decide) (by decide)]; simp [restBootBk])
      | (rw [← hb _ hn]; simp only [GMap.lookup_insert_eq_iff]
         rw [rbData_real_lookup d D _ hn]; simp)
  · rw [hother n (fun h => hn (h ▸ by decide)) (fun h => hn (h ▸ by decide))
      (fun h => hn (h ▸ by decide)) (fun h => hn (h ▸ by decide))]
    have : d.P.RB n = false := by show decide (n ∈ mvcc.restBuckets) = false; simpa using hn
    simp only [mvcc.restBuckets, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hn
    simp [backend.rbData_lookup, this, restBootBk, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6,
      Ne.symm h7, Ne.symm h8]

open backend in
/-- (Restart S6 B2, the post's `srvRest`) **The apply thread's rest buckets at a restart**: at the
image's committed log `A` (`srvRest`'s), from the tracked buckets after the constructors
(`restartBk_eq`), the cluster's members at the image's, the objects' backend parts `H`, and, in a
cluster that grants leases, the lessor's live-set half, permits, requests and ever-set half; the
applied table's ids empty in a cluster that grants none (`hng`), so that `srvIds` is the table's. -/
theorem srvRest_restart (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) (D : Data)
    (d : mvcc.KBReal) (M : auth.AuthMode) (hM : M = .off) (cl : Loc) (H : IProp GF)
    (c0 : w64) (boot : List EntryM)
    (hRO : E.RO = srvRestOwnH M d.γB cl H) (hpre : γr.raft.pre = []) (hc0 : γr.kv.c0 = c0)
    (hboot : γr.raft.raft.boot = boot)
    (HbkR : bkRestAtL γr.kv γr.raft.raft.boot (γr.raft.pre ++ A) D)
    (hng : E.lg = false → (appliedTable γr A).ids = []) :
    rbOwnIn d.γB (kitSet M)
        (((((((rbData d.P D).insert go!"lease" ((D.lookup go!"lease").getD ∅)).insert go!"auth"
          authBoot).insert go!"authUsers" ∅).insert go!"authRoles" ∅).insert go!"alarm" ∅)) ∗
      membership.clusterMem cl (restModel c0 boot A).mem ∗ H ∗
      apply.ltHalf E (appliedTable γr A).ids ∗ srvGrantIf E ∗ srvReqsIf E (appliedTable γr A) ∗
      (∃ U : List w64, apply.everOwn E U ∗ ⌜srvEverOk E A U⌝) ⊢ srvRest E γr A := by
  obtain ⟨f, hf, hb⟩ := HbkR
  have hT : srvIds E (appliedTable γr A).ids = (appliedTable γr A).ids := by
    unfold srvIds; cases h : E.lg
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact (hng h).symm
    · rfl
  iintro ⟨Hrb, Hmem, HH, HL, #HG, #HQ, ⟨%U, HU, %HU⟩⟩
  iapply srvRest_close
  iexists f
  rw [hT]
  isplitr
  · ipureintro; intro _; exact hf
  rw [hpre, List.nil_append] at hb ⊢
  rw [hc0, hboot] at hb ⊢
  iframe HL HG HQ
  isplitl [Hrb Hmem HH]
  · rw [hRO]
    unfold srvRestOwnH srvRestOwn
    iframe HH
    icases rbOwnIn_kit_rest M d.γB _ $$ Hrb with ⟨Hc, Hp⟩
    rw [apply.restLeasesWith_mem]
    iframe Hmem
    have hbk := restartBk_eq d D c0 boot A f (appliedTable γr A).ids
      (by unfold appliedTable; rw [hpre, List.nil_append]; exact hb)
    isplitl [Hc]
    · iapply (rbOwnIn_congr d.γB _ _ _ (fun n _ => hbk n)).1 $$ Hc
    isplitl [Hp]
    · iapply (rbPart_congr d.γB _ _ _ (fun n _ => hbk n)).1 $$ Hp
    ipureintro
    exact ⟨restModel_memIdOk' _ _ _,
      restPresent_restLeasesWith _ _ _ (restPresent_restModel _ _ _)⟩
  iunfold srvEver
  iexists U
  iframe HU
  ipureintro; exact HU

/-- (Restart S6 B2, the post's `srvRest`) **The applied table's requests from the restarted lessor's
records** (`NewLessor`'s `leaseReqIs` of each record, at the table's request): every lease of the table
is a record's (`hperm`), its request the table's (`tableReq_of_mem`). -/
theorem srvReqs_of_recs (E : apply.AEnv GF) (T : LeaseTable) (recs : List (w64 × w64 × w64))
    (hn : T.ids.Nodup) (hperm : (recs.map (·.1)).Perm T.ids) :
    ([∗list] x ∈ recs, lease.leaseReqIs (mvcc.api.mvccLeases E.γ) x.1 (tableReq T x.1)) ⊢
      srvReqs E T := by
  iintro #H
  iunfold srvReqs
  iintro !> %p %hp
  have hm : p.1 ∈ recs.map (·.1) := hperm.symm.subset (List.mem_map.2 ⟨p, hp, rfl⟩)
  obtain ⟨x, hx, hx1⟩ := List.mem_map.1 hm
  ihave #Hx := BigSepL.bigSepL_mem
    (Φ := fun x : w64 × w64 × w64 => lease.leaseReqIs (mvcc.api.mvccLeases E.γ) x.1 (tableReq T x.1))
    hx $$ H
  have h1 : x.1 = p.1 := hx1
  rw [h1, tableReq_of_mem hn hp] at *
  iexact Hx

/-- (Restart S6 B2, the post's `srvApRes`) **The members' bounds at a restart**: `srvMemOk` at the
committed log `A` from a first start's (`srvMemOk_boot`), the members' ids at `A` the boot's (the
peer URLs at `A` the boot's, `restart_peerURLs`, give the same ids). -/
theorem srvMemOk_of_keys (γs : ServerRaftNames) (c0 : w64) (A : List EntryModel)
    (h0 : srvMemOk γs c0 [])
    (hk : ∀ f, ((restModel c0 γs.raft.boot (γs.pre ++ A)).mem.lookup f).isSome =
      ((restModel c0 γs.raft.boot (γs.pre ++ [])).mem.lookup f).isSome) :
    srvMemOk γs c0 A := by
  unfold srvMemOk srvMemCover at *
  exact ⟨fun k h => h0.1 k (by rw [← hk]; exact h), h0.2.1, fun k h => by rw [hk]; exact h0.2.2 k h⟩

/-- (Restart S6 B2, P3) **The indices at a restart**: `srvIndices_allocM`'s at the mode off, the apply
thread's ghost applied index at the image's `i` (`uint.Z i = |A|`), its log `kvModel A`'s (Go's
atomic fields still `0`: `run` sets them, and the invariant asks only `v ≤ a`). -/
theorem srvIndices_allocR (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (Ec : CoPset)
    (A : List EntryModel) (i : w64) (hai : γr.raft.ai0 = W64 0) (hi : uint.Z i = A.length) :
    ⊢ sync.atomic.ownUint64 (srvAppliedIndexAddr s) (DFrac.own 1) (W64 0) -∗
      sync.atomic.ownUint64 (srvCommittedIndexAddr s) (DFrac.own 1) (W64 0) -∗
      sync.atomic.ownUint64 (srvTermAddr s) (DFrac.own 1) (W64 0) -∗
      monoNatAuthOwn γr.applied 1 0 -∗ monoNatAuthOwn γr.committed 1 0 -∗
      ghostMapAuth γr.logs 1 (∅ : GMap w64 mvcc.Log) -∗ ghostVar γr.pend 1 false -∗
      srvApi.kvLogLb E.γs (kvModel γr.kv A) -∗ srvRLogLb γr.raft A ={Ec}=∗
      srvAppliedInvM false s E γr ∗ srvAppliedOwn γr i ∗ appliedLogAt γr i (kvModel γr.kv A) ∗
      srvCommittedInv s γr ∗ srvCommittedOwn γr (W64 0) ∗
      inv srvN (∃ t : w64, sync.atomic.ownUint64 (srvTermAddr s) (DFrac.own 1) t) := by
  iintro Hai Hci Hti Hap Hcm Hlogs Hpend #Hcert #HL
  have h0 : uint.nat (W64 0) = 0 := rfl
  imod (mono_nat_own_update (uint.nat i) (Nat.zero_le _)) $$ Hap with ⟨Hap, -⟩
  icases buildMonoNatHalves γr.applied (uint.nat i) $$ Hap with ⟨Hap1, Hap2⟩
  icases buildMonoNatHalves γr.committed 0 $$ Hcm with ⟨Hcm1, Hcm2⟩
  icases buildGhostVarHalves γr.pend false $$ Hpend with ⟨Hp1, Hp2⟩
  imod ghost_map_insert_persist i (kvModel γr.kv A) (GMap.lookup_empty _) $$ Hlogs with ⟨Hlogs, #Hlog0⟩
  imod inv_alloc srvN Ec (iprop(∃ t : w64,
      sync.atomic.ownUint64 (srvTermAddr s) (DFrac.own 1) t)) $$ [Hti] with #Hterm
  · inext; iexists W64 0; iexact Hti
  imod inv_alloc srvN Ec (iprop(∃ v : w64,
      sync.atomic.ownUint64 (srvCommittedIndexAddr s) (DFrac.own 1) v ∗
      monoNatAuthOwn γr.committed (1 : Qp).half (uint.nat v) ∗
      (∃ L : List EntryModel, srvRLogLb γr.raft L ∗ ⌜uint.Z v ≤ uint.Z γr.raft.ai0 + L.length⌝)))
    $$ [Hci Hcm1] with #Hcinv
  · inext
    iexists W64 0
    rw [h0]
    iframe Hci Hcm1
    iexists A
    iframe HL
    ipureintro; rw [hai]; word
  imod inv_alloc srvN Ec (srvAppliedBodyM false s E γr)
    $$ [Hai Hap1 Hlogs Hp1] with #Hainv
  · inext
    iunfold srvAppliedBodyM
    iexists W64 0, i, kvModel γr.kv A, (∅ : GMap w64 mvcc.Log).insert i (kvModel γr.kv A), false
    iframe Hai Hap1 Hlogs Hp1 Hcert
    isplitr
    · ipureintro
      refine ⟨by simp, ?_, ?_⟩
      · intro k L' hk
        rw [GMap.lookup_insert_Some] at hk
        rcases hk with ⟨rfl, -⟩ | ⟨-, hk⟩
        · left; exact Int.le_refl _
        · simp at hk
      · intro k k' L1 L2 h1 h2 _
        rw [GMap.lookup_insert_Some] at h1 h2
        rcases h1 with ⟨-, rfl⟩ | ⟨-, h1⟩
        · rcases h2 with ⟨-, rfl⟩ | ⟨-, h2⟩
          · exact List.prefix_refl _
          · simp at h2
        · simp at h1
    isplitr
    · iunfold appliedLogAt; iexact Hlog0
    iapply (kvLogsPubM_iff false E γr _ _).2
    isplitl
    · iunfold kvLogsOkM
      iexists A
      iframe HL
      ipureintro
      intro k L' hk
      rw [GMap.lookup_insert_Some] at hk
      rcases hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
      · refine ⟨A, List.prefix_refl _, ?_, by rw [kvModelM_false]⟩
        rw [hai, hi]; word
      · simp at hk
    iunfold appliedPubM; itrivial
  imodintro
  unfold srvAppliedInvM srvCommittedInv srvAppliedOwn srvCommittedOwn
  iframe Hainv Hcinv Hterm
  rw [h0]
  iframe Hap2 Hp2 Hcm2
  iunfold appliedLogAt; iexact Hlog0

/-- (Restart S6 B2, P3) **The certificates' invariant at a restart**: `kvCertInv_alloc`'s, its bound
`hi` the image's KV model's length, the model certified (its certificate at its length). -/
theorem kvCertInv_allocR (γs : ServerRaftNames) (γk : KVNames) (E : CoPset) (A : List EntryModel)
    (h2 : 2 ≤ γk.log0.length) (hlen : (kvModel γk A).length < 2 ^ 63) :
    ⊢ ghostMapAuth (GF := GF) γk.cok 1 (∅ : GMap w64 mvcc.Log) -∗
      ghostVar γk.hi (1 : Qp).half (kvModel γk A).length -∗ srvRLogLb γs A ={E}=∗
      kvCertInv γs γk ∗ kvCert γk (kvModel γk A) := by
  iintro HC Hhi #HL
  imod ghost_map_insert_persist (W64 ((kvModel γk A).length : Int)) (kvModel γk A)
    (GMap.lookup_empty _) $$ HC with ⟨HC, #Hc⟩
  imod inv_alloc kvcN E iprop(∃ (C : GMap w64 mvcc.Log) (hi : Nat) (Lb : List EntryModel),
    ghostMapAuth γk.cok 1 C ∗ ghostVar γk.hi (1 : Qp).half hi ∗ srvRLogLb γs Lb ∗
    ⌜certMapOk γk C hi Lb ∧ 2 ≤ γk.log0.length⌝) $$ [HC Hhi] with #Hinv
  · inext
    iexists _, (kvModel γk A).length, A
    iframe HC Hhi HL
    ipureintro
    refine ⟨?_, h2⟩
    intro n l hn
    rw [GMap.lookup_insert_Some] at hn
    rcases hn with ⟨rfl, rfl⟩ | ⟨-, hn⟩
    · exact ⟨Nat.le_refl _, rfl, hlen, A, List.prefix_refl _, rfl⟩
    · simp at hn
  imodintro
  iunfold kvCertInv
  iframe Hinv
  iunfold kvCert
  iright; iexact Hc

/-- A snapshot's read-only conf state at a non-null pointer, as `epCsVoters` takes it
(`epCsOk_of_csOptA`'s third case). -/
theorem csPts_of_csOptA (p : Loc) (c : ConfStateM) (hp : p ≠ null) :
    ⊢ csOptA (GF := GF) p DFrac.discard c -∗ csPts p DFrac.discard c false := by
  iintro H
  iunfold csOptA at H
  icases H with (⟨%Hn, -⟩ | #H | #H)
  · exact absurd Hn hp
  · iexact H
  · iunfold csPts at H
    icases H with ⟨%sv, %sl, %so, %sn, %pa, H⟩
    iNamed H
    iunfold csPts
    iexists sv, sl, so, sn, pa
    simp only [named]
    iframe HV Hv HL Hl HO Ho HN Hn HA cA Hpb
    ipureintro; exact ⟨Hnn, fun h => by cases h⟩

/-- (Restart S6 B2, P3) **The restarted storage's snapshot, once** (`rnSnapOnce_of_tok`'s restart
form): `MemoryStorage.Snapshot()` on the storage `bootstrap` rebuilt from the WAL's records `σ`, not yet
opened for writes (`memSnapNone γs (walSnapCS σ cs)`, `NodeStartSpecR`'s post: nothing writes the
storage's snapshot before `run` reads it), answers exactly the records' snapshot `walSnapCS σ cs`: the
index `σ.b = |A.take σ.b|`, the base's term, the conf state `cs` the voters' (`epCsAt`); the writers'
`memSnapLb γs 0` once opened (`memSnapNone_open`). (Restart S6 B2, 2026-11-14: restated once raft's
token was generalized to the attached snapshot, approved by etcd-grove-81; until then over the
records' certificate and the server's log, from which the exact answer did not follow.) -/
theorem restart_snapOnceR [MemStorReg GF] (wp_Snapshot : MemoryStorage.Snapshot.spec (GF := GF) (hG := hG))
    (E : RNEnv GF) (γ : RNNames) (r ms0 : Loc) (γs : MemStorNames) (σ : StorContents)
    (cs : ConfStateM) (γr : ServerRaftNames) (A : List EntryModel) (Hms0 : γ.ms = ms0)
    (hb : σ.b ≤ A.length) (hcs : confStateIs cs (Membership.simple γr.raft.cfg)) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver -∗
      isRaftNode E γ r -∗ memStorInv ms0 γs γ.node.cl γ.key -∗ memSnapNone γs (walSnapCS σ cs) -∗
      ∃ ms : Loc, rnRaftStorageAddr r ↦□ ms ∗
        rnSnapOnceR (MemStorReg.memStorRegName (GF := GF)) γ.node.cl γ.key ms γs
          (W64 (A.take σ.b).length) σ.base.term' γr A := by
  subst Hms0
  iintro #Hpkg #Hrn #Hinv Hnone
  ihave #Hinv0 := Hinv
  iunfold memStorInv at Hinv
  ihave #Hrn' := Hrn
  iunfold isRaftNode at Hrn'
  iNamed Hrn'
  subst Hmsγ
  iexists γ.ms
  iframe Hms
  iunfold rnSnapOnceR
  iintro %Φ HΦ
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hinit := isInitialized_access $$ Hraft
  iunfold isInitialized at Hinit
  iNamed Hinit
  ihave #Hc0 := memCompacted_zero (GF := GF) γs
  iapply wp_fupd
  wp_apply wp_Snapshot γ.ms γs (memStorJ γ.node.cl γ.key) none 0 (some (walSnapCS σ cs)) _
    $$ [$Hraft $Hc0 Hnone $ErrSnapUnavail] as %snap %err ⟨Hnone, %Herr, %sv, Hw, %Hsv, -⟩
  · isplitr [Hnone]
    · iapply memStorAt_none_intro $$ Hinv
      iempintro
    simp only; iexact Hnone
  imod ownSnapW_persist $$ Hw with ⟨%pm, %pc, %Hnn, #Hsn, #Hpm, #Hpc, #Hcs⟩
  have Hsv0 := Hsv.2 _ rfl
  subst Hsv0
  subst Herr
  imod memSnapNone_open γs (walSnapCS σ cs) $$ Hnone with #Hlb
  imodintro
  have hidx : (walSnapCS σ cs).Metadata'.Index' = W64 (A.take σ.b).length := by
    have hl : (A.take σ.b).length = σ.b := by simp; omega
    rw [hl]
    show σ.base.index' = W64 σ.b
    unfold StorContents.b; simp
  iapply HΦ $$ %snap %pm %pc %(walSnapCS σ cs) [] Hsn Hpm Hpc [] [] [] []
  · ipureintro
    exact ⟨hidx, rfl, Hnn.1, Hnn.2⟩
  · iapply epCsOk_of_csOptA $$ Hcs
  · iapply epCsAt_voters
    iunfold epCsVoters
    iexists (walSnapCS σ cs).Metadata'.ConfState'
    isplitl []
    · iapply csPts_of_csOptA pc (walSnapCS σ cs).Metadata'.ConfState' Hnn.2 $$ Hcs
    ipureintro; exact hcs
  · imodintro; iapply memSnapLb_mono γs _ 0 (Nat.zero_le _) $$ Hlb
  · iexact Hinv0

end lemmas

end EtcdGrove
end Perennial
