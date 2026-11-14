/-
**The restart construction's sub-facts** (restart S6 B2, 2026-11-14): the lemmas `NewServer.wp_proofR`
(`NewServerR.lean`) uses that no other proof provides yet, each stated here so that the main proof
stays a copy of `NewServer.wp_proofG`'s with the boot steps replaced. Lean-first.

STATUS: being written; the lemmas marked `sorry` are open (the handoff's list,
`notes/restart-s56-handoff.md`, "B2 proof").
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BuiltRestart
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ImageLeases
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthSrv
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyRest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyKVLemmas

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

/-- (Probe P5; the restart contract's clause (G)) **The members' peer URLs at a committed log are the
boot log's**: no committed conf change adds a member (every `AddNode` names a present id) and the
attribute updates keep peer URLs (`withAttrs`). OPEN: the phase-2 invariant of `RestConf.lean`
(the `members` bucket exactly the encodings of `r.mem`, peer URLs `memBoot`'s). -/
theorem restart_peerURLs (γ : ServerRaftNames) (γk : KVNames) (A : List EntryModel)
    (hpre : γ.pre = []) :
    ⊢ kvInv (GF := GF) γ γk -∗ srvRaftLogInv γ -∗ srvRLogLb γ A ={⊤}=∗
      ⌜∀ f, ((restModel (W64 0) γ.raft.boot A).mem.lookup f).map apply.MemberM.peerURLs =
        ((memBoot γ.raft.boot).lookup f).map apply.MemberM.peerURLs⌝ := by
  sorry

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

/-- (Restart S6 B2, P3) **The restarted storage's snapshot, once** (`rnSnapOnce_of_tok`'s restart
form): `MemoryStorage.Snapshot()` on the storage `bootstrap` rebuilt from the WAL's records `σ` answers
the records' snapshot, at the index `σ.b = |A.take σ.b|` and the base's term, its conf state the voters
after `A` (`epCsAt`). OPEN: the proof opens `memStorInv` for `memStorAt` as `rnSnapOnce_of_tok` does
and reads the snapshot's justification (`MemJust.SV`) of the restarted storage; it may need a premise
from `NodeStartSpecR`'s post (`memStorMeta`, a compaction bound `memCompacted γs σ.b`): a form. -/
theorem restart_snapOnceR [MemStorReg GF] (wp_Snapshot : MemoryStorage.Snapshot.spec (GF := GF) (hG := hG))
    (E : RNEnv GF) (γ : RNNames) (r ms0 : Loc) (γs : MemStorNames) (σ : StorContents)
    (γr : ServerRaftNames) (A : List EntryModel) (Hms0 : γ.ms = ms0) (hb : σ.b ≤ A.length) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver -∗
      isRaftNode E γ r -∗ memStorInv ms0 γs γ.node.cl γ.key -∗ walSnapCert γ.node.cl σ -∗
      srvRaftLogInv γr -∗ srvRLogLb γr A -∗
      ∃ ms : Loc, rnRaftStorageAddr r ↦□ ms ∗
        rnSnapOnceR (MemStorReg.memStorRegName (GF := GF)) γ.node.cl γ.key ms γs
          (W64 (A.take σ.b).length) σ.base.term' γr A := by
  sorry

end lemmas

section kit
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]
variable [auth_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]
open go_etcd_io.etcd.server.v3

/-- (Restart S6 B2) **`authStoreKit` with the auth bucket a restart finds**: as `authStoreKit` (its body
copied), the auth bucket empty (a first start) or at `authBoot` (a restart: what a first start
leaves), as `NewAuthStore`'s axiom takes it since HS1 (restart S5). Only the mode `off`'s is built
(`authStoreKitR_off`). Follow-up (proof cleanup): widen `authStoreKit` itself and drop this copy. -/
def authStoreKitR (M : auth.AuthMode) (tp : GoInterface) : IProp GF :=
  iprop(∃ K : IProp GF, K ∗ □ ∀ (lg : Loc) (ab : GoInterface) (abl : Loc)
      (d : mvcc.KBReal) (W Pk : IProp GF) (qo : Qp) (r : GMap GoString backend.BktData) (cost : w64),
    {{ K ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ zapLoggerOk lg ∗
        ⌜tp ≠ GoInterface.nil⌝ ∗ ⌜authRecordsFit⌝ ∗ ⌜ab = authBkIface abl⌝ ∗
        structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBackend go!"be" abl ↦□
          (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
            #d.be : GoInterface) ∗
        structFieldRef go_etcd_io.etcd.server.v3.storage.schema.authBackend go!"lg" abl ↦□ lg ∗
        backend.isBackend d.γB d.P W Pk d.be ∗ backend.bOpen d.γB qo ∗
        backend.plHook d.γB func.nil ∗ ownToks d.γB.wb 2 ∗ backend.rbOwnIn d.γB authBkts r ∗
        authKitIn M d ∗
        ⌜((r.lookup go!"auth").getD ∅ = ∅ ∨ (r.lookup go!"auth").getD ∅ = authBoot) ∧
          (r.lookup go!"authUsers").getD ∅ = ∅ ∧ (r.lookup go!"authRoles").getD ∅ = ∅⌝ ∗
        -- (2026-11-02, the backend-auth-split stage) the auth buckets in the backend's table, as
        -- `NewAuthStore`'s axiom now takes them
        ⌜d.P.has mvcc.authBI ∧ d.P.has mvcc.authUsersBI ∧ d.P.has mvcc.authRolesBI⌝ }}
      (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.auth.NewAuthStore)) (Val #lg))
        (Val #ab)) (Val #tp)) (Val #cost))
    {{ (st : GoInterface), RET #st; backend.bOpen d.γB qo ∗ backend.plHook d.γB func.nil ∗
        authKitOut M d r ∗
        ∃ (RD : IProp GF) (stl : Loc), ⌜st = auth.authIface stl⌝ ∗ authBeOn stl d.be ∗
        authRdSupply RD ∗
        -- (auth-schema-fix S1 option A) the request side once the token provider is ready (`start`
        -- fires `auth.tpReady`)
        □ (auth.tpReady M -∗ isReqAuth st RD) ∗
        authApplyOkM M stl RD ∗ authStoreLatestM M st RD stl ∗ authStoreLbM M st RD ∗
        authPublishM M stl ∗
        -- (E3zb) with auth on, the request side bound to the request context's token
        □ (⌜M.isOn = true⌝ → auth.tpReady M -∗ isReqAuthBound st RD M) ∗
        authApplyResPre M stl (auth.bump auth.bootState) d RD ∗ authCapM M stl ∗
        -- (R-D1, 2026-11-04) the store abandoned on `NewServer`'s error path
        authAbandonM M stl d RD ∗
        -- (D22 J1a, 2026-10-26) in the mode `off`, the store's `Recover` on a new backend
        -- (`NewAuthStore`'s axiom's `authRecoverOk`)
        □ (⌜M = auth.AuthMode.off⌝ → authRecoverOk stl) ∗
        -- (R2b-3d stage 5b, 2026-11-05) in the mode `off`, the store's `Close` (`NewAuthStore`'s
        -- axiom's `authCloseOk`), for `Cleanup`
        □ (⌜M = auth.AuthMode.off⌝ → authCloseOk stl) ∗
        -- (the auth-on snapshot plan's decision 8) in the mode `on`, its snapshot clause
        authSnapKitM M stl RD ∗
        -- (authkv's Main, 2026-10-30) with auth on, the store's cost field, read-only
        -- (`BcryptCost()`'s; `newAuthStore_on`'s); (C1's A4, 2026-10-31) and its `Authenticate`
        -- side (`authnStoreOk`, of its invariant: `authnStoreOk_of_authInv`)
        □ (⌜M.isOn = true⌝ →
          (∃ c : w64, structFieldRef go_etcd_io.etcd.server.v3.auth.authStore go!"bcryptCost" stl ↦□ c) ∗
          authnStoreOk st RD) }})


/-- `authStoreKitR` in the mode `off`, of `NewAuthStore`'s axiom (`authStoreKit_off`'s proof). -/
theorem authStoreKitR_off (h30 : auth.NewAuthStore.spec (GF := GF) (hG := hG)) (tp : GoInterface) :
    ⊢ authStoreKitR (GF := GF) .off tp := by
  iunfold authStoreKitR
  iexists iprop(True)
  isplitr
  · itrivial
  iintro !> %lg %ab %abl %d %W %Pk %qo %r %cost %Φ !> ⟨-, #Hpkg, #Hlg, %Htp, %Hfit, %Hab, #Habbe,
    #Hablg, #HB, Ho, Hh, Hwb, Hrb, -, %Hr, %Hhas⟩ HΦ
  -- (the auth-on snapshot plan's Prove step) the axiom at the auth buckets, idle
  ihave Hrb := backend.rbOwnIn_part _ _ _ $$ Hrb
  iapply (h30 lg ab tp cost abl d W Pk qo authBkts r (fun _ h => h) Hhas.1 Hhas.2.1
    Hhas.2.2) $$ [Ho Hh Hwb Hrb]
  · iframe Hpkg Habbe Hablg HB Ho Hh Hwb Hrb
    isplitr
    · iapply zapLoggerOk_orNil; iexact Hlg
    ipureintro; exact ⟨Htp, Hfit, Hab, Hr.1, Hr.2⟩
  iintro !> %st ⟨Ho, Hh, Hr, %RD, %stl, %Hst, Hbe, Hsl, #Hreq, #Hok, #HauR, #HauC⟩
  iapply HΦ
  iframe Ho Hh
  isplitl [Hr]
  · simp only [authKitOut]; iexact Hr
  have hR : backend.authRdN - 1 ≤ Int.toNat sync.rwmutex.actualMaxReaders := by
    rw [sync.rwmutex.actualMaxReaders_unseal]; unfold backend.authRdN; decide
  icases replicate_takeN _ (backend.authRdN - 1) _ hR $$ Hsl with ⟨Hsl, -⟩
  ihave Hsl : authRdSupply RD $$ [Hsl]
  · unfold authRdSupply; iexact Hsl
  iexists RD, stl
  iframe Hbe Hsl
  isplitr
  · ipureintro; exact Hst
  isplitr
  · iintro !> -; iexact Hreq
  isplitr
  · iExactEq Hok; rfl
  isplitr
  · unfold authStoreLatestM; itrivial
  isplitr
  · unfold authStoreLbM; itrivial
  isplitr
  · unfold authPublishM; itrivial
  isplitr
  · iintro !> %h; exact absurd h (by decide)
  isplitr
  · unfold authApplyResPre
    itrivial
  isplitr
  · unfold authCapM; itrivial
  isplitr
  · iunfold authAbandonM
    iintro !> %_st _ _
    unfold authOpenM
    imodintro; itrivial
  isplitr
  · iintro !> -
    iexact HauR
  isplitr
  · iintro !> -
    iexact HauC
  isplitr
  · unfold authSnapKitM; itrivial
  iintro !> %h; exact absurd h (by decide)


end kit

end EtcdGrove
end Perennial
