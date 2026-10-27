/-
**The image facts of a received snapshot** (D22, stage J7, 2026-10-26; `notes/snapshot-sj-plan.md`,
J7 and J0 decision 9): what `applySnapshot.specSnap`'s pure premises about the snapshot's image
(`EtcdServer__applySnapshot.lean`) follow from, on the receiver's side: the image's certificate
`srvImage γ i D` (what the snapshot message carries, `srvNet`'s `img`), the apply thread's KV ghost
state (`kvApplied`) and rest buckets (`srvRest`), the server's KV invariants (`srvKVInvs`: the
workload facts of the committed log) and its cluster (`isRaftCluster`). Lemmas, outside the
spec/proof discipline (no code). Lean-first (no Rocq counterpart).

* `snapRecv_image`: from those, a committed log `A'` extending the applied `A` with
  `uint.Z i = |A'|` and the restored log's tail `R` (`[[], []] ++ R = kvModel γr.kv A'`), with
  `SnapImageFacts`: `specSnap`'s `hpre`, `hkI`, `hlease`, `halarm`, `hauthb`, `hmemb`, `himg`
  (through the trust-boundary axiom `membership.clusterImageOk_restModel`) and `hA'` at
  `memI := (restModel …).mem`, the image's stored index (`∃ t, metaIs D (i, t)`: `hmeta` at
  `tI := t`) and (D22 J7b) `hRok` and the KV jump's length bound `hlen`.
* `snapRecv_kv_jump`: the apply thread's KV ghost state moved to `A'` (`kv_cert_jump`), and the
  restored log's certificate `certOk E.γ (kvModel γr.kv A')`; `kvApplied_of_jump` re-forms
  `kvApplied` at `A'` for the restored state (chain the start's, `alarmChain false false false`).
* (`srvRLogLb_dlv`, the image's committed log raft's delivered log of the same length, the
  `Ready`'s `isCommitted l.dlv`: deleted 2026-10-27, it read raft's committed log, and the
  server's clusters send no snapshot.)

(D22 J7b, 2026-10-26; `notes/decisions.md`, "D22 J7b") The two premises J7 left: `hRok`
(`restoreLogOk R`) is `SnapImageFacts.hRok`, from the image's `IdxWf` of its KV model (the sender's
store's, `imageAt`) and the committed log plain (`kv_log_plain`: revisions non-empty, no lease,
`restoreLogOk_kvRaftOf`), and `kv_cert_jump`'s bound is `SnapImageFacts.hlen`
(`kvModel_len_of_rok`). `hmeta` is `hmetaI` at its term `t`: `specSnap` takes the image's stored
term (`tI`), whatever it is, since the consistent index's protocol does not track the term and
restore reads none (`imageAt`'s header).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvImage
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVApply
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApply
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.clusterImageOk_restModel
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVModelRestore

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## The rest model's buckets (pure) -/

/-- A put keeps a bucket present. -/
theorem putIn_isSome (r : apply.RestM) (n k v n' : GoString) (h : (r.bk.lookup n').isSome) :
    ((r.putIn n k v).bk.lookup n').isSome := by
  by_cases e : n = n'
  · subst e; simp [apply.RestM.putIn]
  · rw [putIn_other _ _ _ _ _ e]; exact h

/-- A delete keeps a bucket present. -/
theorem delIn_isSome (r : apply.RestM) (n k n' : GoString) (h : (r.bk.lookup n').isSome) :
    ((r.delIn n k).bk.lookup n').isSome := by
  by_cases e : n = n'
  · subst e; simp [apply.RestM.delIn]
  · rw [delIn_other _ _ _ _ e]; exact h

/-- **An entry keeps every present bucket present.** -/
theorem restEntry_isSome [GooseExts] (c0 : w64) (m : EntryModel) (r : apply.RestM) (n : GoString)
    (h : (r.bk.lookup n).isSome) : ((restEntry c0 m r).bk.lookup n).isSome := by
  have hsv : ∀ v3 s (r' : apply.RestM), (r'.bk.lookup n).isSome →
      ((apply.restSetVersion v3 s r').bk.lookup n).isSome := by
    intro v3 s r' h'; unfold apply.restSetVersion; split
    · exact putIn_isSome _ _ _ _ _ h'
    · exact h'
  have hua : ∀ v3 a (r' : apply.RestM), (r'.bk.lookup n).isSome →
      ((apply.restUpdateAttrs v3 a r').bk.lookup n).isSome := by
    intro v3 a r' h'; unfold apply.restUpdateAttrs; split
    · exact h'
    · split
      · exact putIn_isSome _ _ _ _ _ h'
      · exact h'
  have hra : ∀ rq v3 (r' : apply.RestM), (r'.bk.lookup n).isSome →
      ((apply.restAfter rq v3 r').bk.lookup n).isSome := by
    intro rq v3 r' h'; unfold apply.restAfter; split
    · exact hsv _ _ _ h'
    · split
      · exact hua _ _ _ h'
      · exact h'
  have hcc : ∀ v3 cc (r' : apply.RestM), (r'.bk.lookup n).isSome →
      ((ccRest v3 cc r').bk.lookup n).isSome := by
    intro v3 cc r' h'; unfold ccRest; split
    · split
      · exact putIn_isSome _ _ _ _ _ h'
      · split
        · exact putIn_isSome _ _ _ _ _ (delIn_isSome _ _ _ _ h')
        · exact h'
    · exact h'
  unfold restEntry
  split
  · split
    · exact h
    · split
      · exact hra _ _ _ h
      · exact h
  · split
    · exact hcc _ _ _ h
    · exact h

/-- The model keeps every bucket present at the start present. -/
theorem restModel_isSome [GooseExts] (c0 : w64) (bootLog : List EntryM) (L : List EntryModel)
    (n : GoString) (h : ((restBoot bootLog).bk.lookup n).isSome) :
    ((restModel c0 bootLog L).bk.lookup n).isSome := by
  unfold restModel
  generalize restBoot bootLog = r0 at h
  induction L generalizing r0 with
  | nil => exact h
  | cons m L ih => rw [List.foldl_cons]; exact ih _ (restEntry_isSome _ _ _ _ h)

/-- The model has no bucket but the rest buckets. -/
theorem restModel_bk_none [GooseExts] (c0 : w64) (bootLog : List EntryM) (L : List EntryModel)
    (n : GoString) (hn : n ∉ mvcc.restBuckets) : (restModel c0 bootLog L).bk.lookup n = none := by
  have h1 : go!"members" ≠ n := fun e => hn (e ▸ by decide)
  have h2 : go!"cluster" ≠ n := fun e => hn (e ▸ by decide)
  have h3 : go!"members_removed" ≠ n := fun e => hn (e ▸ by decide)
  rw [restModel_keep _ _ _ _ h1 h2 h3]
  simp only [mvcc.restBuckets, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := hn
  simp [restBoot, restBootBk, Ne.symm e1, Ne.symm e2, Ne.symm e3, Ne.symm e4, Ne.symm e5,
    Ne.symm e6, Ne.symm e7, Ne.symm e8]

/-! ## An image's buckets (pure) -/

/-- `bkRestAt_boot` (`InvImage.lean`) without its section's instances. -/
theorem bkRestAt_boot' [GooseExts] {c0 : w64} {bootLog : List EntryM} {L : List EntryModel}
    {D : backend.Data} (h : bkRestAt c0 bootLog L D) :
    D.lookup go!"lease" = some ∅ ∧ D.lookup go!"alarm" = some ∅ ∧
      D.lookup go!"auth" = some authBoot ∧ D.lookup go!"authUsers" = some ∅ ∧
      D.lookup go!"authRoles" = some ∅ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [h _ (by decide), bkRestOf, restModel_keep _ _ _ _ (by decide) (by decide) (by decide)]
     simp [restBoot, restBootBk])

/-- **The rest model at an image's log is the image's tracked buckets** with the lessor's and the
alarm store's emptied (`specSnap`'s `hA'`, first half): the real instance tracks exactly the rest
buckets, which the image holds at the model's values (`bkRestAt`), the lease and alarm buckets
empty already. -/
theorem restModel_bk_of_bkRestAt [GooseExts] (d : mvcc.KBReal) {c0 : w64} {bootLog : List EntryM}
    {L : List EntryModel} {D : backend.Data} (h : bkRestAt c0 bootLog L D) :
    (restModel c0 bootLog L).bk =
      <[go!"alarm" := ∅]> (<[go!"lease" := ∅]> (backend.rbData d.P D)) := by
  obtain ⟨hl, ha, -, -, -⟩ := bkRestAt_boot' h
  apply GMap.ext
  intro n
  by_cases hn : n ∈ mvcc.restBuckets
  · have e1 : (restModel c0 bootLog L).bk.lookup n = D.lookup n := by rw [h n hn, bkRestOf]
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

/-- **An image's lease, alarm and auth buckets are the boot state's** (`specSnap`'s `hlease`,
`halarm`, `hauthb`). -/
theorem image_bootBuckets [GooseExts] (d : mvcc.KBReal) {c0 : w64} {bootLog : List EntryM}
    {L : List EntryModel} {D : backend.Data} (h : bkRestAt c0 bootLog L D) :
    ((backend.rbData d.P D).lookup go!"lease").getD ∅ = ∅ ∧
    ((backend.rbData d.P D).lookup go!"alarm").getD ∅ = ∅ ∧
    (((backend.rbData d.P D).lookup go!"auth").getD ∅ = authBoot ∧
      ((backend.rbData d.P D).lookup go!"authUsers").getD ∅ = ∅ ∧
      ((backend.rbData d.P D).lookup go!"authRoles").getD ∅ = ∅) := by
  obtain ⟨hl, ha, hau, hu, hr⟩ := bkRestAt_boot' h
  rw [rbData_real_lookup d D go!"lease" (by decide), rbData_real_lookup d D go!"alarm" (by decide),
    rbData_real_lookup d D go!"auth" (by decide), rbData_real_lookup d D go!"authUsers" (by decide),
    rbData_real_lookup d D go!"authRoles" (by decide), hl, ha, hau, hu, hr]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **An image's membership buckets are present** (`specSnap`'s `hmemb`): the start's, kept by
every entry. -/
theorem image_membBuckets [GooseExts] (d : mvcc.KBReal) {c0 : w64} {bootLog : List EntryM}
    {L : List EntryModel} {D : backend.Data} (h : bkRestAt c0 bootLog L D) :
    ((backend.rbData d.P D).lookup go!"members").isSome ∧
    ((backend.rbData d.P D).lookup go!"members_removed").isSome ∧
    ((backend.rbData d.P D).lookup go!"cluster").isSome := by
  rw [rbData_real_lookup d D go!"members" (by decide),
    rbData_real_lookup d D go!"members_removed" (by decide),
    rbData_real_lookup d D go!"cluster" (by decide), h go!"members" (by decide),
    h go!"members_removed" (by decide), h go!"cluster" (by decide)]
  simp only [bkRestOf]
  refine ⟨restModel_isSome _ _ _ _ ?_, restModel_isSome _ _ _ _ ?_, restModel_isSome _ _ _ _ ?_⟩ <;>
    simp [restBoot, restBootBk]

/-- **The image's membership buckets are the model's** (for `specSnap`'s `himg`): `clusterImageOk`
reads only the three membership buckets, which the image holds at the model's values. -/
theorem clusterImageOk_of_bkRestAt [GooseExts] (d : mvcc.KBReal) (c : Loc) (mem : GMap w64 apply.MemberM)
    {c0 : w64} {bootLog : List EntryM} {L : List EntryModel} {D : backend.Data}
    (h : bkRestAt c0 bootLog L D)
    (hc : membership.clusterImageOk c (restModel c0 bootLog L).bk mem) :
    membership.clusterImageOk c (backend.rbData d.P D) mem := by
  unfold membership.clusterImageOk at hc ⊢
  rw [rbData_real_lookup d D go!"members" (by decide),
    rbData_real_lookup d D go!"members_removed" (by decide),
    rbData_real_lookup d D go!"cluster" (by decide), h go!"members" (by decide),
    h go!"members_removed" (by decide), h go!"cluster" (by decide)]
  exact hc

/-! ## The restored log (pure) -/

/-- **The restored log's tail**: a model log from the start log `[[], []]` is `[[], []]` and its
tail (`R` of `specSnap`, `[[], []] ++ R = kvModel γk A`). -/
theorem kvModel_split (γk : KVNames) (A : List EntryModel) (h : γk.log0 = [[], []]) :
    [[], []] ++ (kvModel γk A).drop 2 = kvModel γk A := by
  have hp : γk.log0 <+: kvModel γk A := kvRaftOf_extends γk.c0 γk.ch0 γk.log0 A
  rw [h] at hp
  obtain ⟨t, ht⟩ := hp
  rw [← ht]
  simp

/-- `restoreLogOk R` bounds the restored log's length (`kv_cert_jump`'s premise). -/
theorem kvModel_len_of_rok (γk : KVNames) (A : List EntryModel) (R : mvcc.Log)
    (hlog : [[], []] ++ R = kvModel γk A) (h : mvcc.restoreLogOk R) :
    (kvModel γk A).length < 2 ^ 63 := by
  rw [← hlog]
  have := h.2.1.2.1
  omega

/-- **The facts `specSnap` takes of the image** `D` at the index `i` for the receiver's names `γr`
and real backend `d`, the applied raft log `A` and KV state `x`, the image's committed log `A'`
(after the fresh start's index `0`) and the restored log's tail `R`, the members `memI` the
membership buckets decode to (see the file header). Each field is the premise of `specSnap` of the
same name. -/
structure SnapImageFacts [GooseExts] (γr : ReadNames) (d : mvcc.KBReal) (D : backend.Data) (cl : Loc)
    (i : w64) (A A' : List EntryModel) (x : apply.ApplyKV) (R : mvcc.Log)
    (memI : GMap w64 apply.MemberM) : Prop where
  /-- the image's log extends the applied one -/
  pre : A <+: A'
  /-- the image's log ends at its index -/
  len : uint.Z i = A'.length
  /-- the restored log is the KV model of the image's log -/
  log : [[], []] ++ R = kvModel γr.kv A'
  hpre : x.log <+: [[], []] ++ R
  hkI : mvcc.keyImage ([[], []] ++ R) D
  /-- the image's stored index is `i`, its stored term some term (`specSnap`'s `hmeta` at
  `tI := t`, D22 J7b) -/
  hmetaI : ∃ t : w64, metaIs D (i, t)
  /-- (D22 J7b) the restored log's tail restorable (`specSnap`'s `hRok`) -/
  hRok : mvcc.restoreLogOk R
  /-- (D22 J7b) the image's KV model short enough (`snapRecv_kv_jump`'s `hlen`) -/
  hlen : (kvModel γr.kv A').length < 2 ^ 63
  hlease : ((backend.rbData d.P D).lookup go!"lease").getD ∅ = ∅
  halarm : ((backend.rbData d.P D).lookup go!"alarm").getD ∅ = ∅
  hauthb : ((backend.rbData d.P D).lookup go!"auth").getD ∅ = authBoot ∧
    ((backend.rbData d.P D).lookup go!"authUsers").getD ∅ = ∅ ∧
    ((backend.rbData d.P D).lookup go!"authRoles").getD ∅ = ∅
  hmemb : ((backend.rbData d.P D).lookup go!"members").isSome ∧
    ((backend.rbData d.P D).lookup go!"members_removed").isSome ∧
    ((backend.rbData d.P D).lookup go!"cluster").isSome
  himg : membership.clusterImageOk cl (backend.rbData d.P D) memI
  hA' : (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A')).bk =
      <[go!"alarm" := ∅]> (<[go!"lease" := ∅]> (backend.rbData d.P D)) ∧
    (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A')).mem = memI

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **Every conf change of a committed prefix is one the server's `applyConfChange` takes**
(`ccLogOk`, the KV invariant's workload fact `kvWork`; as `kv_log_plain` for `plainLog`). -/
theorem kv_log_ccOk (γ : ServerRaftNames) (γk : KVNames) (B : List EntryModel) :
    ⊢ kvInv (GF := GF) γ γk -∗ srvRaftLogInv γ -∗ srvRLogLb γ B ={⊤}=∗
      ⌜ccLogOk γ.raft B⌝ := by
  iintro #Hinv #Hr #HB
  iunfold kvInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%L, HL, Hσ, %Hok, #Hw⟩
  imod srvRLog_lb γ (⊤ \ ↑kvN) (mask_ndot_ne' nroot "raft_commit" "server_kv" (by decide))
    L B $$ Hr HL HB with ⟨HL, %Hp⟩
  ihave %HBi := srvRLogLb_idx γ B $$ HB
  ihave %Hcc : iprop(⌜ccLogOk γ.raft L⌝) $$ []
  · iunfold kvWork at Hw; icases Hw with ⟨%h, -⟩; ipureintro; exact h.2
  imod Hclose $$ [HL Hσ] with -
  · inext; iexists L; iframe HL Hσ Hw; ipureintro; exact Hok
  imodintro
  ipureintro
  -- (2026-10-27) `B`'s entries are the server's log's or fillers
  exact srv_entry_transfer γ.ai0 B L (fun m => m.typ ≠ W32 0 → ccPolOk γ.raft m.data)
    (fun m m' he h => by
      have h1 := congrArg Draft.LogEntry.type he
      have h2 := congrArg Draft.LogEntry.data he
      simp only [EntryModel.toLE] at h1 h2
      rw [h1, h2]; exact h)
    (fun m ht _ h => absurd ht h) HBi Hp.2.2 Hcc

/-- **The image facts, from the image's certificate** (see the file header): for the receiver at
the fresh cluster's start (`γr.raft = ⟨γ, [], 0⟩`, the start values of `NewServer.spec`), its
applied raft log `A` at the applied index `ai` below the snapshot's `i`, at least the boot log's
length, and its rest resource on the real backend `d` of the cluster `cl` (`hRO`): a committed
`A'` with `SnapImageFacts` at `memI` the model's members, `kvApplied` and `srvRest` given back. -/
theorem snapRecv_image (γ : SrvRaft) (γr : ReadNames) (E : apply.AEnv GF) (i ai : w64)
    (D : backend.Data) (d : mvcc.KBReal) (A : List EntryModel) (x : apply.ApplyKV) (cl : Loc)
    (H : IProp GF)
    (hraft : γr.raft = ⟨γ, [], W64 0⟩) (hc0 : γr.kv.c0 = W64 0)
    (hch : γr.kv.ch0 = apply.alarmChain false false false) (hlog0 : γr.kv.log0 = [[], []])
    (hai : uint.Z ai = uint.Z γr.raft.ai0 + A.length) (hi : uint.Z ai < uint.Z i)
    (hboot : (γ.boot.length : Int) ≤ uint.Z i)
    (hRO : E.RO = srvRestOwnH d.γB cl H)
    -- (merge of D43 M5, 2026-10-27) a static cluster (the image axiom's `ccBootOk` log)
    (hstat : γ.dyn = false) :
    ⊢ srvKVInvs E γr -∗ srvImage γ i D -∗ kvApplied γr.raft γr.kv A x -∗ srvRest E γr A -∗
      membership.isRaftCluster cl ={⊤}=∗
      kvApplied γr.raft γr.kv A x ∗ srvRest E γr A ∗
      ∃ (A' : List EntryModel) (R : mvcc.Log), srvRLogLb γr.raft A' ∗
        ⌜SnapImageFacts γr d D cl i A A' x R
          (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A')).mem⌝ := by
  have hpre0 : γr.raft.pre = [] := by rw [hraft]
  have hai0 : γr.raft.ai0 = W64 0 := by rw [hraft]
  have hrr : γr.raft.raft = γ := by rw [hraft]
  iintro #Hinvs #Himg Hka Hrest #Hrc
  iunfold srvKVInvs at Hinvs
  icases Hinvs with ⟨#HkI, #HcI, #HrI, %Hcok⟩
  ihave #Hdb : dbImage γr.raft γr.kv i D $$ []
  · rw [hraft]; iapply (dbImage_of_srvImage hc0 hch hlog0); iexact Himg
  iunfold dbImage at Hdb
  icases Hdb with ⟨%A', #HA', %hA'⟩
  obtain ⟨hlen', himA⟩ := hA'
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
  imod kv_log_plain γr.raft γr.kv A' $$ HkI HrI HA' with %Hpl0
  have Hpl := Hpl0.1
  -- the cluster's in-memory members, from the rest resource
  iunfold srvRest at Hrest
  rw [hRO]
  iunfold srvRestOwnH at Hrest
  icases Hrest with ⟨Hro, HH⟩
  iunfold srvRestOwn at Hro
  icases Hro with ⟨Hrb, Hmem⟩
  ihave #HA'' : srvRLogLb γr.raft (γr.raft.pre ++ A') $$ []
  · rw [hpre0, List.nil_append]; iexact HA'
  have hLL : γr.raft.pre ++ A <+: γr.raft.pre ++ A' := (List.prefix_append_right_inj _).2 hAA'
  have hbl : γr.raft.raft.boot.length ≤ (γr.raft.pre ++ A').length := by
    rw [hpre0, hrr, List.nil_append]; omega
  have hcc' : ∀ m ∈ γr.raft.pre ++ A', m.typ ≠ W32 0 → ccBootOk γr.raft.raft.cfg m.data := by
    rw [hpre0, List.nil_append]
    intro m hm ht
    exact ccPolOk_static _ _ (by rw [hrr]; exact hstat) (Hcc m hm ht)
  ihave Hax := membership.clusterImageOk_restModel.wp_proof cl γr.raft γr.kv.c0
    (γr.raft.pre ++ A) (γr.raft.pre ++ A') hpre0 hc0 hLL hbl hcc' $$ Hrc HA'' Hmem
  icases Hax with ⟨Hmem, %Himg⟩
  imodintro
  isplitl [Hhi]
  · iunfold kvApplied
    iunfold kvAppliedL
    iframe HA Hhi Hc
    ipureintro; exact ⟨Hl, Hch'⟩
  isplitl [Hrb Hmem HH]
  · iunfold srvRest
    rw [hRO]
    iunfold srvRestOwnH
    iframe HH
    iunfold srvRestOwn
    iframe Hrb Hmem
  iexists A', (kvModel γr.kv A').drop 2
  iframe HA'
  ipureintro
  have hsplit := kvModel_split γr.kv A' hlog0
  obtain ⟨hkI, hci, htm, hrest, hwf⟩ := himA
  have hb := image_bootBuckets d hrest
  have hrok : mvcc.restoreLogOk ((kvModel γr.kv A').drop 2) := by
    unfold kvModel at hwf ⊢
    rw [hlog0] at hwf ⊢
    exact restoreLogOk_kvRaftOf _ _ A' Hpl hwf
  exact {
    pre := hAA'
    len := by omega
    log := hsplit
    hpre := by rw [Hl, hsplit]; exact kvRaftOf_prefix _ _ _ _ _ hAA'
    hkI := by rw [hsplit]; exact hkI
    hmetaI := by obtain ⟨t, ht⟩ := htm; exact ⟨t, hci, ht⟩
    hRok := hrok
    hlen := kvModel_len_of_rok γr.kv A' _ hsplit hrok
    hlease := hb.1
    halarm := hb.2.1
    hauthb := hb.2.2
    hmemb := image_membBuckets d hrest
    himg := clusterImageOk_of_bkRestAt d cl _ hrest Himg
    hA' := ⟨restModel_bk_of_bkRestAt d hrest, rfl⟩ }

/-- **The apply thread's KV ghost state jumps to the image's log** (`kv_cert_jump`, with
`specSnap`'s certificate of the restored log): from its state at the applied `A` and the image's
committed `A'` extending it, its state at `A'` with the model log certified, `certOk E.γ` of it
(the server's store's map is the KV names', `srvKVInvs`), and the chain the start's. The length
bound is `kvModel_len_of_rok`'s, from `specSnap`'s `hRok`. -/
theorem snapRecv_kv_jump (E : apply.AEnv GF) (γr : ReadNames) (A A' : List EntryModel)
    (x : apply.ApplyKV) (hA : A <+: A') (hlen : (kvModel γr.kv A').length < 2 ^ 63) :
    ⊢ srvKVInvs E γr -∗ kvApplied γr.raft γr.kv A x -∗ srvRLogLb γr.raft A' ={⊤}=∗
      ⌜x.chain = γr.kv.ch0⌝ ∗ mvcc.certOk E.γ (kvModel γr.kv A') ∗
      kvAppliedL γr.raft γr.kv A' (kvModel γr.kv A') := by
  iintro #Hinvs Ha #Hlb
  iunfold srvKVInvs at Hinvs
  icases Hinvs with ⟨-, #HcI, -, %Hcok⟩
  iunfold kvApplied at Ha
  icases Ha with ⟨Ha, %Hch⟩
  imod kv_cert_jump γr.raft γr.kv ⊤ (fun _ _ => CoPset.mem_full) A A' x.log hA hlen
    $$ HcI Ha Hlb with Ha
  iunfold kvAppliedL at Ha
  icases Ha with ⟨#HB, Hhi, #Hc, %Hl⟩
  imodintro
  isplitr
  · ipureintro; exact Hch
  isplitr
  · iapply kvCert_certOk γr.kv E.γ Hcok $$ Hc
  iunfold kvAppliedL
  iframe HB Hhi Hc
  ipureintro; exact Hl

/-- **`kvApplied` at the image's log for the restored state** `x'` (its log the model's, its chain
the start's: after `applySnapshot`, `NewUberApplier`'s chain with auth off and no alarm,
`alarmChain false false false`, which `γk.ch0` is). -/
theorem kvApplied_of_jump (γ : ServerRaftNames) (γk : KVNames) (A' : List EntryModel)
    (x' : apply.ApplyKV) (hlog : x'.log = kvModel γk A') (hch : x'.chain = γk.ch0) :
    kvAppliedL (GF := GF) γ γk A' (kvModel γk A') ⊢ kvApplied γ γk A' x' := by
  iintro H
  iunfold kvApplied
  rw [hlog]
  iframe H
  ipureintro; exact hch

end lemmas

end EtcdGrove
end Perennial
