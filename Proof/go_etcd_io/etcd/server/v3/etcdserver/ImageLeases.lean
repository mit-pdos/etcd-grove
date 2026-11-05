/-
**The image's lease bucket** (the lease-expiry plan's S2–S4 Draft, 2026-11-05, S3;
`notes/lease-expiry-plan.md`, "S2–S4 Draft"). Lean-first (no Rocq counterpart).

A snapshot's image in a cluster that grants leases carries, in its `lease` bucket, the records of
the live leases of its committed log (the leased rest image `bkRestAtL`, `RestLeased.lean`, which
the image certificate `imageAt` already states): one record per id of the log's lease table, at
some TTL (each member's `minLeaseTTL` is its own, B1). `imageLeasesAt` is that bucket alone, at the
receiver's names: what `lessor.Recover` reads (`imageLeasesAt_recs`: the bucket's entries are
`MustUnsafeGetAllLeases`'s record encodings, `leaseRecEnc`, so no decoding law beyond that axiom's
is needed) and what the apply thread's rest buckets hold after the restore (`srvRest`'s leased arm,
`restLeasesWith` at the snapshot's table). In a log that grants nothing it is the old `hlease`
(`imageLeasesAt_nil`).

Also the two facts S2 needs of the lease table along a prefix of the committed log, one per
lessor mode: monotone, every live lease of the applied log is live at the snapshot's
(`appliedTable_mono_sub`); revocable, an id the applied log granted that the snapshot's table has
is live at the applied log (`appliedTable_granted_live`). They give `lessor.Recover`'s mode and
ever-set premises.

(The S2–S4 Probe, 2026-11-05) Proved, over the table's step lemmas (`kvTable_eq_or`,
`backendTable_cases`): a lease of the table after a log was in the table before or granted in the
log (`kvTableOf_mem`), the table's ids distinct (`kvTableOf_nodup`), and in the monotone mode no
lease leaves it (`kvTableOf_mono`). The two mode facts are stated over the log after the prefix,
which is what the KV invariant speaks of (`kv_log_plain`, `kvGrantIds`), and of each lease, not only
its id (`appliedTable_mono_mem`, `appliedTable_rev_mem`): the lease's request is then the same in
both tables, which `Recover`'s request premise needs.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RestLeased
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyCmpArm
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.MustUnsafeGetAllLeases

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open backend

/-- **The image `D`'s lease bucket holds the records of the live leases of its committed log**
`γr.raft.pre ++ A'` (the receiver's names `γr`, tracked through the parameters `P`): one record per
id of the log's lease table (`appliedTable γr A'`, i.e. `kvLeases γr.kv (γr.raft.pre ++ A')`), each
the record `Grant` writes (`leaseEnc id t 0`), its TTL `f id` for some `f` (TTLs differ per
member: `minLeaseTTL`; at least the table's, the grant's request: the lease-expiry plan's S2–S4,
Q-S6 (A-ii)), and no other record. Stated as `restLeasesWith`'s bucket over the rest
model's (empty) one, as `bkRestAtL` and `srvRest`'s leased arm state theirs. -/
def imageLeasesAt [GooseExts] (γr : ReadNames) (P : BParams) (D : Data) (A' : List EntryModel) :
    Prop :=
  ∃ f : w64 → w64, leaseTTLsGeReq (appliedTable γr A') f ∧ ((rbData P D).lookup go!"lease").getD ∅ =
    ((apply.restLeasesWith f (appliedTable γr A').ids
      (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A'))).bk.lookup go!"lease").getD ∅

/-- **The leased rest image gives the image's lease bucket** (on a real backend, which tracks
every rest bucket): `bkRestAtL` at the receiver's raft log (what `imageAt` states, with
`L = γr.raft.pre ++ A'`). -/
theorem imageLeasesAt_of_bkRestAtL [GooseExts] (d : mvcc.KBReal) {γr : ReadNames}
    {A' : List EntryModel} {D : Data}
    (h : bkRestAtL γr.kv γr.raft.raft.boot (γr.raft.pre ++ A') D) :
    imageLeasesAt γr d.P D A' := by
  obtain ⟨f, hb, hf⟩ := h
  refine ⟨f, hb, ?_⟩
  rw [rbData_real_lookup d D go!"lease" (by decide), hf go!"lease" (by decide)]
  rfl

/-- **In a log whose table is empty, the image's lease bucket is empty** (the old `hlease`). -/
theorem imageLeasesAt_nil [GooseExts] {γr : ReadNames} {P : BParams} {D : Data}
    {A' : List EntryModel} (hn : (appliedTable γr A').ids = []) (h : imageLeasesAt γr P D A') :
    ((rbData P D).lookup go!"lease").getD ∅ = ∅ := by
  obtain ⟨f, -, hf⟩ := h
  rw [hf, hn, apply.restLeasesWith_nil]
  have := restModel_lease γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A')
  exact (congrArg (fun o => Option.getD o ∅) this).trans rfl

/-- **An empty bucket at an empty table** (`imageLeasesAt_nil`'s converse): a cluster that grants
none (review r1 F2). -/
theorem imageLeasesAt_of_nil [GooseExts] {γr : ReadNames} {P : BParams} {D : Data}
    {A' : List EntryModel} (hn : (appliedTable γr A').ids = [])
    (h : ((rbData P D).lookup go!"lease").getD ∅ = ∅) : imageLeasesAt γr P D A' := by
  refine ⟨fun _ => W64 0, leaseTTLsGeReq_of_ids_nil hn _, ?_⟩
  rw [h, hn, apply.restLeasesWith_nil]
  have := restModel_lease γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A')
  exact ((congrArg (fun o => Option.getD o ∅) this).trans rfl).symm

/-! ## The lease table along the log (pure; the S2–S4 Probe, 2026-11-05) -/

section probe
variable [GooseExts]

theorem chainTable_cases (c : apply.Chain) (rq : apply.IRRModel) (lt : LeaseTable) :
    chainTable c rq lt = lt ∨ chainTable c rq lt = backendTable rq lt := by
  induction c with
  | backend => right; rfl
  | auth _ c ih => exact ih
  | quota c ih => exact ih
  | capped c ih =>
    unfold chainTable
    by_cases h : apply.cappedRejects (apply.dispatchKind rq) = true
    · left; simp only [h, ↓reduceIte]
    · simp only [h, Bool.false_eq_true, ↓reduceIte]; exact ih
  | corrupt c ih =>
    unfold chainTable
    by_cases h : apply.corruptRejects (apply.dispatchKind rq) = true
    · left; simp only [h, ↓reduceIte]
    · simp only [h, Bool.false_eq_true, ↓reduceIte]; exact ih

/-- **The backend's table step**: unchanged, a grant's lease appended (its id new), or a revoked
id's lease removed. -/
theorem backendTable_cases (rq : apply.IRRModel) (lt : LeaseTable) :
    backendTable rq lt = lt ∨
    (∃ g : apply.LeaseGrantModel, apply.dispatchKind rq = .leaseGrant ∧ rq.leaseGrant = some g ∧
      g.id ∉ lt.ids ∧ backendTable rq lt = lt ++ [(g.id, g.ttl)]) ∨
    (∃ id : w64, apply.dispatchKind rq = .leaseRevoke ∧
      backendTable rq lt = lt.filter (fun p => p.1 ≠ id)) := by
  by_cases hg : apply.dispatchKind rq = .leaseGrant
  · cases hgg : rq.leaseGrant with
    | none => left; simp [backendTable, hg, hgg]
    | some g =>
      by_cases hok : leaseGrantOk lt g.id g.ttl
      · right; left; exact ⟨g, hg, rfl, hok.2.2, by simp [backendTable, hg, hgg, hok]⟩
      · left; simp [backendTable, hg, hgg, hok]
  · by_cases hr : apply.dispatchKind rq = .leaseRevoke
    · cases hrr : rq.leaseRevoke with
      | none => left; simp [backendTable, hr, hrr]
      | some id =>
        by_cases hm : id ∈ lt.ids
        · right; right; exact ⟨id, hr, by simp [backendTable, hr, hrr, hm]⟩
        · left; simp [backendTable, hr, hrr, hm]
    · left; unfold backendTable; split <;> simp_all

/-- **An entry's table step**: unchanged, or the backend's step of the entry's request. -/
theorem kvTable_eq_or (c0 : w64) (ch : apply.Chain) (lt : LeaseTable) (m : EntryModel) :
    kvTable c0 ch lt m = lt ∨ ∃ rq : apply.IRRModel, m.typ = W32 0 ∧ m.data ≠ [] ∧
      apply.irrDecode m.data = some rq ∧ kvTable c0 ch lt m = backendTable rq lt := by
  by_cases ht : m.typ = W32 0
  · by_cases hd : m.data = []
    · left; simp [kvTable, ht, hd]
    · cases hdec : apply.irrDecode m.data with
      | none => left; simp [kvTable, ht, hd, hdec]
      | some rq =>
        have he : kvTable c0 ch lt m =
            dispatchTable ch rq (decide (uint.Z c0 < uint.Z m.index)) lt := by
          simp [kvTable, ht, hd, hdec]
        rw [he]
        generalize decide (uint.Z c0 < uint.Z m.index) = v3
        by_cases hv : apply.preV3Kind (apply.dispatchKind rq) = true ∨ v3 = false
        · left; unfold dispatchTable; rw [if_pos hv]
        · have he' : dispatchTable ch rq v3 lt = chainTable ch rq lt := by
            unfold dispatchTable; rw [if_neg hv]
          rw [he']
          rcases chainTable_cases ch rq lt with h | h
          · left; exact h
          · right; exact ⟨rq, ht, hd, rfl, h⟩
  · left; unfold kvTable; rw [if_neg ht]

theorem mem_srvGrantLog (L : List EntryModel) (u : w64) :
    u ∈ srvGrantLog L ↔ ∃ e ∈ L, e.data ≠ [] ∧ entryRevGrantId .revocable e = some u := by
  unfold srvGrantLog logRevGrantIds
  simp only [List.mem_filterMap, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨e, ⟨he, hd⟩, hg⟩; exact ⟨e, he, hd, hg⟩
  · rintro ⟨e, he, hd, hg⟩; exact ⟨e, ⟨he, hd⟩, hg⟩

/-- **A lease of the table after `B` was in the table before, or granted in `B`.** -/
theorem kvTableOf_mem (c0 : w64) (ch : apply.Chain) :
    ∀ (B : List EntryModel) (lt : LeaseTable) (q : w64 × w64), q ∈ kvTableOf c0 ch lt B →
      q ∈ lt ∨ q.1 ∈ srvGrantLog B := by
  intro B
  induction B with
  | nil => intro lt q h; left; exact h
  | cons m B ih =>
    intro lt q h
    have h' : q ∈ kvTableOf c0 ch (kvTable c0 ch lt m) B := h
    have hsub : ∀ u, u ∈ srvGrantLog B → u ∈ srvGrantLog (m :: B) := fun u hu => by
      obtain ⟨e, he, hd, hg⟩ := (mem_srvGrantLog B u).1 hu
      exact (mem_srvGrantLog _ u).2 ⟨e, List.mem_cons_of_mem _ he, hd, hg⟩
    rcases ih _ q h' with h1 | h1
    · rcases kvTable_eq_or c0 ch lt m with he | ⟨rq, ht, hd, hdec, he⟩
      · rw [he] at h1; left; exact h1
      · rw [he] at h1
        rcases backendTable_cases rq lt with hb | ⟨g, hk, hg, -, hb⟩ | ⟨id, -, hb⟩
        · rw [hb] at h1; left; exact h1
        · rw [hb] at h1
          rcases List.mem_append.1 h1 with h2 | h2
          · left; exact h2
          · right
            rw [List.mem_singleton] at h2
            subst h2
            refine (mem_srvGrantLog _ _).2 ⟨m, List.mem_cons_self, hd, ?_⟩
            unfold entryRevGrantId rqRevGrantId
            simp [ht, hdec, hk, hg]
        · rw [hb] at h1; left; exact (List.mem_filter.1 h1).1
    · right; exact hsub _ h1

/-- **The table's ids stay distinct.** -/
theorem kvTableOf_nodup (c0 : w64) (ch : apply.Chain) :
    ∀ (B : List EntryModel) (lt : LeaseTable), lt.ids.Nodup → (kvTableOf c0 ch lt B).ids.Nodup := by
  intro B
  induction B with
  | nil => intro lt h; exact h
  | cons m B ih =>
    intro lt h
    apply ih
    rcases kvTable_eq_or c0 ch lt m with he | ⟨rq, -, -, -, he⟩
    · rw [he]; exact h
    · rw [he]
      rcases backendTable_cases rq lt with hb | ⟨g, -, -, hn, hb⟩ | ⟨id, -, hb⟩
      · rw [hb]; exact h
      · rw [hb]
        unfold LeaseTable.ids at h hn ⊢
        simp only [List.map_append, List.map_cons, List.map_nil]
        rw [List.nodup_append]
        refine ⟨h, by simp, ?_⟩
        intro a ha b hb e
        rw [List.mem_singleton] at hb
        subst hb e
        exact hn ha
      · rw [hb]
        exact h.sublist (List.Sublist.map _ List.filter_sublist)

/-- **In the monotone mode no lease leaves the table** (no revocation, X7). -/
theorem kvTableOf_mono (c0 : w64) (ch : apply.Chain) (cmp : Bool) :
    ∀ (B : List EntryModel) (lt : LeaseTable), plainLogM cmp .mono B →
      ∀ p ∈ lt, p ∈ kvTableOf c0 ch lt B := by
  intro B
  induction B with
  | nil => intro lt _ p h; exact h
  | cons m B ih =>
    intro lt hpl p hp
    apply ih _ (fun e he => hpl e (List.mem_cons_of_mem _ he))
    rcases kvTable_eq_or c0 ch lt m with he | ⟨rq, ht, hd, hdec, he⟩
    · rw [he]; exact hp
    · rw [he]
      rcases backendTable_cases rq lt with hb | ⟨g, -, -, -, hb⟩ | ⟨id, hk, hb⟩
      · rw [hb]; exact hp
      · rw [hb]; exact List.mem_append_left _ hp
      · exfalso
        rcases hpl m List.mem_cons_self ht hd rq hdec with h | h | h | h
        · have := h.2; rw [hk] at this; simp [putgetKind] at this
        · rw [h.2.1.1] at hk; cases hk
        · rw [h.2.1] at hk; cases hk
        · cases h.1

theorem appliedTable_append (γr : ReadNames) (A B : List EntryModel) :
    appliedTable γr (A ++ B) = kvTableOf γr.kv.c0 γr.kv.ch0 (appliedTable γr A) B := by
  unfold appliedTable kvLeases kvTableOf
  rw [← List.append_assoc, List.foldl_append]

theorem appliedTable_nodup (γr : ReadNames) (A : List EntryModel) :
    (appliedTable γr A).ids.Nodup :=
  kvTableOf_nodup _ _ _ [] List.nodup_nil

/-- **Two leases of one table with one id are one.** -/
theorem table_eq_of_id {T : LeaseTable} (hn : T.ids.Nodup) {p q : w64 × w64} (hp : p ∈ T)
    (hq : q ∈ T) (h : p.1 = q.1) : p = q := by
  induction T with
  | nil => cases hp
  | cons a T ih =>
    simp only [LeaseTable.ids, List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.1 hp with rfl | hp' <;> rcases List.mem_cons.1 hq with rfl | hq'
    · rfl
    · exact (hn.1 (h ▸ List.mem_map.2 ⟨q, hq', rfl⟩)).elim
    · exact (hn.1 (h.symm ▸ List.mem_map.2 ⟨p, hp', rfl⟩)).elim
    · exact ih hn.2 hp' hq'

/-- **A lease of the snapshot's table is granted in its log** (with an empty prefix). -/
theorem appliedTable_ids_granted (γr : ReadNames) (hpre : γr.raft.pre = []) (A' : List EntryModel)
    (u : w64) (hu : u ∈ (appliedTable γr A').ids) : u ∈ srvGrantLog A' := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hu
  have hq' : q ∈ kvTableOf γr.kv.c0 γr.kv.ch0 [] A' := by
    have : appliedTable γr A' = kvTableOf γr.kv.c0 γr.kv.ch0 [] A' := by
      unfold appliedTable kvLeases; rw [hpre, List.nil_append]
    rw [← this]; exact hq
  rcases kvTableOf_mem _ _ A' [] q hq' with h | h
  · cases h
  · exact h

/-- **The image's lease bucket is `Recover`'s records** (`lease.lessor.Recover.spec`'s `recs`): its
entries in key order are `leaseRecEnc` of some records whose ids are the snapshot's table's, as a
permutation (review r1 F15: `Recover`'s `Lr.Perm`; the bucket's keys are distinct, and so are the
table's ids, `leaseGrantOk`), each with remaining TTL `0`, each record's TTL at least its table
entry's (the grant's request: `Recover`'s `reqOf` premise, Q-S6 (A-ii)). -/
theorem imageLeasesAt_recs {γr : ReadNames} {P : BParams} {D : Data}
    {A' : List EntryModel} (h : imageLeasesAt γr P D A') :
    ∃ recs : List (w64 × w64 × w64),
      bktEnts (((rbData P D).lookup go!"lease").getD ∅) = recs.map lease.leaseRecEnc ∧
      (recs.map (·.1)).Perm (appliedTable γr A').ids ∧
      (∀ x ∈ recs, x.2.2 = W64 0) ∧
      ∀ x ∈ recs, ∀ p ∈ appliedTable γr A', p.1 = x.1 → sint.Z p.2 ≤ sint.Z x.2.1 := by
  obtain ⟨f, hf, hb⟩ := h
  generalize hT : appliedTable γr A' = T at hf hb ⊢
  generalize hr0 : restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A') = r0 at hb
  have hr0l : (r0.bk.lookup mvcc.leaseName) = some ∅ := by
    rw [← hr0]; exact restModel_lease _ _ _
  have hTn : T.ids.Nodup := hT ▸ appliedTable_nodup γr A'
  generalize hbk : ((rbData P D).lookup go!"lease").getD ∅ = bk at hb ⊢
  have hbk' : bk = (((apply.restLeasesWith f T.ids r0).bk.lookup mvcc.leaseName).getD ∅) := hb
  -- the bucket's entries: each a record of an id of the table, and each id's record there
  have hput : ∀ (id t : w64) (r : apply.RestM),
      ((apply.restGrantT id t r).bk.lookup mvcc.leaseName).getD ∅ =
        GMap.insert (apply.leaseKey id) (lease.leaseEnc id t (W64 0))
          ((r.bk.lookup mvcc.leaseName).getD ∅) := by
    intro id t r
    unfold apply.restGrantT apply.RestM.putIn
    simp only
    rw [GMap.lookup_insert]; rfl
  have hin : ∀ (ids : List w64) (r : apply.RestM) (k v : GoString),
      ((apply.restLeasesWith f ids r).bk.lookup mvcc.leaseName).getD ∅ !! k = some v →
      ((r.bk.lookup mvcc.leaseName).getD ∅) !! k = some v ∨
        ∃ id ∈ ids, k = apply.leaseKey id ∧ v = lease.leaseEnc id (f id) (W64 0) := by
    intro ids
    induction ids with
    | nil => intro r k v h; left; exact h
    | cons id0 ids ih =>
      intro r k v h
      rcases ih (apply.restGrantT id0 (f id0) r) k v h with h1 | ⟨id, hid, hk, hv⟩
      · rw [hput] at h1
        rcases (GMap.lookup_insert_Some _ _ _ _ _).1 h1 with ⟨hk, hv⟩ | ⟨-, h2⟩
        · right; exact ⟨id0, List.mem_cons_self, hk.symm, hv.symm⟩
        · left; exact h2
      · right; exact ⟨id, List.mem_cons_of_mem _ hid, hk, hv⟩
  have hhas : ∀ (ids : List w64) (r : apply.RestM) (id : w64),
      ((apply.restLeasesWith f ids r).bk.lookup mvcc.leaseName).getD ∅ !! apply.leaseKey id =
        if id ∈ ids then some (lease.leaseEnc id (f id) (W64 0))
        else ((r.bk.lookup mvcc.leaseName).getD ∅) !! apply.leaseKey id := by
    intro ids
    induction ids with
    | nil => intro r id; rw [apply.restLeasesWith_nil, if_neg List.not_mem_nil]
    | cons id0 ids ih =>
      intro r id
      have e1 : apply.restLeasesWith f (id0 :: ids) r =
          apply.restLeasesWith f ids (apply.restGrantT id0 (f id0) r) := by
        unfold apply.restLeasesWith; rfl
      rw [e1, ih, hput]
      by_cases h1 : id ∈ ids
      · simp [h1]
      · by_cases h2 : id = id0
        · subst h2; simp [h1, GMap.lookup_insert]
        · have hk : apply.leaseKey id0 ≠ apply.leaseKey id := by
            intro e; apply h2; unfold apply.leaseKey at e
            exact (u64Le_inj (List.reverse_inj.1 e)).symm
          rw [if_neg h1, if_neg (by simp [h1, h2]), GMap.lookup_insert_ne _ _ hk]
  have hent : ∀ e ∈ bktEnts bk, ∃ x : w64 × w64 × w64,
      (x.1 ∈ T.ids ∧ x.2.1 = f x.1 ∧ x.2.2 = W64 0) ∧ e = lease.leaseRecEnc x := by
    intro e he
    have he' : e ∈ bk.toList := (List.mergeSort_perm _ _).mem_iff.1 he
    have hl : bk !! e.1 = some e.2 := (GMap.mem_toList bk e.1 e.2).1 he'
    rw [hbk'] at hl
    rcases hin T.ids r0 e.1 e.2 hl with h1 | ⟨id, hid, hk, hv⟩
    · rw [hr0l] at h1; cases h1
    · exact ⟨(id, f id, W64 0), ⟨hid, rfl, rfl⟩, by
        obtain ⟨e1, e2⟩ := e; simp only at hk hv; subst hk hv; rfl⟩
  have hchoose : ∀ L : List Ent, (∀ e ∈ L, ∃ x : w64 × w64 × w64,
      (x.1 ∈ T.ids ∧ x.2.1 = f x.1 ∧ x.2.2 = W64 0) ∧ e = lease.leaseRecEnc x) →
      ∃ xs : List (w64 × w64 × w64), L = xs.map lease.leaseRecEnc ∧
        ∀ x ∈ xs, x.1 ∈ T.ids ∧ x.2.1 = f x.1 ∧ x.2.2 = W64 0 := by
    intro L
    induction L with
    | nil => intro _; exact ⟨[], rfl, fun _ h => absurd h List.not_mem_nil⟩
    | cons e L ih =>
      intro hL
      obtain ⟨x, hx, rfl⟩ := hL e List.mem_cons_self
      obtain ⟨xs, hxs, hP⟩ := ih (fun e he => hL e (List.mem_cons_of_mem _ he))
      refine ⟨x :: xs, by rw [hxs]; rfl, fun y hy => ?_⟩
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hx
      · exact hP y hy
  obtain ⟨recs, hrecs, hP⟩ := hchoose (bktEnts bk) hent
  refine ⟨recs, hrecs, ?_, fun x hx => (hP x hx).2.2, ?_⟩
  · have hn1 := lease.leaseRecs_nodup bk recs hrecs
    refine (List.perm_ext_iff_of_nodup hn1 hTn).2 (fun id => ⟨fun h => ?_, fun h => ?_⟩)
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
      exact (hP x hx).1
    · have hl : bk !! apply.leaseKey id = some (lease.leaseEnc id (f id) (W64 0)) := by
        rw [hbk', hhas, if_pos h]
      have he : (apply.leaseKey id, lease.leaseEnc id (f id) (W64 0)) ∈ bktEnts bk :=
        (List.mergeSort_perm _ _).mem_iff.2 ((GMap.mem_toList _ _ _).2 hl)
      rw [hrecs] at he
      obtain ⟨x, hx, hxe⟩ := List.mem_map.1 he
      have : x.1 = id := by
        have := congrArg Prod.fst hxe
        simp only [lease.leaseRecEnc] at this
        unfold apply.leaseKey at this
        exact u64Le_inj (List.reverse_inj.1 this)
      exact List.mem_map.2 ⟨x, hx, this⟩
  · intro x hx p hp hpx
    rw [(hP x hx).2.1, ← hpx]
    exact hf p hp

/-- **S2, the monotone mode: every live lease of the applied log is live at the snapshot's**: along
a prefix of a committed log that is plain in the monotone mode (no revocation: the lease-expiry
plan's X7, a revocation exists only in the revocable mode), the lease table only grows. What
`Recover`'s monotone premise (`mono = true → ∀ id ∈ L, id ∈ recs.map (·.1)`) takes, with the
lessor's live set the applied table (`ltHalf`). (S2–S4 Probe: the log after the prefix `A'`, the
KV invariant's `kv_log_plain`, in place of `γr.raft.pre ++ A'`; and each lease, not only its id.) -/
theorem appliedTable_mono_mem (γr : ReadNames) {A A' : List EntryModel}
    (hpre : A <+: A') (hpl : plainLogM γr.kv.cmp .mono A') :
    ∀ p ∈ appliedTable γr A, p ∈ appliedTable γr A' := by
  obtain ⟨B, rfl⟩ := hpre
  rw [appliedTable_append]
  exact kvTableOf_mono _ _ _ B _ (fun e he => hpl e (List.mem_append_right _ he))

theorem appliedTable_mono_sub (γr : ReadNames) {A A' : List EntryModel}
    (hpre : A <+: A') (hpl : plainLogM γr.kv.cmp .mono A') :
    ∀ id ∈ (appliedTable γr A).ids, id ∈ (appliedTable γr A').ids := by
  intro id h
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
  exact List.mem_map.2 ⟨p, appliedTable_mono_mem γr hpre hpl p hp, rfl⟩

/-- **S2, the revocable mode: a lease of the snapshot's table whose id the applied log granted is a
lease of the applied table**: with the grant ids of the log distinct (`kvGrantIds`'s fact, E3
(b)), a revoked id is never granted again, so an id of `srvGrantLog A` (the apply thread's ever-set
bound, `srvEverOk`) live at the longer log `A'` was not revoked within `A`, and its lease is the
one `A` granted (its request the same). (S2–S4 Probe: the log after the prefix, `srvGrantLog A'`,
in place of `γr.raft.pre ++ A'`.) -/
theorem appliedTable_rev_mem (γr : ReadNames) {A A' : List EntryModel}
    (hpre : A <+: A') (hnd : (srvGrantLog A').Nodup) (q : w64 × w64)
    (hu : q.1 ∈ srvGrantLog A) (hq : q ∈ appliedTable γr A') : q ∈ appliedTable γr A := by
  obtain ⟨B, rfl⟩ := hpre
  rw [appliedTable_append] at hq
  rcases kvTableOf_mem _ _ B _ q hq with h | h
  · exact h
  · exfalso
    have he : srvGrantLog (A ++ B) = srvGrantLog A ++ srvGrantLog B := by
      unfold srvGrantLog logRevGrantIds; rw [List.filter_append, List.filterMap_append]
    rw [he] at hnd
    exact (List.nodup_append.1 hnd).2.2 _ hu _ h rfl

theorem appliedTable_granted_live (γr : ReadNames) {A A' : List EntryModel}
    (hpre : A <+: A') (hnd : (srvGrantLog A').Nodup) (u : w64)
    (hu : u ∈ srvGrantLog A) (hu' : u ∈ (appliedTable γr A').ids) :
    u ∈ (appliedTable γr A).ids := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hu'
  exact List.mem_map.2 ⟨q, appliedTable_rev_mem γr hpre hnd q hu hq, rfl⟩


end probe

end EtcdGrove
end Perennial
