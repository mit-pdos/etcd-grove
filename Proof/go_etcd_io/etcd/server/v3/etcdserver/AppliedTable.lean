/-
**The applied log's lease table** (the lease-grant stage, 2026-11-02; `notes/lease-grant-plan.md`,
"Design of the server chain", 2.0): `appliedTable γr A`, the KV model's lease table of the raft
node's prefix `γr.raft.pre` (`RNNames.pre`) and the applied entries `A`, folded from the empty
table: the live ids the leased rest image (`srvRest`'s leased arm) and the tie's halves (`ltHalf`)
are at. Lean-first (no Rocq counterpart). The KV model's own table folds over `A` alone; the two
agree where the prefix is empty (`kvLeases_pre`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRequest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.GrantRest

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

/-- **The lease table of the applied log** `A`, after the raft node's prefix. -/
def appliedTable [GooseExts] (γr : ReadNames) (A : List EntryModel) : LeaseTable :=
  kvLeases γr.kv (γr.raft.pre ++ A)

/-- **An empty prefix grants nothing** (m-a): the table of the prefix alone is empty. -/
theorem kvLeases_pre [GooseExts] (γr : ReadNames) (h : γr.raft.pre = []) :
    (kvLeases γr.kv γr.raft.pre).ids = [] := by
  rw [h]; rfl

/-! ## The table one entry later (the lease-grant stage, 2.0's ids law; amendment (C)) -/

theorem appliedTable_snoc [GooseExts] (γr : ReadNames) (A : List EntryModel) (m : EntryModel) :
    appliedTable γr (A ++ [m]) = kvTable γr.kv.c0 γr.kv.ch0 (appliedTable γr A) m := by
  unfold appliedTable kvLeases; rw [← List.append_assoc, kvTableOf_snoc]

/-- A grant is no cluster request. -/
theorem dispatchKind_leaseGrant_noCluster (rq : apply.IRRModel)
    (hk : apply.dispatchKind rq = .leaseGrant) :
    rq.clusterVersionSet = none ∧ rq.clusterMemberAttrSet = none := by
  constructor
  · cases h : rq.clusterVersionSet with
    | none => rfl
    | some _ => simp [apply.dispatchKind, h] at hk
  · cases h : rq.clusterMemberAttrSet with
    | none => rfl
    | some _ =>
      cases h' : rq.clusterVersionSet <;> simp [apply.dispatchKind, h, h'] at hk

theorem leaseGrantOk_iff (lt : LeaseTable) (id ttl : w64) :
    leaseGrantOk lt id ttl ↔ apply.grantIdsOk lt.ids id ttl := Iff.rfl

/-- **Neither a grant nor a revocation leaves the table**, whatever the chain. -/
theorem chainTable_nonLease (c : apply.Chain) (rq : apply.IRRModel) (lt : LeaseTable)
    (hg : apply.dispatchKind rq ≠ .leaseGrant) (hr : apply.dispatchKind rq ≠ .leaseRevoke) :
    chainTable c rq lt = lt := by
  induction c with
  | backend =>
    unfold chainTable backendTable
    split
    · rename_i h; exact absurd h hg
    · rename_i h; exact absurd h hr
    · rfl
  | auth _ c ih => exact ih
  | quota c ih => exact ih
  | capped c ih => unfold chainTable; split <;> first | rfl | exact ih
  | corrupt c ih => unfold chainTable; split <;> first | rfl | exact ih

/-- **A grant's table**: appended when the chain lets it through and the lessor's condition holds. -/
theorem chainTable_grant (c : apply.Chain) (rq : apply.IRRModel) (g : apply.LeaseGrantModel)
    (lt : LeaseTable) (hk : apply.dispatchKind rq = .leaseGrant) (hg : rq.leaseGrant = some g) :
    chainTable c rq lt =
      if apply.grantGoes c rq = true ∧ leaseGrantOk lt g.id g.ttl then lt ++ [(g.id, g.ttl)] else lt := by
  induction c with
  | backend =>
    simp only [chainTable, backendTable, hk, hg, apply.grantGoes, true_and]
  | auth _ c ih => exact ih
  | quota c ih => exact ih
  | capped c =>
    simp [chainTable, hk, apply.cappedRejects, apply.grantGoes]
  | corrupt c =>
    simp [chainTable, hk, apply.corruptRejects, apply.grantGoes]

/-- **The ids law** (2.0, under amendment (C)'s `grantOutOk`): the table `dispatch` leaves, of a
request that revokes nothing, has the ids `grantIds` gives. -/
theorem chainTable_grantNone (c : apply.Chain) (rq : apply.IRRModel) (lt : LeaseTable)
    (hk : apply.dispatchKind rq = .leaseGrant) (hgl : rq.leaseGrant = none) :
    chainTable c rq lt = lt := by
  induction c with
  | backend => simp only [chainTable, backendTable, hk, hgl]
  | auth _ c ih => exact ih
  | quota c ih => exact ih
  | capped c ih => unfold chainTable; split <;> first | rfl | exact ih
  | corrupt c ih => unfold chainTable; split <;> first | rfl | exact ih

theorem dispatchTable_ids (c : apply.Chain) (rq : apply.IRRModel) (v3 : Bool) (lt : LeaseTable)
    (o : apply.Outcome) (hr : apply.dispatchKind rq ≠ .leaseRevoke)
    (hgo : apply.grantOutOk c rq v3 lt.ids o) :
    (dispatchTable c rq v3 lt).ids = apply.grantIds rq v3 o lt.ids := by
  by_cases hk : apply.dispatchKind rq = .leaseGrant
  · have hpre : apply.preV3Kind (apply.dispatchKind rq) = false := by rw [hk]; rfl
    cases v3
    · simp [dispatchTable, apply.grantIds_noV3]
    · cases hgl : rq.leaseGrant with
      | none =>
        rw [apply.grantIds_none _ _ _ _ hgl]
        simp only [dispatchTable, hpre, Bool.false_eq_true, false_or, ↓reduceIte]
        rw [chainTable_grantNone c rq lt hk hgl]
        simp
      | some g =>
        have h := hgo hk rfl g hgl
        simp only [dispatchTable, hpre, Bool.false_eq_true, false_or, ↓reduceIte]
        rw [chainTable_grant c rq g lt hk hgl]
        cases o with
        | applied l ns =>
          rw [apply.grantIds_applied rq g l ns _ hk hgl]
          have hc : apply.grantGoes c rq = true ∧ leaseGrantOk lt g.id g.ttl := h.1 ⟨l, ns, rfl⟩
          rw [if_pos hc]
          simp [LeaseTable.ids]
        | rejected e =>
          rw [apply.grantIds_rejected]
          have hc : ¬ (apply.grantGoes c rq = true ∧ leaseGrantOk lt g.id g.ttl) :=
            fun hc => by obtain ⟨l, ns, he⟩ := h.2 hc; cases he
          simp only [Bool.true_eq_false, ↓reduceIte, hc]
  · rw [apply.grantIds_nonGrant _ _ _ _ hk]
    unfold dispatchTable
    split
    · rfl
    · rw [chainTable_nonLease c rq lt hk hr]

/-- **The ids law over `Apply`'s outcome**: a request that revokes nothing, a grant one the apply
thread admits (so dispatched, `grantKindOk`), at the chain the model's. -/
theorem dispatchTableA_ids (rq : apply.IRRModel) (v3 : Bool) (x x' : apply.ApplyKV)
    (out : apply.ApplyOut) (lt : LeaseTable) (hr : apply.dispatchKind rq ≠ .leaseRevoke)
    (hg : apply.dispatchKind rq = .leaseGrant → apply.grantKindOk rq)
    (hs : apply.applyStep rq v3 x x' out) (hgo : apply.grantOutOkA x.chain rq v3 lt.ids out) :
    (dispatchTable x.chain rq v3 lt).ids = apply.grantIdsA rq v3 out lt.ids := by
  cases out with
  | dispatched o sk => exact dispatchTable_ids x.chain rq v3 lt o hr hgo
  | skipped =>
    have hk : apply.dispatchKind rq ≠ .leaseGrant := fun hk => by
      have := (hg hk).2.2.1; rw [hs.1] at this; cases this
    show _ = lt.ids
    rw [dispatchTable_ids x.chain rq v3 lt (.rejected .backend) hr
      (apply.grantOutOk_nonGrant _ _ _ _ _ hk), apply.grantIds_rejected]
  | rejected =>
    have hk : apply.dispatchKind rq ≠ .leaseGrant := fun hk => by
      have := (hg hk).2.1; rw [hs.1] at this; cases this
    show _ = lt.ids
    rw [dispatchTable_ids x.chain rq v3 lt (.rejected .backend) hr
      (apply.grantOutOk_nonGrant _ _ _ _ _ hk), apply.grantIds_rejected]

/-- **The TTL bound one request later** (the lease-expiry plan's S2–S4, Q-S6 (A-ii)): the table
`dispatch` leaves, of a request that revokes nothing, keeps `leaseTTLsGeReq` at TTLs `f'` that are
the old ones' on the table and the record's `t` (at least the request's, `grantTTLOk`) at an id the
grant added. -/
theorem dispatchTable_ttls (c : apply.Chain) (rq : apply.IRRModel) (v3 : Bool) (lt : LeaseTable)
    (o : apply.Outcome) (hr : apply.dispatchKind rq ≠ .leaseRevoke)
    (hgo : apply.grantOutOk c rq v3 lt.ids o) (f' : w64 → w64) (t : w64)
    (hlt : leaseTTLsGeReq lt f') (htt : apply.grantTTLOk rq t)
    (hnew : ∀ id ∈ apply.grantIds rq v3 o lt.ids, id ∉ lt.ids → f' id = t) :
    leaseTTLsGeReq (dispatchTable c rq v3 lt) f' := by
  by_cases hk : apply.dispatchKind rq = .leaseGrant
  · have hpre : apply.preV3Kind (apply.dispatchKind rq) = false := by rw [hk]; rfl
    cases v3
    · simpa [dispatchTable] using hlt
    · cases hgl : rq.leaseGrant with
      | none =>
        simp only [dispatchTable, hpre, Bool.false_eq_true, false_or, ↓reduceIte]
        rw [chainTable_grantNone c rq lt hk hgl]
        exact hlt
      | some g =>
        have h := hgo hk rfl g hgl
        simp only [dispatchTable, hpre, Bool.false_eq_true, false_or, ↓reduceIte]
        rw [chainTable_grant c rq g lt hk hgl]
        cases o with
        | applied l ns =>
          have hc : apply.grantGoes c rq = true ∧ leaseGrantOk lt g.id g.ttl := h.1 ⟨l, ns, rfl⟩
          rw [if_pos hc]
          have hf : f' g.id = t := hnew g.id
            (by rw [apply.grantIds_applied rq g l ns _ hk hgl]; simp) hc.2.2.2
          intro p hp
          rcases List.mem_append.1 hp with hp | hp
          · exact hlt p hp
          · simp at hp; subst hp; simp only; rw [hf]; exact htt g hgl
        | rejected e =>
          have hc : ¬ (apply.grantGoes c rq = true ∧ leaseGrantOk lt g.id g.ttl) :=
            fun hc => by obtain ⟨l, ns, he⟩ := h.2 hc; cases he
          rw [if_neg hc]; exact hlt
  · unfold dispatchTable
    split
    · exact hlt
    · rw [chainTable_nonLease c rq lt hk hr]; exact hlt

/-- **The TTL bound over `Apply`'s outcome** (as `dispatchTableA_ids`). -/
theorem dispatchTableA_ttls (rq : apply.IRRModel) (v3 : Bool) (x x' : apply.ApplyKV)
    (out : apply.ApplyOut) (lt : LeaseTable) (hr : apply.dispatchKind rq ≠ .leaseRevoke)
    (hg : apply.dispatchKind rq = .leaseGrant → apply.grantKindOk rq)
    (hs : apply.applyStep rq v3 x x' out) (hgo : apply.grantOutOkA x.chain rq v3 lt.ids out)
    (f' : w64 → w64) (t : w64) (hlt : leaseTTLsGeReq lt f') (htt : apply.grantTTLOk rq t)
    (hnew : ∀ id ∈ apply.grantIdsA rq v3 out lt.ids, id ∉ lt.ids → f' id = t) :
    leaseTTLsGeReq (dispatchTable x.chain rq v3 lt) f' := by
  cases out with
  | dispatched o sk => exact dispatchTable_ttls x.chain rq v3 lt o hr hgo f' t hlt htt hnew
  | skipped =>
    have hk : apply.dispatchKind rq ≠ .leaseGrant := fun hk => by
      have := (hg hk).2.2.1; rw [hs.1] at this; cases this
    exact dispatchTable_ttls x.chain rq v3 lt (.rejected .backend) hr
      (apply.grantOutOk_nonGrant _ _ _ _ _ hk) f' t hlt htt
      (fun id h hn => by rw [apply.grantIds_rejected] at h; exact absurd h hn)
  | rejected =>
    have hk : apply.dispatchKind rq ≠ .leaseGrant := fun hk => by
      have := (hg hk).2.1; rw [hs.1] at this; cases this
    exact dispatchTable_ttls x.chain rq v3 lt (.rejected .backend) hr
      (apply.grantOutOk_nonGrant _ _ _ _ _ hk) f' t hlt htt
      (fun id h hn => by rw [apply.grantIds_rejected] at h; exact absurd h hn)

/-- **A request that grants nothing adds no entry** (a revocation removes one, anything else none). -/
theorem chainTable_sub_nonGrant (c : apply.Chain) (rq : apply.IRRModel) (lt : LeaseTable)
    (hk : apply.dispatchKind rq ≠ .leaseGrant) : ∀ p ∈ chainTable c rq lt, p ∈ lt := by
  induction c with
  | backend =>
    intro p hp
    unfold chainTable backendTable at hp
    split at hp
    · rename_i h; exact absurd h hk
    · split at hp
      · split at hp
        · exact (List.mem_filter.1 hp).1
        · exact hp
      · exact hp
    · exact hp
  | auth _ c ih => exact ih
  | quota c ih => exact ih
  | capped c ih =>
    intro p hp; unfold chainTable at hp; split at hp
    · exact hp
    · exact ih p hp
  | corrupt c ih =>
    intro p hp; unfold chainTable at hp; split at hp
    · exact hp
    · exact ih p hp

theorem dispatchTable_sub_nonGrant (c : apply.Chain) (rq : apply.IRRModel) (v3 : Bool)
    (lt : LeaseTable) (hk : apply.dispatchKind rq ≠ .leaseGrant) :
    ∀ p ∈ dispatchTable c rq v3 lt, p ∈ lt := by
  intro p hp
  unfold dispatchTable at hp
  split at hp
  · exact hp
  · exact chainTable_sub_nonGrant c rq lt hk p hp

/-- **The table's entries one request later** (the lease-expiry plan's S2–S4, F7, DRAFT
2026-11-05): of a request that revokes nothing, the old table's and an applied grant's. -/
theorem dispatchTable_mem (c : apply.Chain) (rq : apply.IRRModel) (v3 : Bool) (lt : LeaseTable)
    (o : apply.Outcome) (hr : apply.dispatchKind rq ≠ .leaseRevoke)
    (hgo : apply.grantOutOk c rq v3 lt.ids o) (p : w64 × w64) (hp : p ∈ dispatchTable c rq v3 lt) :
    p ∈ lt ∨ (apply.dispatchKind rq = .leaseGrant ∧ v3 = true ∧ ∃ g : apply.LeaseGrantModel,
      rq.leaseGrant = some g ∧ p = (g.id, g.ttl) ∧ ∃ l ns, o = .applied l ns) := by
  by_cases hk : apply.dispatchKind rq = .leaseGrant
  · have hpre : apply.preV3Kind (apply.dispatchKind rq) = false := by rw [hk]; rfl
    cases v3
    · left; simpa [dispatchTable] using hp
    · cases hgl : rq.leaseGrant with
      | none =>
        left
        simp only [dispatchTable, hpre, Bool.false_eq_true, false_or, ↓reduceIte] at hp
        rwa [chainTable_grantNone c rq lt hk hgl] at hp
      | some g =>
        have h := hgo hk rfl g hgl
        simp only [dispatchTable, hpre, Bool.false_eq_true, false_or, ↓reduceIte] at hp
        rw [chainTable_grant c rq g lt hk hgl] at hp
        by_cases hc : apply.grantGoes c rq = true ∧ leaseGrantOk lt g.id g.ttl
        · rw [if_pos hc] at hp
          rcases List.mem_append.1 hp with hp | hp
          · exact .inl hp
          · simp at hp
            exact .inr ⟨hk, rfl, g, rfl, hp, h.2 hc⟩
        · rw [if_neg hc] at hp; exact .inl hp
  · exact .inl (dispatchTable_sub_nonGrant c rq v3 lt hk p hp)

/-- **`dispatchTable_mem` over `Apply`'s outcome** (as `dispatchTableA_ids`). -/
theorem dispatchTableA_mem (rq : apply.IRRModel) (v3 : Bool) (x x' : apply.ApplyKV)
    (out : apply.ApplyOut) (lt : LeaseTable) (hr : apply.dispatchKind rq ≠ .leaseRevoke)
    (hg : apply.dispatchKind rq = .leaseGrant → apply.grantKindOk rq)
    (hs : apply.applyStep rq v3 x x' out) (hgo : apply.grantOutOkA x.chain rq v3 lt.ids out)
    (p : w64 × w64) (hp : p ∈ dispatchTable x.chain rq v3 lt) :
    p ∈ lt ∨ (apply.dispatchKind rq = .leaseGrant ∧ v3 = true ∧ ∃ g : apply.LeaseGrantModel,
      rq.leaseGrant = some g ∧ p = (g.id, g.ttl) ∧
      ∃ o sk l ns, out = .dispatched o sk ∧ o = .applied l ns) := by
  cases out with
  | dispatched o sk =>
    rcases dispatchTable_mem x.chain rq v3 lt o hr hgo p hp with h | ⟨hk, hv, g, hgl, hpg, l, ns, ho⟩
    · exact .inl h
    · exact .inr ⟨hk, hv, g, hgl, hpg, o, sk, l, ns, rfl, ho⟩
  | skipped =>
    have hk : apply.dispatchKind rq ≠ .leaseGrant := fun hk => by
      have := (hg hk).2.2.1; rw [hs.1] at this; cases this
    exact .inl (dispatchTable_sub_nonGrant _ rq v3 lt hk p hp)
  | rejected =>
    have hk : apply.dispatchKind rq ≠ .leaseGrant := fun hk => by
      have := (hg hk).2.1; rw [hs.1] at this; cases this
    exact .inl (dispatchTable_sub_nonGrant _ rq v3 lt hk p hp)

/-- The table after a normal entry with no data, or a conf change: unchanged. -/
theorem appliedTable_nodata [GooseExts] (γr : ReadNames) (A : List EntryModel) (m : EntryModel)
    (ht : m.typ = W32 0) (hd : m.data = []) : appliedTable γr (A ++ [m]) = appliedTable γr A := by
  rw [appliedTable_snoc]; unfold kvTable; rw [if_pos ht, if_pos hd]

theorem appliedTable_cc [GooseExts] (γr : ReadNames) (A : List EntryModel) (m : EntryModel)
    (ht : m.typ ≠ W32 0) : appliedTable γr (A ++ [m]) = appliedTable γr A := by
  rw [appliedTable_snoc]; unfold kvTable; rw [if_neg ht]

/-- After a normal entry whose request neither grants nor revokes: unchanged. -/
theorem appliedTable_nonLease [GooseExts] (γr : ReadNames) (A : List EntryModel) (m : EntryModel)
    (rq : apply.IRRModel) (ht : m.typ = W32 0) (hd : m.data ≠ [])
    (hdec : apply.irrDecode m.data = some rq) (hg : apply.dispatchKind rq ≠ .leaseGrant)
    (hr : apply.dispatchKind rq ≠ .leaseRevoke) :
    appliedTable γr (A ++ [m]) = appliedTable γr A := by
  rw [appliedTable_snoc]; unfold kvTable; rw [if_pos ht, if_neg hd]
  simp only [hdec, dispatchTable]
  split
  · rfl
  · exact chainTable_nonLease _ rq _ hg hr

end EtcdGrove
end Perennial
