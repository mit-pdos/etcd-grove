/-
**The apply thread's compaction arm** (M2's apply side, 2026-10-31, the user's (a): the snapshot
track's `srvEnvOkD` in place, so a compaction entry reaches `applyEntryNormal` in the cluster's
compaction mode). The facts `applyEntryNormal`'s proof needs of a committed entry that is a covered
request or a compaction in M2's scope (`plainOrCmp`): the certificates `Apply` asks
(`kv_certPre_M`), the rest buckets after it (`srvRest_apply_M`), the KV state after it
(`batchStep_plainM`), its result's error not `ErrNoSpace`'s at the start's chain
(`applyResultIs_notNoSpace_M`); and a compaction's facts (`cmpAdmit`) from the KV invariant's claims
(`kv_entry_claim`, S3-3's transfer, `cmpEntryOk_transfer`; `cmpAdmit_of_entry`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVApply
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NoSpaceDead
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.DispatchLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [GooseExts]

/-- **A covered request or a compaction in M2's scope**: what a committed entry plain in the mode
decodes to. -/
def plainOrCmp (rq : apply.IRRModel) : Prop := plainCover rq ∨ compactPropOk rq

theorem plainOrCmp_of_entryM (cmp : Bool) (m : EntryModel) (h : plainEntryM cmp .none m)
    (ht : m.typ = W32 0) (hd : m.data ≠ []) (rq : apply.IRRModel)
    (hdec : apply.irrDecode m.data = some rq) : plainOrCmp rq := by
  rcases plainEntryM_lg_false cmp m h ht hd rq hdec with h | ⟨-, h⟩
  · exact Or.inl h.1
  · exact Or.inr h

/-- Neither skipped nor rejected: `Apply`'s rest-bucket effect is `dispatch`'s. -/
theorem restOut_plainOrCmp (rq : apply.IRRModel) (v3 : Bool) (x x' : apply.ApplyKV)
    (out : apply.ApplyOut) (r : apply.RestM) (hp : plainOrCmp rq)
    (h : apply.applyStep rq v3 x x' out) :
    apply.restOut rq v3 out r = apply.restAfter rq v3 r := by
  rcases hp with hp | hc
  · exact restOut_plain rq v3 x x' out r hp h
  · cases out with
    | skipped => exact absurd h.1 (by rw [hc.2.1]; decide)
    | rejected => exact absurd h.1 (by rw [hc.2.2]; decide)
    | dispatched o skip => rfl

/-- **`Apply` on a compaction keeps the chain and the KV's log.** -/
theorem applyStep_cmp (rq : apply.IRRModel) (hc : compactPropOk rq) (v3 : Bool)
    (x x' : apply.ApplyKV) (out : apply.ApplyOut) (h : apply.applyStep rq v3 x x' out) :
    x'.chain = x.chain ∧ x'.log = x.log := by
  have hk := hc.1.1
  cases out with
  | skipped => rw [h.2]; exact ⟨rfl, rfl⟩
  | rejected => rw [h.2]; exact ⟨rfl, rfl⟩
  | dispatched o skip =>
    obtain ⟨-, hd, hl, hch, -⟩ := h
    refine ⟨?_, ?_⟩
    · rcases hch with h | ⟨-, hka, -⟩
      · exact h
      · rw [hk] at hka; cases hka
    · rw [hl]
      unfold apply.dispatchStep at hd
      simp only [hk, apply.preV3Kind, apply.storeKind, Bool.false_eq_true, _root_.false_or,
        ↓reduceIte] at hd
      split at hd
      · rw [hd]; rfl
      · exact apply.chainStep_cmp_log rq hk hc.2.2 x.log x.chain o hd

/-- A compaction entry leaves the model's log. -/
theorem kvEntry_cmp (c₀ : w64) (ch : apply.Chain) (lt : LeaseTable) (log : mvcc.Log)
    (m : EntryModel) (rq : apply.IRRModel) (hdec : apply.irrDecode m.data = some rq)
    (hc : compactPropOk rq) : kvEntry c₀ ch lt log m = log :=
  kvEntry_nonwrite _ _ _ _ m (Or.inr (Or.inr fun rq' h => by
    rw [hdec] at h; cases h; exact compactPropOk_nonwrite rq hc))

/-- **A raft entry's step on an entry plain in the mode**, at a `kvExact` chain: the chain
unchanged and the log as `kvEntry` says (a compaction: unchanged). -/
theorem batchStep_plainM (c₀ : w64) (lt : LeaseTable) (cmp : Bool) (m : EntryModel)
    (x x' : apply.ApplyKV) (hp : plainEntryM cmp .none m) (hoff : x.chain.kvExact = true)
    (h : batchStep c₀ m x x') :
    x'.chain = x.chain ∧ x'.log = kvEntry c₀ x.chain lt x.log m := by
  by_cases hcm : ∃ rq, m.typ = W32 0 ∧ m.data ≠ [] ∧ apply.irrDecode m.data = some rq ∧
      compactPropOk rq
  · obtain ⟨rq, ht, hd, hdec, hc⟩ := hcm
    rw [kvEntry_cmp c₀ x.chain lt x.log m rq hdec hc]
    unfold batchStep at h
    rw [if_pos ht] at h
    obtain ⟨out, h⟩ := h
    unfold entryStep at h
    rw [if_neg hd] at h
    obtain ⟨rq', id, hdec', -, h⟩ := h
    rw [hdec] at hdec'
    cases hdec'
    exact applyStep_cmp rq hc _ x x' out h
  · have hpl : plainEntry m := by
      intro ht hd rq hdec
      rcases plainEntryM_lg_false cmp m hp ht hd rq hdec with h | ⟨-, hc⟩
      · exact h
      · exact absurd ⟨rq, ht, hd, hdec, hc⟩ hcm
    exact batchStep_plain c₀ lt m x x' hpl hoff h

/-- **A compaction dispatched at the start's chain is applied** (the chain reaches the backend). -/
theorem dispatchStep_start_cmp (rq : apply.IRRModel) (hc : compactPropOk rq) (log : mvcc.Log)
    (o : apply.Outcome) (h : apply.dispatchStep (apply.alarmChain false false false) rq true log o) :
    o = .applied log false := by
  have hk := hc.1.1
  have hna := hc.2.2
  unfold apply.dispatchStep at h
  simp only [hk, apply.preV3Kind, apply.storeKind, Bool.false_eq_true, _root_.false_or,
    _root_.or_false, ↓reduceIte] at h
  simp [apply.alarmChain, apply.baseChain, apply.chainStep, apply.authChecks, apply.cappedRejects,
    apply.corruptRejects, apply.backendStep, hk, hna] at h
  exact h

/-- **The transfer (S3-3, item 8), pure**: a committed log `A ++ [m]` whose requested entries are
a prefix of the server's log `L`'s (no fillers in `L`) gets the entry's claim from `L`'s claims:
`m`, if a compaction, is one of `L`'s entries, at the position after the prefix `A'` of `L` with
`A`'s requested entries, and the model of `A'` is `A`'s (`kvModel_eqv`). -/
theorem cmpEntryOk_transfer (γ : ServerRaftNames) (γk : KVNames) (cmp : Bool)
    (A L : List EntryModel) (m : EntryModel)
    (hAm : srvIdxOkW γ.ai0 (A ++ [m])) (hL : srvIdxOkW γ.ai0 L)
    (hnf : ∀ e ∈ L, ¬ e.toLE.isFiller ∧ ¬ e.toLE.isEmptyV2)
    (h : opsOf ((A ++ [m]).map EntryModel.toLE) <+: L.map EntryModel.toLE)
    (hc : uint.Z γk.c0 ≤ uint.Z γ.ai0) (hcl : cmpLogOk γk cmp L) :
    cmpEntryOk γk cmp A m := by
  intro ht hd rq hdec hk
  have hA : srvIdxOkW γ.ai0 A := srvIdxOkW_prefix _ A _ hAm (List.prefix_append _ _)
  have hf : ¬ m.toLE.isFiller := fun hf => hd hf.1
  have hv : ¬ m.toLE.isEmptyV2 := fun hv => by
    have h2 : m.typ = W32 2 := hv.2
    rw [ht] at h2; exact absurd h2 (by decide)
  have hops : opsOf ((A ++ [m]).map EntryModel.toLE) =
      opsOf (A.map EntryModel.toLE) ++ [m.toLE] := by
    rw [List.map_append, opsOf_append]
    simp [opsOf, hf, hv]
  rw [hops] at h
  -- the prefix of `L` with `A`'s requested entries, and the entry after it
  obtain ⟨A', hA'L, hAA'⟩ := srv_eqv_prefix γ A L hA hL hnf
    ((List.prefix_append _ _).trans h)
  have hA'nf : ∀ x ∈ A'.map EntryModel.toLE, ¬ x.isFiller ∧ ¬ x.isEmptyV2 := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact hnf y (hA'L.subset hy)
  have hlen : (opsOf (A.map EntryModel.toLE)).length = A'.length := by
    rw [hAA'.2.2, opsOf_nofill _ hA'nf, List.length_map]
  have hA'eq : A' = L.take A'.length := List.prefix_iff_eq_take.1 hA'L
  obtain ⟨t, htl⟩ := h
  have hget : (L.map EntryModel.toLE)[A'.length]? = some m.toLE := by
    rw [← htl, List.append_assoc, List.getElem?_append_right (by omega), ← hlen, Nat.sub_self]
    rfl
  rw [List.getElem?_map, Option.map_eq_some_iff] at hget
  obtain ⟨m', hm', he⟩ := hget
  have h1 := congrArg LogEntry.type he
  have h2 := congrArg LogEntry.data he
  simp only [EntryModel.toLE] at h1 h2
  have := hcl A'.length m' hm' (h1 ▸ ht) (h2 ▸ hd) rq (h2 ▸ hdec) hk
  rw [← hA'eq, ← (kvModel_eqv γ γk A A' hAA' hc).1] at this
  exact this


/-! ### The lease-grant stage's M1 lemmas at `lg` (commit 4): a grant beside the plain requests -/

/-- **A covered request, a compaction in M2's scope, or a grant the cluster admits** (the
lease-grant stage, §2.9's `srvRest_applyG` premise): what a committed entry plain in the modes
`cmp`, `lg` decodes to; (the lease-expiry plan's X7) or a revocation in the revocable mode
(`revokePropOk`). At `lg = false`, `plainOrCmp`. -/
def plainOrCmpG (lm : lease.Mode) (rq : apply.IRRModel) : Prop :=
  plainOrCmp rq ∨ grantPropOk lm rq ∨ revokePropOk lm rq

theorem plainOrCmpG_of_entryM (cmp : Bool) (lm : lease.Mode) (m : EntryModel) (h : plainEntryM cmp lm m)
    (ht : m.typ = W32 0) (hd : m.data ≠ []) (rq : apply.IRRModel)
    (hdec : apply.irrDecode m.data = some rq) : plainOrCmpG lm rq := by
  rcases h ht hd rq hdec with h | ⟨-, h⟩ | h | h
  · exact Or.inl (Or.inl h.1)
  · exact Or.inl (Or.inr h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- A grant the cluster admits is neither skipped nor rejected: `Apply`'s rest-bucket effect is
`dispatch`'s. -/
theorem restOut_grant (rq : apply.IRRModel) (v3 : Bool) (x x' : apply.ApplyKV)
    (out : apply.ApplyOut) (r : apply.RestM) (hg : apply.grantKindOk rq)
    (h : apply.applyStep rq v3 x x' out) :
    apply.restOut rq v3 out r = apply.restAfter rq v3 r := by
  cases out with
  | skipped => exact absurd h.1 (by rw [hg.2.2.1]; decide)
  | rejected => exact absurd h.1 (by rw [hg.2.1]; decide)
  | dispatched o skip => rfl

/-- A revocation the cluster admits is neither skipped nor rejected (as `restOut_grant`). -/
theorem restOut_revoke (rq : apply.IRRModel) (v3 : Bool) (x x' : apply.ApplyKV)
    (out : apply.ApplyOut) (r : apply.RestM) (hr : apply.revokeKindOk rq)
    (h : apply.applyStep rq v3 x x' out) :
    apply.restOut rq v3 out r = apply.restAfter rq v3 r := by
  cases out with
  | skipped => exact absurd h.1 (by rw [hr.2.2]; decide)
  | rejected => exact absurd h.1 (by rw [hr.2.1]; decide)
  | dispatched o skip => rfl

theorem restOut_plainOrCmpG (lm : lease.Mode) (rq : apply.IRRModel) (v3 : Bool) (x x' : apply.ApplyKV)
    (out : apply.ApplyOut) (r : apply.RestM) (hp : plainOrCmpG lm rq)
    (h : apply.applyStep rq v3 x x' out) :
    apply.restOut rq v3 out r = apply.restAfter rq v3 r := by
  rcases hp with hp | hg | hr
  · exact restOut_plainOrCmp rq v3 x x' out r hp h
  · exact restOut_grant rq v3 x x' out r hg.2 h
  · exact restOut_revoke rq v3 x x' out r hr.2 h

/-- **A lease-free state has no lease's keys** (`leaseDels` is `[]`). -/
theorem leaseDels_leaseZero (s : List EtcdKv) (hs : mvcc.LeaseZero s) (id : w64) :
    mvcc.leaseDels s id = [] := by
  unfold mvcc.leaseDels mvcc.leaseDelKeys
  split
  · rfl
  · rename_i h0
    rw [List.filter_eq_nil_iff.2 (fun v hv => by
      rw [hs v hv]; simp only [decide_eq_true_eq]; exact fun e => h0 e.symm)]
    rfl

/-- The model's revocation deletes nothing of a lease-free state, `0` aside. -/
theorem revokeChanges_leaseZero (s : List EtcdKv) (hs : mvcc.LeaseZero s) (id : w64)
    (h0 : id ≠ W64 0) : revokeChanges s id = [] := by
  unfold revokeChanges
  rw [List.filter_eq_nil_iff.2 (fun v hv => by
    rw [hs v hv]; simp only [decide_eq_true_eq]; exact fun e => h0 e.symm)]
  rfl

/-- **A revocation's step through the chain keeps a lease-free log** (its deletions, `leaseDels`,
are none). -/
theorem chainStep_revoke_logAfter (rq : apply.IRRModel) (hk : apply.dispatchKind rq = .leaseRevoke)
    (log : mvcc.Log) (hz : mvcc.LeaseZero (mvcc.stateAfter log)) :
    ∀ (c : apply.Chain) (o : apply.Outcome), apply.chainStep apply.backendStep c rq log o →
      o.logAfter log = log
  | .backend, o, h => by
    simp only [apply.chainStep, apply.backendStep, hk] at h
    obtain ⟨id, -, rfl⟩ := h
    show mvcc.commitLog log _ = log
    rw [leaseDels_leaseZero _ hz id]; rfl
  | .auth _ c, o, h => by
    simp only [apply.chainStep] at h
    split at h
    · rcases h with ⟨-, rfl⟩ | h
      · rfl
      · exact chainStep_revoke_logAfter rq hk log hz c o h
    · exact chainStep_revoke_logAfter rq hk log hz c o h
  | .quota c, o, h => by
    simp only [apply.chainStep] at h
    exact chainStep_revoke_logAfter rq hk log hz c o h
  | .capped c, o, h => by
    simp only [apply.chainStep, apply.cappedRejects, hk, Bool.false_eq_true, ↓reduceIte,
      reduceCtorEq] at h
    exact chainStep_revoke_logAfter rq hk log hz c o h
  | .corrupt c, o, h => by
    simp only [apply.chainStep] at h
    split at h
    · subst h; rfl
    · exact chainStep_revoke_logAfter rq hk log hz c o h

/-- **`Apply` on a revocation keeps the chain and a lease-free log**. -/
theorem applyStep_revoke (rq : apply.IRRModel) (hr : apply.revokeKindOk rq) (v3 : Bool)
    (x x' : apply.ApplyKV) (out : apply.ApplyOut) (hz : mvcc.LogNoLease x.log)
    (h : apply.applyStep rq v3 x x' out) :
    x'.chain = x.chain ∧ x'.log = x.log := by
  have hk := hr.1
  cases out with
  | skipped => rw [h.2]; exact ⟨rfl, rfl⟩
  | rejected => rw [h.2]; exact ⟨rfl, rfl⟩
  | dispatched o skip =>
    obtain ⟨-, hd, hl, hch, -⟩ := h
    refine ⟨?_, ?_⟩
    · rcases hch with h | ⟨-, hka, -⟩
      · exact h
      · rw [hk] at hka; cases hka
    · rw [hl]
      unfold apply.dispatchStep at hd
      split at hd
      · rw [hd]; rfl
      · rw [if_pos (Or.inl (by rw [hk]; rfl))] at hd
        exact chainStep_revoke_logAfter rq hk x.log (mvcc.stateAfter_leaseZero _ hz) x.chain o hd

/-- A revocation entry leaves a lease-free model's log, at a table without `0`. -/
theorem kvEntry_revoke (c₀ : w64) (ch : apply.Chain) (lt : LeaseTable) (log : mvcc.Log)
    (m : EntryModel) (rq : apply.IRRModel) (hdec : apply.irrDecode m.data = some rq)
    (hr : apply.revokeKindOk rq) (hz : mvcc.LogNoLease log) (h0 : W64 0 ∉ lt.ids) :
    kvEntry c₀ ch lt log m = log := by
  have hs := mvcc.stateAfter_leaseZero _ hz
  have hb : backendLog lt rq log = log := by
    unfold backendLog
    rw [hr.1]
    dsimp only
    split
    · rename_i id _
      split
      · rename_i hm
        have : id ≠ W64 0 := fun e => h0 (e ▸ hm)
        rw [revokeChanges_leaseZero _ hs id this]; rfl
      · rfl
    · rfl
  have hc : ∀ c : apply.Chain, chainLog c rq lt log = log := by
    intro c
    induction c with
    | backend => exact hb
    | corrupt c ih => simp only [chainLog]; split <;> first | rfl | exact ih
    | capped c ih => simp only [chainLog]; split <;> first | rfl | exact ih
    | auth _ c ih => exact ih
    | quota c ih => exact ih
  unfold kvEntry
  split
  · split
    · rfl
    · simp only [hdec]
      unfold dispatchLog
      split
      · rfl
      · split
        · exact hc ch
        · rfl
  · rfl

/-- **`Apply` on a grant keeps the chain and the KV's log** (a grant writes no revision,
`chainStep_grant_logAfter`; it is no alarm request). -/
theorem applyStep_grant (rq : apply.IRRModel) (hg : apply.grantKindOk rq) (v3 : Bool)
    (x x' : apply.ApplyKV) (out : apply.ApplyOut) (h : apply.applyStep rq v3 x x' out) :
    x'.chain = x.chain ∧ x'.log = x.log := by
  have hk := hg.1
  cases out with
  | skipped => rw [h.2]; exact ⟨rfl, rfl⟩
  | rejected => rw [h.2]; exact ⟨rfl, rfl⟩
  | dispatched o skip =>
    obtain ⟨-, hd, hl, hch, -⟩ := h
    refine ⟨?_, ?_⟩
    · rcases hch with h | ⟨-, hka, -⟩
      · exact h
      · rw [hk] at hka; cases hka
    · rw [hl]
      unfold apply.dispatchStep at hd
      split at hd
      · rw [hd]; rfl
      · rw [if_pos (Or.inr hk)] at hd
        exact apply.chainStep_grant_logAfter rq hk x.log x.chain o hd

/-- A grant entry leaves the model's log (a grant is no write). -/
theorem kvEntry_grant (c₀ : w64) (ch : apply.Chain) (lt : LeaseTable) (log : mvcc.Log)
    (m : EntryModel) (rq : apply.IRRModel) (hdec : apply.irrDecode m.data = some rq)
    (hg : apply.grantKindOk rq) : kvEntry c₀ ch lt log m = log := by
  unfold kvEntry
  split
  · split
    · rfl
    · simp only [hdec]
      unfold dispatchLog
      simp [hg.1, apply.storeKind]
  · rfl

/-- **`batchStep_plainM` at `lg`**: a raft entry's step on an entry plain in the modes, at a
`kvExact` chain: the chain unchanged and the log as `kvEntry` says (a compaction or a grant:
unchanged). -/
theorem batchStep_plainMG (c₀ : w64) (lt : LeaseTable) (cmp : Bool) (lm : lease.Mode) (m : EntryModel)
    (x x' : apply.ApplyKV) (hp : plainEntryM cmp lm m) (hoff : x.chain.kvExact = true)
    (hz : mvcc.LogNoLease x.log) (h0 : W64 0 ∉ lt.ids)
    (h : batchStep c₀ m x x') :
    x'.chain = x.chain ∧ x'.log = kvEntry c₀ x.chain lt x.log m := by
  by_cases hrm : ∃ rq, m.typ = W32 0 ∧ m.data ≠ [] ∧ apply.irrDecode m.data = some rq ∧
      revokePropOk lm rq
  · obtain ⟨rq, ht, hd, hdec, hr⟩ := hrm
    rw [kvEntry_revoke c₀ x.chain lt x.log m rq hdec hr.2 hz h0]
    unfold batchStep at h
    rw [if_pos ht] at h
    obtain ⟨out, h⟩ := h
    unfold entryStep at h
    rw [if_neg hd] at h
    obtain ⟨rq', id, hdec', -, h⟩ := h
    rw [hdec] at hdec'
    cases hdec'
    exact applyStep_revoke rq hr.2 _ x x' out hz h
  by_cases hgm : ∃ rq, m.typ = W32 0 ∧ m.data ≠ [] ∧ apply.irrDecode m.data = some rq ∧
      grantPropOk lm rq
  · obtain ⟨rq, ht, hd, hdec, hg⟩ := hgm
    rw [kvEntry_grant c₀ x.chain lt x.log m rq hdec hg.2]
    unfold batchStep at h
    rw [if_pos ht] at h
    obtain ⟨out, h⟩ := h
    unfold entryStep at h
    rw [if_neg hd] at h
    obtain ⟨rq', id, hdec', -, h⟩ := h
    rw [hdec] at hdec'
    cases hdec'
    exact applyStep_grant rq hg.2 _ x x' out h
  · have hpl : plainEntryM cmp .none m := by
      intro ht hd rq hdec
      rcases hp ht hd rq hdec with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact absurd ⟨rq, ht, hd, hdec, h⟩ hgm
      · exact absurd ⟨rq, ht, hd, hdec, h⟩ hrm
    exact batchStep_plainM c₀ lt cmp m x x' hpl hoff h


/-! ### A revocation's rest (the lease-expiry plan's X7) -/

theorem leaseKey_ne (a id : w64) (h : a ≠ id) : apply.leaseKey a ≠ apply.leaseKey id := by
  intro e; apply h; unfold apply.leaseKey at e; exact u64Le_inj (List.reverse_inj.1 e)

/-- Deleting a record commutes with putting another's. -/
theorem restRevoke_grantT_ne (id a t : w64) (r : apply.RestM) (h : a ≠ id) :
    apply.restRevoke id (apply.restGrantT a t r) = apply.restGrantT a t (apply.restRevoke id r) := by
  have hk := leaseKey_ne a id h
  cases r with
  | mk bk mem =>
    simp only [apply.restRevoke, apply.restGrantT, apply.RestM.delIn, apply.RestM.putIn,
      apply.RestM.mk.injEq, and_true]
    apply GMap.ext; intro n
    by_cases hn : mvcc.leaseName = n
    · subst hn
      simp only [GMap.lookup_insert_eq_iff, ↓reduceIte, Option.getD_some]
      congr 1
      apply GMap.ext; intro k
      simp only [GMap.lookup_insert_eq_iff, GMap.lookup_delete_iff]
      by_cases h1 : apply.leaseKey id = k
      · subst h1; simp [hk]
      · simp [h1]
    · simp only [GMap.lookup_insert_eq_iff, hn, ↓reduceIte]

/-- Deleting a record undoes putting it. -/
theorem restRevoke_grantT_eq (id t : w64) (r : apply.RestM) :
    apply.restRevoke id (apply.restGrantT id t r) = apply.restRevoke id r := by
  cases r with
  | mk bk mem =>
    simp only [apply.restRevoke, apply.restGrantT, apply.RestM.delIn, apply.RestM.putIn,
      apply.RestM.mk.injEq, and_true]
    apply GMap.ext; intro n
    by_cases hn : mvcc.leaseName = n
    · subst hn
      simp only [GMap.lookup_insert_eq_iff, ↓reduceIte, Option.getD_some]
      congr 1
      apply GMap.ext; intro k
      simp only [GMap.lookup_insert_eq_iff, GMap.lookup_delete_iff]
      by_cases h1 : apply.leaseKey id = k <;> simp [h1]
    · simp only [GMap.lookup_insert_eq_iff, hn, ↓reduceIte]

/-- **A revocation's delete over the records** (the commutation, any base). -/
theorem restRevoke_leasesWith (id : w64) (f : w64 → w64) :
    ∀ (T : List w64) (r : apply.RestM), apply.restRevoke id (apply.restLeasesWith f T r) =
      apply.restLeasesWith f (T.filter (· != id)) (apply.restRevoke id r)
  | [], r => rfl
  | a :: T, r => by
    have hc : apply.restLeasesWith f (a :: T) r =
        apply.restLeasesWith f T (apply.restGrantT a (f a) r) := rfl
    rw [hc, restRevoke_leasesWith id f T]
    by_cases h : a = id
    · subst h
      rw [restRevoke_grantT_eq]
      simp
    · rw [restRevoke_grantT_ne id a (f a) r h]
      have : (a :: T).filter (· != id) = a :: T.filter (· != id) := by
        simp [List.filter_cons, h]
      rw [this]; rfl

/-- **The model's rest holds no lease record** (the `lease` bucket the boot's, empty, an entry
changing other buckets only). -/
theorem restModel_lease [GooseExts] (c0 : w64) (b : List EntryM) (L : List EntryModel) :
    (restModel c0 b L).bk.lookup mvcc.leaseName = some ∅ := by
  unfold restModel
  have h0 : (restBoot b).bk.lookup mvcc.leaseName = some ∅ := by
    simp [restBoot, restBootBk, mvcc.leaseName, go_etcd_io.etcd.server.v3.storage.schema.leaseName]
  generalize restBoot b = r0 at h0
  induction L generalizing r0 with
  | nil => exact h0
  | cons m L ih =>
    rw [List.foldl_cons]
    exact ih _ (by
      rw [restEntry_keep c0 m _ _ (by simp [mvcc.leaseName,
        go_etcd_io.etcd.server.v3.storage.schema.leaseName]) (by simp [mvcc.leaseName,
        go_etcd_io.etcd.server.v3.storage.schema.leaseName]) (by simp [mvcc.leaseName,
        go_etcd_io.etcd.server.v3.storage.schema.leaseName])]
      exact h0)

/-- The delete of a record the model's rest lacks leaves it. -/
theorem restRevoke_restModel [GooseExts] (id c0 : w64) (b : List EntryM) (L : List EntryModel) :
    apply.restRevoke id (restModel c0 b L) = restModel c0 b L := by
  have h := restModel_lease c0 b L
  generalize restModel c0 b L = r at h ⊢
  cases r with
  | mk bk mem =>
    simp only [apply.restRevoke, apply.RestM.delIn, apply.RestM.mk.injEq, and_true]
    simp only at h
    apply GMap.ext; intro n
    by_cases hn : mvcc.leaseName = n
    · subst hn
      simp only [GMap.lookup_insert_eq_iff, ↓reduceIte, h, Option.getD_some]
      congr 1
      apply GMap.ext; intro k
      simp only [GMap.lookup_delete_iff]
      split <;> rfl
    · simp only [GMap.lookup_insert_eq_iff, hn, ↓reduceIte]

/-- **A revocation dispatched at the start's chain** (with `v3`): applied (the auth layer, off,
does not reject it; the backend applies it). -/
theorem dispatchStep_start_revoke (rq : apply.IRRModel) (hr : apply.revokeKindOk rq)
    (log : mvcc.Log) (o : apply.Outcome)
    (h : apply.dispatchStep (apply.alarmChain false false false) rq true log o) :
    ∃ l ns, o = .applied l ns := by
  obtain ⟨hk, hna, -⟩ := hr
  unfold apply.dispatchStep at h
  rw [if_neg (by simp [hk, apply.preV3Kind]), if_pos (Or.inl (by rw [hk]; rfl))] at h
  simp only [apply.alarmChain, apply.baseChain, apply.chainStep, apply.authChecks, hk,
    Bool.false_eq_true, ↓reduceIte, apply.backendStep, true_or] at h
  rcases h with ⟨hm, -⟩ | ⟨id, -, rfl⟩
  · exfalso
    unfold apply.authMayReject at hm
    rcases hm with h | h | h
    · cases h
    · rw [hna] at h; cases h
    · exact h.2.2.2.2 hk
  · exact ⟨_, _, rfl⟩

end pure

section arm
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The certificates `Apply` asks of an entry's request**, covered or a compaction (whose
outcomes keep the log, certified as the entry's model log). -/
theorem kv_certPre_M (E : apply.AEnv GF) (γk : KVNames) (hγ : E.γ.cok = γk.cok) (c₀ : w64)
    (lt : LeaseTable) (x : apply.ApplyKV) (m : EntryModel) (rq : apply.IRRModel) (v3 : Bool)
    (hp : plainOrCmp rq) (hoff : x.chain.kvExact = true) (ht : m.typ = W32 0) (hd : m.data ≠ [])
    (hdec : apply.irrDecode m.data = some rq) (hv : v3 = decide (uint.Z c₀ < uint.Z m.index)) :
    kvCert (GF := GF) γk (kvEntry c₀ x.chain lt x.log m) ⊢ apply.certPreV v3 E x.chain rq x.log := by
  rcases hp with hp | hc
  · exact kv_certPre E γk hγ c₀ lt x m rq v3 hp hoff ht hd hdec hv
  rw [kvEntry_cmp c₀ x.chain lt x.log m rq hdec hc]
  iintro #Hc
  cases v3
  · simp only [apply.certPreV, Bool.false_eq_true, ↓reduceIte]; itrivial
  · simp only [apply.certPreV, ↓reduceIte]
    unfold apply.certPre
    imodintro
    iintro %oc %hs
    rw [apply.chainStep_cmp_log rq hc.1.1 hc.2.2 x.log x.chain oc hs]
    iapply kvCert_certOk γk E.γ hγ $$ Hc

theorem plainOrCmp_nonLease (rq : apply.IRRModel) (hp : plainOrCmp rq) :
    apply.dispatchKind rq ≠ .leaseGrant ∧ apply.dispatchKind rq ≠ .leaseRevoke := by
  rcases hp with hp | hc
  · unfold plainCover at hp
    constructor <;> intro hk <;> rw [hk] at hp <;> exact hp.elim
  · rw [hc.1.1]; exact ⟨by decide, by decide⟩

open Iris.ProofMode in
/-- **`srvRest` one entry later, a covered request or a compaction** (`srvRest_applyG` at a request
that neither grants nor revokes). -/
theorem srvRest_applyP (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) (m : EntryModel)
    (rq : apply.IRRModel) (v3 : Bool) (x x' : apply.ApplyKV) (out : apply.ApplyOut) (f : w64 → w64)
    (ht : m.typ = W32 0) (hd : m.data ≠ []) (hdec : apply.irrDecode m.data = some rq)
    (hv3 : v3 = decide (uint.Z γr.kv.c0 < uint.Z m.index)) (hch : x.chain = γr.kv.ch0)
    (hp : plainOrCmp rq) (hs : apply.applyStep rq v3 x x' out)
    (hfb : E.lg = true → leaseTTLsGeReq (appliedTable γr A) f) :
    srvGrantIf E ∗ srvReqsIf E (appliedTable γr A) ∗ grantReqA E rq v3 out ∗
      ⌜apply.grantOutOkA x.chain rq v3 (srvIds E (appliedTable γr A).ids) out⌝ ∗
      apply.ltHalf E (apply.grantIdsA rq v3 out (srvIds E (appliedTable γr A).ids)) ∗
      (∃ t : w64, ⌜apply.grantTTLOk rq t⌝ ∗ E.RO (apply.grantRestA t rq v3 out (apply.restOut rq v3 out
        (apply.restLeasesWith f (srvIds E (appliedTable γr A).ids)
          (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)))))) ∗
      srvEver E (A ++ [m]) ⊢
      srvRest E γr (A ++ [m]) :=
  have hk := plainOrCmp_nonLease rq hp
  srvRest_applyG E γr A m rq v3 x x' out f ht hd hdec hv3 hch hk.2 (fun h => absurd h hk.1)
    (fun r => restOut_plainOrCmp rq v3 x x' out r hp hs) hs hfb

/-- `srvRest_applyP` for a triple whose post carries no grant conjuncts (`kvSpecL`'s): a plain
request or a compaction grants nothing, so its ids, its rest and `grantOutOkA` are the identity's. -/
theorem srvRest_applyP0 (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) (m : EntryModel)
    (rq : apply.IRRModel) (v3 : Bool) (x x' : apply.ApplyKV) (out : apply.ApplyOut) (f : w64 → w64)
    (ht : m.typ = W32 0) (hd : m.data ≠ []) (hdec : apply.irrDecode m.data = some rq)
    (hv3 : v3 = decide (uint.Z γr.kv.c0 < uint.Z m.index)) (hch : x.chain = γr.kv.ch0)
    (hp : plainOrCmp rq) (hs : apply.applyStep rq v3 x x' out)
    (hfb : E.lg = true → leaseTTLsGeReq (appliedTable γr A) f) :
    srvGrantIf E ∗ srvReqsIf E (appliedTable γr A) ∗ apply.ltHalf E (srvIds E (appliedTable γr A).ids) ∗
      E.RO (apply.restOut rq v3 out
        (apply.restLeasesWith f (srvIds E (appliedTable γr A).ids)
          (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)))) ∗
      srvEver E (A ++ [m]) ⊢
      srvRest E γr (A ++ [m]) := by
  have hk := (plainOrCmp_nonLease rq hp).1
  iintro ⟨HGI, HRq, HLt, HR, HU⟩
  iapply srvRest_applyP E γr A m rq v3 x x' out f ht hd hdec hv3 hch hp hs hfb
  iframe HGI HRq HU
  isplitl []
  · iapply grantReqA_nonGrant E rq v3 out hk
  isplitl []
  · ipureintro
    cases out with
    | dispatched o _ => exact apply.grantOutOk_nonGrant _ _ _ _ _ hk
    | _ => trivial
  rw [apply.grantIdsA_nonGrant _ _ _ _ hk]
  iframe HLt
  iexists (apply.grantTTLW rq)
  isplitr
  · ipureintro; exact apply.grantTTLOk_w rq
  rw [apply.grantRestA_nonGrant _ _ _ _ _ hk]
  iexact HR

/-- **Its permits give a covered request's or a compaction's** (`grantPermRq`, vacuous). -/
theorem srvGrantIf_permP [go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions] (E : apply.AEnv GF) (rq : apply.IRRModel) (hp : plainOrCmp rq) :
    srvGrantIf E ⊢ apply.grantPermRq E rq :=
  srvGrantIf_perm E rq (fun h => absurd h (plainOrCmp_nonLease rq hp).1)

theorem plainOrCmpG_rev (lm : lease.Mode) (rq : apply.IRRModel)
    (hp : plainOrCmp rq ∨ grantPropOk lm rq) :
    apply.dispatchKind rq ≠ .leaseRevoke := by
  rcases hp with hp | hg
  · exact (plainOrCmp_nonLease rq hp).2
  · rw [hg.2.1]; decide

theorem plainOrCmpG_grant (lm : lease.Mode) (rq : apply.IRRModel) (hp : plainOrCmpG lm rq) :
    apply.dispatchKind rq = .leaseGrant → grantPropOk lm rq := by
  intro hk
  rcases hp with hp | hg | hr
  · exact absurd hk (plainOrCmp_nonLease rq hp).1
  · exact hg
  · rw [hr.2.1] at hk; cases hk

/-- **Not a revocation, the grant's form** (`plainOrCmpG` without its revocation disjunct). -/
theorem plainOrCmpG_nonRev (lm : lease.Mode) (rq : apply.IRRModel) (hp : plainOrCmpG lm rq)
    (hk : apply.dispatchKind rq ≠ .leaseRevoke) : plainOrCmp rq ∨ grantPropOk lm rq := by
  rcases hp with hp | hg | hr
  · exact Or.inl hp
  · exact Or.inr hg
  · exact absurd hr.2.1 hk

/-- **No revocation, the live set and the rest as the grant's** (the lease-expiry plan's X7): a
request not dispatched as a revocation leaves `revokeIdsA`/`revokeRestA` the identity. -/
theorem revokeA_drop (E : apply.AEnv GF) (rq : apply.IRRModel) (v3 : Bool) (out : apply.ApplyOut)
    (L T : List w64) (R : w64 → apply.RestM) (hk : apply.dispatchKind rq ≠ .leaseRevoke) :
    apply.ltHalf E (apply.revokeIdsA rq v3 out L) ∗
      (∃ t : w64, ⌜apply.grantTTLOk rq t⌝ ∗ E.RO (apply.revokeRestA T rq v3 out (R t))) ⊢
      apply.ltHalf E L ∗ ∃ t : w64, ⌜apply.grantTTLOk rq t⌝ ∗ E.RO (R t) := by
  rw [apply.revokeIdsA_nonRevoke _ _ _ _ hk]
  simp only [apply.revokeRestA_nonRevoke _ _ _ _ _ hk]
  iintro H; iexact H

/-- **`kv_certPre_M` at `lm`**: a grant's outcomes keep the log (`chainStep_grant_logAfter`),
certified as the entry's model log (`kvEntry_grant`). -/
theorem kv_certPre_G (E : apply.AEnv GF) (γk : KVNames) (hγ : E.γ.cok = γk.cok) (c₀ : w64)
    (lt : LeaseTable) (x : apply.ApplyKV) (m : EntryModel) (rq : apply.IRRModel) (v3 : Bool) (lm : lease.Mode)
    (hp : plainOrCmpG lm rq) (hoff : x.chain.kvExact = true) (ht : m.typ = W32 0) (hd : m.data ≠ [])
    (hdec : apply.irrDecode m.data = some rq) (hv : v3 = decide (uint.Z c₀ < uint.Z m.index))
    (hz : mvcc.LogNoLease x.log) (h0 : W64 0 ∉ lt.ids) :
    kvCert (GF := GF) γk (kvEntry c₀ x.chain lt x.log m) ⊢ apply.certPreV v3 E x.chain rq x.log := by
  rcases hp with hp | hg | hr
  · exact kv_certPre_M E γk hγ c₀ lt x m rq v3 hp hoff ht hd hdec hv
  rotate_left
  · rw [kvEntry_revoke c₀ x.chain lt x.log m rq hdec hr.2 hz h0]
    iintro #Hc
    cases v3
    · simp only [apply.certPreV, Bool.false_eq_true, ↓reduceIte]; itrivial
    · simp only [apply.certPreV, ↓reduceIte]
      unfold apply.certPre
      imodintro
      iintro %oc %hs
      rw [chainStep_revoke_logAfter rq hr.2.1 x.log (mvcc.stateAfter_leaseZero _ hz) x.chain oc hs]
      iapply kvCert_certOk γk E.γ hγ $$ Hc
  rw [kvEntry_grant c₀ x.chain lt x.log m rq hdec hg.2]
  iintro #Hc
  cases v3
  · simp only [apply.certPreV, Bool.false_eq_true, ↓reduceIte]; itrivial
  · simp only [apply.certPreV, ↓reduceIte]
    unfold apply.certPre
    imodintro
    iintro %oc %hs
    rw [apply.chainStep_grant_logAfter rq hg.2.1 x.log x.chain oc hs]
    iapply kvCert_certOk γk E.γ hγ $$ Hc

open Iris.ProofMode in
/-- **`srvRest_applyP` at `lm`**: a covered request, a compaction, or a grant the cluster admits. -/
theorem srvRest_applyPG (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) (m : EntryModel)
    (rq : apply.IRRModel) (v3 : Bool) (x x' : apply.ApplyKV) (out : apply.ApplyOut) (f : w64 → w64)
    (ht : m.typ = W32 0) (hd : m.data ≠ []) (hdec : apply.irrDecode m.data = some rq)
    (hv3 : v3 = decide (uint.Z γr.kv.c0 < uint.Z m.index)) (hch : x.chain = γr.kv.ch0)
    (hp : plainOrCmp rq ∨ grantPropOk E.lm rq) (hs : apply.applyStep rq v3 x x' out)
    (hfb : E.lg = true → leaseTTLsGeReq (appliedTable γr A) f) :
    srvGrantIf E ∗ srvReqsIf E (appliedTable γr A) ∗ grantReqA E rq v3 out ∗
      ⌜apply.grantOutOkA x.chain rq v3 (srvIds E (appliedTable γr A).ids) out⌝ ∗
      apply.ltHalf E (apply.grantIdsA rq v3 out (srvIds E (appliedTable γr A).ids)) ∗
      (∃ t : w64, ⌜apply.grantTTLOk rq t⌝ ∗ E.RO (apply.grantRestA t rq v3 out (apply.restOut rq v3 out
        (apply.restLeasesWith f (srvIds E (appliedTable γr A).ids)
          (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)))))) ∗
      srvEver E (A ++ [m]) ⊢
      srvRest E γr (A ++ [m]) :=
  have hp' : plainOrCmpG E.lm rq := by rcases hp with h | h; exact Or.inl h; exact Or.inr (Or.inl h)
  srvRest_applyG E γr A m rq v3 x x' out f ht hd hdec hv3 hch (plainOrCmpG_rev _ rq hp)
    (plainOrCmpG_grant _ rq hp') (fun r => restOut_plainOrCmpG E.lm rq v3 x x' out r hp' hs) hs hfb

/-- A revocation is no cluster request (its rest effect, `restAfter`, the identity). -/
theorem dispatchKind_leaseRevoke_noCluster (rq : apply.IRRModel)
    (hk : apply.dispatchKind rq = .leaseRevoke) :
    rq.clusterVersionSet = none ∧ rq.clusterMemberAttrSet = none := by
  constructor
  · cases h : rq.clusterVersionSet with
    | none => rfl
    | some _ => simp [apply.dispatchKind, h] at hk
  · cases h : rq.clusterMemberAttrSet with
    | none => rfl
    | some _ =>
      cases h' : rq.clusterVersionSet <;> simp [apply.dispatchKind, h, h'] at hk

/-- **A revocation's table and image one entry later** (the pure half of `srvRest_applyR`). -/
theorem revokeA_table (γr : ReadNames) (A : List EntryModel) (m : EntryModel)
    (rq : apply.IRRModel) (v3 : Bool) (x x' : apply.ApplyKV) (out : apply.ApplyOut) (f : w64 → w64)
    (ht : m.typ = W32 0) (hd : m.data ≠ []) (hdec : apply.irrDecode m.data = some rq)
    (hv3 : v3 = decide (uint.Z γr.kv.c0 < uint.Z m.index)) (hch : x.chain = γr.kv.ch0)
    (hch0 : γr.kv.ch0 = apply.alarmChain false false false)
    (hr : apply.revokeKindOk rq) (hs : apply.applyStep rq v3 x x' out) (R : apply.RestM)
    (hR : ∀ id, apply.restRevoke id R = R) :
    (appliedTable γr (A ++ [m])).ids = apply.revokeIdsA rq v3 out (appliedTable γr A).ids ∧
      apply.revokeRestA (appliedTable γr A).ids rq v3 out
          (apply.restLeasesWith f (appliedTable γr A).ids R) =
        apply.restLeasesWith f (appliedTable γr (A ++ [m])).ids R := by
  have hk := hr.1
  have htab : appliedTable γr (A ++ [m]) =
      dispatchTable γr.kv.ch0 rq v3 (appliedTable γr A) := by
    rw [appliedTable_snoc]; unfold kvTable; rw [if_pos ht, if_neg hd]; simp only [hdec]; rw [← hv3]
  rw [htab]
  generalize appliedTable γr A = lt
  cases v3 with
  | false =>
    have hd0 : dispatchTable γr.kv.ch0 rq false lt = lt := by
      unfold dispatchTable; rw [if_pos (Or.inr rfl)]
    rw [hd0]
    cases out <;> simp [apply.revokeIdsA, apply.revokeRestA, apply.revokeIds_noV3,
      apply.revokeRest_noV3]
  | true =>
    cases out with
    | skipped => exact absurd hs.1 (by rw [hr.2.2]; decide)
    | rejected => exact absurd hs.1 (by rw [hr.2.1]; decide)
    | dispatched o skip =>
      obtain ⟨l, ns, rfl⟩ := dispatchStep_start_revoke rq hr x.log o (by rw [← hch0, ← hch]; exact hs.2.1)
      have hd1 : dispatchTable γr.kv.ch0 rq true lt = backendTable rq lt := by
        unfold dispatchTable
        rw [if_neg (by simp [hk, apply.preV3Kind]), hch0]
        simp [apply.alarmChain, apply.baseChain, chainTable]
      rw [hd1]
      simp only [apply.revokeIdsA, apply.revokeRestA]
      cases hid : rq.leaseRevoke with
      | none =>
        have h1 : backendTable rq lt = lt := by unfold backendTable; rw [hk]; simp [hid]
        rw [h1]
        unfold apply.revokeIds apply.revokeRest
        rw [if_pos ⟨hk, rfl⟩, if_pos ⟨hk, rfl⟩, hid]
        exact ⟨rfl, rfl⟩
      | some id =>
        rw [apply.revokeIds_applied rq id l ns _ hk hid,
          apply.revokeRest_applied _ rq id l ns _ hk hid]
        have hf : (backendTable rq lt).ids = lt.ids.filter (· != id) := by
          unfold backendTable; rw [hk]; simp only [hid]
          split
          · unfold LeaseTable.ids
            rw [List.filter_map]
            congr 1
            apply List.filter_congr
            intro p _
            cases h : (p.1 == id) <;> simp_all [bne]
          · rename_i hm
            exact (List.filter_eq_self.2 (fun a ha => by
              simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]
              intro e; subst e; exact hm ha)).symm
        refine ⟨hf, ?_⟩
        rw [hf]
        split
        · rw [restRevoke_leasesWith, hR]
        · rename_i hm
          rw [List.filter_eq_self.2 (fun a ha => by
            simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]
            intro e; subst e; exact hm ha)]

open Iris.ProofMode in
/-- **`srvRest` one entry later, a revocation** (the lease-expiry plan's X7): in the revocable mode
(so a granting cluster), at the start's chain: the live set without the lease (the table's
`backendTable`), the image without its record (`restRevoke_leasesWith`; the model's rest holds
none, `restRevoke_restModel`), the rest otherwise the identity's. -/
theorem srvRest_applyR (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) (m : EntryModel)
    (rq : apply.IRRModel) (v3 : Bool) (x x' : apply.ApplyKV) (out : apply.ApplyOut) (f : w64 → w64)
    (ht : m.typ = W32 0) (hd : m.data ≠ []) (hdec : apply.irrDecode m.data = some rq)
    (hv3 : v3 = decide (uint.Z γr.kv.c0 < uint.Z m.index)) (hch : x.chain = γr.kv.ch0)
    (hch0 : γr.kv.ch0 = apply.alarmChain false false false)
    (hr : revokePropOk E.lm rq) (hs : apply.applyStep rq v3 x x' out)
    (hfb : E.lg = true → leaseTTLsGeReq (appliedTable γr A) f) :
    srvGrantIf E ∗ srvReqsIf E (appliedTable γr A) ∗
      apply.ltHalf E (apply.revokeIdsA rq v3 out (srvIds E (appliedTable γr A).ids)) ∗
      (∃ t : w64, ⌜apply.grantTTLOk rq t⌝ ∗ E.RO (apply.revokeRestA (srvIds E (appliedTable γr A).ids) rq v3 out
        (apply.restOut rq v3 out (apply.restLeasesWith f (srvIds E (appliedTable γr A).ids)
          (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A)))))) ∗
      srvEver E (A ++ [m]) ⊢
      srvRest E γr (A ++ [m]) := by
  have hk := hr.2.1
  have hlg : E.lg = true := apply.AEnv.lg_true_of_lm (by rw [hr.1]; decide)
  have hnc := dispatchKind_leaseRevoke_noCluster rq hk
  have hra : ∀ r, apply.restAfter rq v3 r = r := fun r => apply.restAfter_other rq v3 r hnc.1 hnc.2
  have hre : restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ (A ++ [m])) =
      restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A) := by
    rw [← List.append_assoc, restModel_append, restEntry_normal _ _ rq _ ht hd hdec, ← hv3, hra]
  have hro : ∀ r, apply.restOut rq v3 out r = r := fun r => by
    rw [restOut_revoke rq v3 x x' out r hr.2 hs, hra]
  obtain ⟨hT, hR⟩ := revokeA_table γr A m rq v3 x x' out f ht hd hdec hv3 hch hch0 hr.2 hs
    (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A))
    (fun id => restRevoke_restModel id _ _ _)
  have hsub : ∀ p ∈ appliedTable γr (A ++ [m]), p ∈ appliedTable γr A := by
    have htab : appliedTable γr (A ++ [m]) =
        dispatchTable γr.kv.ch0 rq v3 (appliedTable γr A) := by
      rw [appliedTable_snoc]; unfold kvTable; rw [if_pos ht, if_neg hd]; simp only [hdec]; rw [← hv3]
    rw [htab]
    exact dispatchTable_sub_nonGrant _ rq v3 _ (by rw [hk]; decide)
  unfold srvRest srvRestAt srvGrantIf srvIds srvReqsIf
  simp only [hlg, ↓reduceIte, hro]
  rw [hR, ← hT, hre]
  iintro ⟨#HG, #HQ, HL, ⟨%t, -, HR⟩, HU⟩
  iframe HL HG HU
  isplitl [HR]
  · iexists f
    iframe HR
    ipureintro; exact leaseTTLsGeReq_sub (hfb hlg) hsub
  iapply srvReqs_sub E _ _ hsub $$ HQ

open Iris.ProofMode in
/-- **`srvRest` one entry later, through `Apply`'s post** (its revocation wrappers over the grant's):
a revocation by `srvRest_applyR`, anything else by `srvRest_applyPG`. -/
theorem srvRest_applyPGR (E : apply.AEnv GF) (γr : ReadNames) (A : List EntryModel) (m : EntryModel)
    (rq : apply.IRRModel) (v3 : Bool) (x x' : apply.ApplyKV) (out : apply.ApplyOut) (f : w64 → w64)
    (ht : m.typ = W32 0) (hd : m.data ≠ []) (hdec : apply.irrDecode m.data = some rq)
    (hv3 : v3 = decide (uint.Z γr.kv.c0 < uint.Z m.index)) (hch : x.chain = γr.kv.ch0)
    (hch0 : γr.kv.ch0 = apply.alarmChain false false false)
    (hp : plainOrCmpG E.lm rq) (hs : apply.applyStep rq v3 x x' out)
    (hfb : E.lg = true → leaseTTLsGeReq (appliedTable γr A) f) :
    srvGrantIf E ∗ srvReqsIf E (appliedTable γr A) ∗ grantReqA E rq v3 out ∗
      ⌜apply.grantOutOkA x.chain rq v3 (srvIds E (appliedTable γr A).ids) out⌝ ∗
      apply.ltHalf E (apply.revokeIdsA rq v3 out
        (apply.grantIdsA rq v3 out (srvIds E (appliedTable γr A).ids))) ∗
      (∃ t : w64, ⌜apply.grantTTLOk rq t⌝ ∗ E.RO (apply.revokeRestA (srvIds E (appliedTable γr A).ids) rq v3 out
        (apply.grantRestA t rq v3 out (apply.restOut rq v3 out
          (apply.restLeasesWith f (srvIds E (appliedTable γr A).ids)
            (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A))))))) ∗
      srvEver E (A ++ [m]) ⊢
      srvRest E γr (A ++ [m]) := by
  by_cases hk : apply.dispatchKind rq = .leaseRevoke
  · have hr : revokePropOk E.lm rq := by
      rcases hp with hp | hg | hr
      · exact absurd hk (plainOrCmp_nonLease rq hp).2
      · rw [hg.2.1] at hk; cases hk
      · exact hr
    have hng : apply.dispatchKind rq ≠ .leaseGrant := by rw [hk]; decide
    rw [apply.grantIdsA_nonGrant _ _ _ _ hng]
    simp only [apply.grantRestA_nonGrant _ _ _ _ _ hng]
    iintro ⟨#HG, #HQ, -, -, HL, HR, HU⟩
    iapply srvRest_applyR E γr A m rq v3 x x' out f ht hd hdec hv3 hch hch0 hr hs hfb
    iframe HG HQ HL HR HU
  · iintro ⟨#HG, #HQ, #HGr, %Hgo, HL, HR, HU⟩
    ihave ⟨HL, HR⟩ := revokeA_drop E rq v3 out _ _ _ hk $$ [$HL $HR]
    iapply srvRest_applyPG E γr A m rq v3 x x' out f ht hd hdec hv3 hch
      (plainOrCmpG_nonRev _ rq hp hk) hs hfb
    iframe HG HQ HGr HL HR HU
    ipureintro; exact Hgo

open Iris.ProofMode in
/-- **What `applyEntryNormal` hands `Apply` for a revocation** (`revokeOwn`): the applier row's
range deleter and, in the revocable mode, the revocable lessor (`srvGrantIf`'s mode); with the
deleter back from `Apply`'s post. Nothing for another request. -/
theorem revokeOwn_take [go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions] (E : apply.AEnv GF) (rq : apply.IRRModel) (hp : plainOrCmpG E.lm rq) :
    lease.rdAt E.γ.leases E.s ∗ srvGrantIf E ⊢
      apply.revokeOwn E rq ∗ (apply.revokeOwn E rq -∗ lease.rdAt E.γ.leases E.s) := by
  by_cases hk : apply.dispatchKind rq = .leaseRevoke
  · have hr : revokePropOk E.lm rq := by
      rcases hp with hp | hg | hr
      · exact absurd hk (plainOrCmp_nonLease rq hp).2
      · rw [hg.2.1] at hk; cases hk
      · exact hr
    have hlg : E.lg = true := apply.AEnv.lg_true_of_lm (by rw [hr.1]; decide)
    unfold apply.revokeOwn srvGrantIf srvGrantable
    rw [if_pos hk, hlg]
    simp only [↓reduceIte, hr.1]
    iintro ⟨Hrd, #⟨-, Hm⟩⟩
    iframe Hrd
    isplitl []
    · have hf : decide (lease.Mode.revocable = lease.Mode.mono) = false := by decide
      rw [hf]; iexact Hm
    iintro ⟨H, _⟩
    iexact H
  · rw [apply.revokeOwn_nonRevoke E rq hk]
    iintro ⟨H, -⟩
    isplitl []
    · itrivial
    iintro -; iexact H

/-- **Its permits give a covered request's, a compaction's, or an admitted grant's**
(`grantPermRq`). -/
theorem srvGrantIf_permPG [go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]
    (E : apply.AEnv GF) (rq : apply.IRRModel) (hp : plainOrCmpG E.lm rq) :
    srvGrantIf E ⊢ apply.grantPermRq E rq :=
  srvGrantIf_perm E rq (fun hk => apply.AEnv.lg_true_of_lm (plainOrCmpG_grant _ rq hp hk).1)

/-- **The apply package's `cmpAdmit` from the entry's claims** (the glue at `applyEntryNormal`):
the apply thread's log the model's of the applied log `A` (`kvApplied`), the store compacting in
the cluster's compaction mode (`srvEnvOkD`'s `d.cm = E.cmp`, `envAgree`), the revision positive
(the proposal's `compactPropOk`). -/
theorem cmpAdmit_of_entry (γk : KVNames) (cmp : Bool) (A : List EntryModel) (m : EntryModel)
    (rq : apply.IRRModel) (kb : Option mvcc.KBReal) (log : mvcc.Log) (hl : log = kvModel γk A)
    (hkb : cmp = true → mvcc.kbCmpM kb) (ht : m.typ = W32 0) (hd : m.data ≠ [])
    (hdec : apply.irrDecode m.data = some rq) (h : cmpEntryOk γk cmp A m) :
    apply.cmpAdmit kb log rq := by
  intro hk r hr
  obtain ⟨hc, ⟨⟨-, r', hr', h1⟩, -⟩, hrl⟩ := h ht hd rq hdec hk
  rw [hr] at hr'
  cases hr'
  subst hl
  exact ⟨hkb hc, by have := hrl r hr; omega, h1⟩


/-- **A revision of the KV model of a committed prefix is reached** (C3's server stage, 2026-11-02):
the committed prefix `A` is equivalent to a prefix of the cluster's requested log
(`srvReqLogLb_of_rlogLb`), whose KV model is `A`'s (`kvModel_eqv`, with `kvInv`'s `c0 ≤ ai0`), on
the name the KV invariant ties to the KV's (`γk.rlog = γ.raft.log`). -/
theorem kv_revLbZ_of_rlogLb (γ : ServerRaftNames) (γk : KVNames) (A : List EntryModel) (n : Int)
    (hn : n < (kvModel γk A).length) :
    ⊢ kvInv (GF := GF) γ γk -∗ srvRaftLogInv γ -∗ srvRLogLb γ A ={⊤}=∗ kvRevLbZ γk n := by
  iintro #Hinv #Hr #HA
  imod (srvReqLogLb_of_rlogLb γ ⊤ (fun _ _ => CoPset.mem_full) A) $$ Hr HA with ⟨%L₀, #HL0, %Heqv⟩
  iunfold kvInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%L, HL, Hσ, %Hok, #Hw, HG⟩
  imod Hclose $$ [HL Hσ HG] with -
  · inext; iexists L; iframe HL Hσ Hw HG; ipureintro; exact Hok
  imodintro
  have hm := (kvModel_eqv γ γk A L₀ Heqv Hok.2.2.1).1
  iunfold kvRevLbZ
  iexists L₀
  isplitr
  · rw [Hok.2.2.2.2.2.2.1]; iunfold srvReqLogLb at HL0; iexact HL0
  ipureintro; rw [← hm]; exact hn

/-- **The apply package's `cmpPermRq` from the entry's claim** (C3's server stage): a compaction's
claim (`cmpEntryOk`: its revision, positive, at least the cluster's retention below the model
before it, which the cluster has reached, `kv_revLbZ_of_rlogLb`) is the cluster's permit
(`kvCmpPermit`), which the store's permit is (`srvKVInvs`'s `crevPermIs`). -/
theorem cmpPermRq_of_entry [go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions] (E : apply.AEnv GF) (γk : KVNames)
    (A : List EntryModel) (m : EntryModel) (rq : apply.IRRModel) (hcl : cmpEntryOk γk γk.cmp A m)
    (ht : m.typ = W32 0) (hd : m.data ≠ []) (hdec : apply.irrDecode m.data = some rq) :
    kvRevLbZ (GF := GF) γk ((kvModel γk A).length - 1) ∗ mvcc.crevPermIs E.γ (kvCmpPermit γk) ⊢
      apply.cmpPermRq E rq := by
  iintro ⟨#Hlb, #Hcp⟩
  iunfold apply.cmpPermRq
  iintro !> %hk %r %hr
  obtain ⟨-, hc, hrl⟩ := hcl ht hd rq hdec hk
  have h0 : 0 < sint.Z r := by
    obtain ⟨⟨-, r', hr', h1⟩, -⟩ := hc
    rw [hr] at hr'; cases hr'; omega
  have h1 := hrl r hr
  iapply mvcc.crevPermAt_of E.γ (kvCmpPermit γk) (sint.Z r)
  iframe Hcp
  iintro !>
  iunfold kvCmpPermit
  isplitr
  · ipureintro; exact h0
  iapply kvRevLbZ_mono γk (sint.Z r + γk.cret) ((kvModel γk A).length - 1) (by omega)
  iexact Hlb

/-- **The transfer (S3-3, item 8)**: an entry `m` of the committed log after `A` (a lower bound of
it, as `applyEntryNormal`'s proof holds) gets its claim from the KV invariant's, at the invariant's
mode. At `⊤`, as `kv_log_plain`. -/
theorem kv_entry_claim (γ : ServerRaftNames) (γk : KVNames)
    (A : List EntryModel) (m : EntryModel) :
    ⊢ kvInv (GF := GF) γ γk -∗ srvRaftLogInv γ -∗ srvRLogLb γ (A ++ [m]) ={⊤}=∗
      ⌜cmpEntryOk γk γk.cmp A m⌝ := by
  iintro #Hinv #Hr #HB
  iunfold kvInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%L, HL, Hσ, %Hok, #Hw, HG⟩
  imod srvRLog_lb γ (⊤ \ ↑kvN) (mask_ndot_ne' nroot "raft_commit" "server_kv" (by decide))
    L (A ++ [m]) $$ Hr HL HB with ⟨HL, %Hp⟩
  ihave %HBi := srvRLogLb_idx γ (A ++ [m]) $$ HB
  imod Hclose $$ [HL Hσ HG] with -
  · inext; iexists L; iframe HL Hσ Hw HG; ipureintro; exact Hok
  imodintro
  ipureintro
  obtain ⟨-, -, hc0, -, -, hcl, -⟩ := Hok
  exact cmpEntryOk_transfer γ γk γk.cmp A L m HBi Hp.1 Hp.2.1 Hp.2.2 hc0 hcl

/-- The revocable-mode grant id of a raft log entry with data (`entryRevGrantId`'s, E3 (c)). -/
def leRevGrantId (lm : lease.Mode) (e : LogEntry) : Option w64 :=
  if e.type = W32 0 ∧ e.data ≠ [] then (apply.irrDecode e.data).bind (rqRevGrantId lm) else none

/-- Fillers and empty `ConfChangeV2`s have no data, so no grant id. -/
theorem filterMap_leRevGrantId_opsOf (lm : lease.Mode) (l : List LogEntry) :
    (opsOf l).filterMap (leRevGrantId lm) = l.filterMap (leRevGrantId lm) := by
  unfold opsOf
  induction l with
  | nil => rfl
  | cons e l ih =>
    rw [List.filter_cons]
    split
    · rw [List.filterMap_cons, List.filterMap_cons, ih]
    · next h =>
      have hd : e.data = [] := by
        by_cases h1 : e.isFiller
        · exact h1.1
        by_cases h2 : e.isEmptyV2
        · exact h2.1
        simp [h1, h2] at h
      have hn : leRevGrantId lm e = none := by
        unfold leRevGrantId; rw [if_neg (fun h => h.2 hd)]
      rw [List.filterMap_cons, hn, ih]

/-- The applied log's entries with data, through raft's entries. -/
theorem logRevGrantIds_filter_data (lm : lease.Mode) (X : List EntryModel) :
    logRevGrantIds lm (X.filter fun m => decide (m.data ≠ [])) =
      (X.map EntryModel.toLE).filterMap (leRevGrantId lm) := by
  unfold logRevGrantIds
  induction X with
  | nil => rfl
  | cons x X ih =>
    rw [List.filter_cons, List.map_cons]
    by_cases hd : x.data = []
    · have hn : leRevGrantId lm x.toLE = none := by
        unfold leRevGrantId; rw [if_neg (fun h => h.2 hd)]
      rw [if_neg (by simp [hd]), List.filterMap_cons_none hn]
      exact ih
    · have he : entryRevGrantId lm x = leRevGrantId lm x.toLE := by
        unfold entryRevGrantId leRevGrantId
        by_cases ht : x.typ = W32 0
        · rw [if_pos ht, if_pos ⟨ht, hd⟩]; rfl
        · rw [if_neg ht, if_neg (fun h => ht h.1)]
      rw [if_pos (by simp [hd]), List.filterMap_cons, List.filterMap_cons, he, ih]

/-- A log with no filler nor empty `ConfChangeV2` (the requested log): its grant ids through raft's
entries. -/
theorem logRevGrantIds_noFill (lm : lease.Mode) (L : List EntryModel)
    (hnf : ∀ e ∈ L, ¬ e.toLE.isFiller ∧ ¬ e.toLE.isEmptyV2) :
    logRevGrantIds lm L = (L.map EntryModel.toLE).filterMap (leRevGrantId lm) := by
  unfold logRevGrantIds
  induction L with
  | nil => rfl
  | cons x L ih =>
    have hx : entryRevGrantId lm x = leRevGrantId lm x.toLE := by
      unfold entryRevGrantId leRevGrantId
      show _ = (if x.typ = W32 0 ∧ x.data ≠ [] then _ else none)
      by_cases ht : x.typ = W32 0
      · have hd : x.data ≠ [] := fun hd => (hnf x List.mem_cons_self).1 ⟨hd, ht⟩
        rw [if_pos ht, if_pos ⟨ht, hd⟩]; rfl
      · rw [if_neg ht, if_neg (fun h => ht h.1)]
    rw [List.filterMap_cons, List.map_cons, List.filterMap_cons, hx,
      ih (fun e he => hnf e (List.mem_cons_of_mem _ he))]

/-- **A committed entry's grant id is not an earlier one's** (E3 (c)): the requested log's grant
ids have no repeat, and the applied log's entries with data, then `m`, are a prefix of them. -/
theorem grantId_fresh_transfer (lm : lease.Mode) (A L : List EntryModel) (m : EntryModel)
    (hnf : ∀ e ∈ L, ¬ e.toLE.isFiller ∧ ¬ e.toLE.isEmptyV2)
    (h : opsOf ((A ++ [m]).map EntryModel.toLE) <+: L.map EntryModel.toLE)
    (hnd : (logRevGrantIds lm L).Nodup) (hd : m.data ≠ []) (gid : w64)
    (hg : entryRevGrantId lm m = some gid) :
    gid ∉ logRevGrantIds lm (A.filter fun m => decide (m.data ≠ [])) := by
  have h1 := h.filterMap (leRevGrantId lm)
  rw [filterMap_leRevGrantId_opsOf, ← logRevGrantIds_noFill lm L hnf] at h1
  have hn := hnd.sublist h1.sublist
  have hm : leRevGrantId lm m.toLE = some gid := by
    rw [← hg]
    unfold entryRevGrantId leRevGrantId
    show (if m.typ = W32 0 ∧ m.data ≠ [] then _ else none) = _
    by_cases ht : m.typ = W32 0
    · rw [if_pos ⟨ht, hd⟩, if_pos ht]; rfl
    · rw [if_neg (fun h => ht h.1), if_neg ht]
  rw [List.map_append, List.filterMap_append, List.map_singleton, List.filterMap_cons_some hm,
    List.filterMap_nil, ← logRevGrantIds_filter_data] at hn
  intro hin
  exact (List.nodup_append.1 hn).2.2 gid hin gid (List.mem_singleton_self _) rfl

open Iris.ProofMode in
/-- **A committed entry's grant id is new** (E3 (c), `grantId_fresh_transfer`): an entry `m` of the
committed log after `A` (as `kv_entry_claim`) has a revocable-mode grant id that no entry of `A` with
data has, from the KV invariant's (`kvGrantIds`: generated ids of one prefix, no repeat). -/
theorem kv_entry_grantFresh (γ : ServerRaftNames) (γk : KVNames)
    (A : List EntryModel) (m : EntryModel) :
    ⊢ kvInv (GF := GF) γ γk -∗ srvRaftLogInv γ -∗ srvRLogLb γ (A ++ [m]) ={⊤}=∗
      ⌜m.data ≠ [] → ∀ gid, entryRevGrantId γk.lm m = some gid →
        gid ∉ logRevGrantIds γk.lm (A.filter fun m => decide (m.data ≠ []))⌝ := by
  iintro #Hinv #Hr #HB
  iunfold kvInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%L, HL, Hσ, %Hok, #Hw, HG⟩
  imod srvRLog_lb γ (⊤ \ ↑kvN) (mask_ndot_ne' nroot "raft_commit" "server_kv" (by decide))
    L (A ++ [m]) $$ Hr HL HB with ⟨HL, %Hp⟩
  iunfold kvGrantIds at HG
  icases HG with ⟨%U, %HU, HUs⟩
  imod Hclose $$ [HL Hσ HUs] with -
  · inext; iexists L; iframe HL Hσ Hw
    isplitr
    · ipureintro; exact Hok
    iunfold kvGrantIds; iexists U; iframe HUs; ipureintro; exact HU
  imodintro
  ipureintro
  intro hd gid hg
  have hnd : (logRevGrantIds γk.lm L).Nodup := by
    rw [HU.1]; exact leaseIdMask_nodup_of_pfx U (kvPfx γk) HU.2.1 HU.2.2
  exact grantId_fresh_transfer γk.lm A L m Hp.2.1 Hp.2.2 hnd hd gid hg

open Iris.ProofMode in
/-- **The applied log's grant ids have no repeat** (the revocable mode; `kv_entry_grantFresh`'s
argument for the whole log): from the KV invariant's (`kvGrantIds`). What a snapshot's
`appliedTable_rev_mem`/`appliedTable_granted_live` take (the lease-expiry plan's S2–S4, Probe 4). -/
theorem kv_grantLog_nodup (γ : ServerRaftNames) (γk : KVNames) (A : List EntryModel) :
    ⊢ kvInv (GF := GF) γ γk -∗ srvRaftLogInv γ -∗ srvRLogLb γ A ={⊤}=∗
      ⌜γk.lm = .revocable → (srvGrantLog A).Nodup⌝ := by
  iintro #Hinv #Hr #HB
  iunfold kvInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%L, HL, Hσ, %Hok, #Hw, HG⟩
  imod srvRLog_lb γ (⊤ \ ↑kvN) (mask_ndot_ne' nroot "raft_commit" "server_kv" (by decide))
    L A $$ Hr HL HB with ⟨HL, %Hp⟩
  iunfold kvGrantIds at HG
  icases HG with ⟨%U, %HU, HUs⟩
  imod Hclose $$ [HL Hσ HUs] with -
  · inext; iexists L; iframe HL Hσ Hw
    isplitr
    · ipureintro; exact Hok
    iunfold kvGrantIds; iexists U; iframe HUs; ipureintro; exact HU
  imodintro
  ipureintro
  intro hlm
  have hnd : (logRevGrantIds γk.lm L).Nodup := by
    rw [HU.1]; exact leaseIdMask_nodup_of_pfx U (kvPfx γk) HU.2.1 HU.2.2
  have h1 := Hp.2.2.filterMap (leRevGrantId γk.lm)
  rw [filterMap_leRevGrantId_opsOf, ← logRevGrantIds_noFill γk.lm L Hp.2.1] at h1
  have hn := hnd.sublist h1.sublist
  rw [← logRevGrantIds_filter_data, hlm] at hn
  exact hn

/-- A grant the entry carries is in a cluster that grants leases. -/
theorem plainOrCmpG_lg (E : apply.AEnv GF) (rq : apply.IRRModel) (hp : plainOrCmpG E.lm rq) :
    apply.dispatchKind rq = .leaseGrant → E.lg = true :=
  fun hk => apply.AEnv.lg_true_of_lm (plainOrCmpG_grant _ rq hp hk).1

open Iris.ProofMode in
/-- **What `applyEntryNormal` hands `Apply` of the ids** (E3 (c)): the apply thread's half of the
ids the lessor ever had, `U`, and the entry's grant new to it (`srvGrantFresh`, from
`kv_entry_grantFresh`'s `Hgf` at the KV names' mode, the server's). -/
theorem srvEver_applyPre (E : apply.AEnv GF) (γk : KVNames) (A : List EntryModel) (m : EntryModel)
    (rq : apply.IRRModel) (ht : m.typ = W32 0) (hd : m.data ≠ [])
    (hdec : apply.irrDecode m.data = some rq) (hp : plainOrCmpG E.lm rq) (hlm : γk.lm = E.lm)
    (Hgf : m.data ≠ [] → ∀ gid, entryRevGrantId γk.lm m = some gid →
      gid ∉ logRevGrantIds γk.lm (A.filter fun m => decide (m.data ≠ []))) :
    srvGrantIf E ∗ srvEver E A ⊢
      ∃ U : List w64, apply.everOwn E U ∗ apply.grantFresh E rq U ∗ ⌜srvEverOk E A U⌝ := by
  have hfr : E.lm = .revocable → apply.dispatchKind rq = .leaseGrant →
      ∀ g : apply.LeaseGrantModel, rq.leaseGrant = some g → g.id ∉ srvGrantLog A := by
    intro hr hk g hg
    have h := Hgf hd g.id (by
      unfold entryRevGrantId rqRevGrantId
      rw [if_pos ht, hdec]
      simp [hlm, hr, hk, hg])
    rw [hlm, hr] at h
    exact h
  iintro ⟨#HG, HE⟩
  ihave ⟨%U, HU, %Hok⟩ := srvEver_open E A $$ HE
  iexists U
  iframe HU
  isplitl []
  · iapply srvGrantFresh E A U rq Hok (plainOrCmpG_lg E rq hp) hfr $$ HG
  ipureintro; exact Hok

open Iris.ProofMode in
/-- `srvEver_applyPre` for a request that grants nothing (`grantFresh_of_not_grant`). -/
theorem srvEver_applyPreN (E : apply.AEnv GF) (A : List EntryModel) (rq : apply.IRRModel)
    (hk : apply.dispatchKind rq ≠ .leaseGrant) :
    srvEver E A ⊢
      ∃ U : List w64, apply.everOwn E U ∗ apply.grantFresh E rq U ∗ ⌜srvEverOk E A U⌝ := by
  iintro HE
  ihave ⟨%U, HU, %Hok⟩ := srvEver_open E A $$ HE
  iexists U
  iframe HU
  isplitl []
  · iapply apply.grantFresh_of_not_grant E rq U hk
  ipureintro; exact Hok

/-- **Off, a committed log has no compaction** (`kv_log_plain`, `crevOf_plain`). -/
theorem crevOf_off (γ : ServerRaftNames) (γk : KVNames) (A : List EntryModel) (hcm : γk.cmp = false) :
    ⊢ kvInv (GF := GF) γ γk -∗ srvRaftLogInv γ -∗ srvRLogLb γ A ={⊤}=∗ ⌜crevOf γk A = -1⌝ := by
  iintro #Hinv #Hr #HA
  imod kv_log_plain γ γk A $$ Hinv Hr HA with %Hp
  imodintro
  ipureintro
  rw [hcm] at Hp
  exact crevOf_plainM_off γk _ A Hp.1

/-- The mode-off fact for a committed log, in either mode. -/
theorem crevOf_offM (γ : ServerRaftNames) (γk : KVNames) (A : List EntryModel) :
    ⊢ kvInv (GF := GF) γ γk -∗ srvRaftLogInv γ -∗ srvRLogLb γ A ={⊤}=∗
      ⌜γk.cmp = false → crevOf γk A = -1⌝ := by
  iintro #Hinv #Hr #HA
  cases hm : γk.cmp
  · imod crevOf_off γ γk A hm $$ Hinv Hr HA with %h
    imodintro; ipureintro; exact fun _ => h
  · imodintro; ipureintro; intro h; cases h

/-- **The committed log's compaction revision is the cluster's permit** (#7-cmp's Freeze, the
user's approval of the review's `CrevPermitLaw`): `-1`, or the revision of a committed compaction,
whose claim (`cmpEntryOk`, `kv_entry_claim`) puts it at a positive revision at least the retention
below the model before it, which the cluster reached (`kv_revLbZ_of_rlogLb`): `cmpPermRq_of_entry`'s
argument at the maximum. -/
theorem crevOf_permit (γ : ServerRaftNames) (γk : KVNames) (A : List EntryModel) :
    ⊢ kvInv (GF := GF) γ γk -∗ srvRaftLogInv γ -∗ srvRLogLb γ A ={⊤}=∗
      (⌜crevOf γk A = -1⌝ ∨ kvCmpPermit γk (crevOf γk A)) := by
  suffices h : ∀ L : List EntryModel, ⊢ kvInv (GF := GF) γ γk -∗ srvRaftLogInv γ -∗
      srvRLogLb γ L.reverse ={⊤}=∗ (⌜crevOf γk L.reverse = -1⌝ ∨ kvCmpPermit γk (crevOf γk L.reverse)) by
    have := h A.reverse; rw [List.reverse_reverse] at this; exact this
  intro L
  induction L with
  | nil =>
    iintro - - -
    imodintro; ileft; ipureintro; rfl
  | cons m L ih =>
    rw [List.reverse_cons]
    generalize L.reverse = B at ih ⊢
    iintro #Hinv #Hr #HA
    ihave #HB : srvRLogLb (GF := GF) γ B $$ []
    · iapply srvRLogLb_mono γ B (B ++ [m]) (List.prefix_append _ _) $$ HA
    imod ih $$ Hinv Hr HB with Hih
    imod kv_entry_claim γ γk B m $$ Hinv Hr HA with %Hcl
    rw [crevOf_snoc]
    rcases kvCrevEntry_cases γk.c0 γk.ch0 (crevOf γk B) m with heq | ⟨rq, r, ht, hd, hdec, hk, hrc, heq⟩
    · rw [heq]; imodintro; iexact Hih
    · obtain ⟨-, hc, hrl⟩ := Hcl ht hd rq hdec hk
      have h1 : 1 ≤ sint.Z r := by
        obtain ⟨⟨-, r', hr', h1⟩, -⟩ := hc
        rw [hrc] at hr'; cases hr'; exact h1
      have h2 := hrl r hrc
      rw [heq]
      imod kv_revLbZ_of_rlogLb γ γk B (sint.Z r + γk.cret) h2 $$ Hinv Hr HB with #Hlb
      imodintro
      iright
      iunfold kvCmpPermit
      isplitr
      · ipureintro; omega
      iexact Hlb


end arm

section nospace
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]
variable [errors_sem : _root_.Perennial.errors.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **A compaction's answer at the backend's outcome is not `ErrNoSpace`'s** (given back): `nil`,
or mvcc's `ErrCompacted` (apart from `ErrNoSpace`, `applyErrVars`); the corrupt applier's
`ErrCorrupt` comes only with its rejection. -/
theorem dispatchAnswer_notNoSpace_cmp (rq : apply.IRRModel) (log : mvcc.Log) (skip : Bool)
    (resp err : GoInterface) (tr : Loc) (o : apply.Outcome) (log' : mvcc.Log)
    (hk : apply.dispatchKind rq = .compaction) (ho : o = .applied log' false) :
    go_etcd_io.etcd.server.v3.etcdserver.apply.applyErrVars (GF := GF) ⊢
      apply.dispatchAnswer rq log skip resp err tr o -∗
      apply.dispatchAnswer rq log skip resp err tr o ∗ notNoSpaceErr err := by
  unfold apply.dispatchAnswer
  simp only [hk]
  iintro #Hv H
  icases Hv with ⟨-, -, -, -, -, #HC, -, -, -, #AC, -⟩
  icases H with ⟨%rp, %hrp, (⟨%he, Hok⟩ | ⟨%h3, (#HeC | ⟨%hoc, -⟩)⟩)⟩
  · isplitl
    · iexists rp
      isplitr
      · ipureintro; exact hrp
      ileft; iframe Hok; ipureintro; exact he
    rw [he]; iunfold notNoSpaceErr; ileft; ipureintro; rfl
  · isplitl
    · iexists rp
      isplitr
      · ipureintro; exact hrp
      iright
      isplitr
      · ipureintro; exact h3
      ileft; iexact HeC
    iunfold txn.errVarIs at HeC
    iapply errVarIs_notNoSpace _ _ $$ HC AC HeC
  · subst ho; cases hoc

/-- **`apply.Apply`'s result at the start's chain** (given back), for a covered request or a
compaction: `nil`, or its `Err` is not `ErrNoSpace`'s. -/
theorem applyResultIs_notNoSpace_M (rq : apply.IRRModel) (x x' : apply.ApplyKV) (ar : Loc)
    (out : apply.ApplyOut) (hp : plainOrCmp rq)
    (hch : x.chain = apply.alarmChain false false false)
    (hs : apply.applyStep rq true x x' out) :
    go_etcd_io.etcd.server.v3.etcdserver.apply.applyErrVars (GF := GF) ⊢
      apply.applyResultIs rq true x.log ar out -∗
      apply.applyResultIs rq true x.log ar out ∗
      (⌜ar = null⌝ ∨ ∃ err : GoInterface,
        structFieldRef go_etcd_io.etcd.server.v3.etcdserver.apply.Result go!"Err" ar ↦□ err ∗
        notNoSpaceErr err) := by
  rcases hp with hp | hc
  · exact applyResultIs_notNoSpace rq x x' ar out hp hch hs
  iintro #Hv H
  cases out with
  | skipped => exact absurd hs.1 (by rw [hc.2.1]; decide)
  | rejected => exact absurd hs.1 (by rw [hc.2.2]; decide)
  | dispatched o skip =>
    obtain ⟨-, hd, -, -⟩ := hs
    rw [hch] at hd
    have ho := dispatchStep_start_cmp rq hc x.log o hd
    simp only [apply.applyResultIs, apply.dispatchResult, _root_.or_true, ↓reduceIte]
    icases H with ⟨%hnn, %v, #Hvv, Hans, #HeI⟩
    ihave ⟨Hans, #Hn⟩ := dispatchAnswer_notNoSpace_cmp rq x.log skip v.Resp' v.Err' v.Trace' o x.log
      hc.1.1 ho $$ Hv Hans
    isplitl [Hans]
    · isplitr
      · ipureintro; exact hnn
      iexists v
      iframe Hvv Hans HeI
    iright
    iexists v.Err'
    iframe Hn
    iapply apply.result_err_ro
    iexact Hvv

/-- **A lessor's error is not `ErrNoSpace`'s** (the lease-grant plan's amendment (E)): the lessor's
three error variables hold leaf errors (`leaseInit`'s `leaseErrVar`s) apart from `ErrNoSpace`'s
(`applyErrVars`). -/
theorem lessorErrIs_notNoSpace (err : GoInterface) :
    go_etcd_io.etcd.server.v3.etcdserver.apply.applyErrVars (GF := GF) ⊢
      go_etcd_io.etcd.server.v3.lease.leaseInit -∗ lease.lessorErrIs err -∗ notNoSpaceErr err := by
  iintro #Hv #Hli #Hle
  iunfold lease.lessorErrIs at Hle
  icases Hle with ⟨%g, %e, %hg, #He, %heq⟩
  icases Hv with ⟨-, -, -, #LNF, -, -, -, #ANF, -, -, -, #AEx, #ATL⟩
  icases Hli with ⟨#VNF, #VEx, #VTL, -⟩
  rcases hg with rfl | rfl | rfl
  · iapply errVarIs_notNoSpace _ err $$ LNF ANF
    iexists e; iframe He; ipureintro; exact heq
  · iapply errVarIs_notNoSpace _ err $$ [] AEx
    · unfold EtcdGrove.errVarLeaf EtcdGrove.errLeaf EtcdGrove.errMsgOk
      iunfold go_etcd_io.etcd.server.v3.lease.leaseErrVar at VEx
      iexact VEx
    iexists e; iframe He; ipureintro; exact heq
  · iapply errVarIs_notNoSpace _ err $$ [] ATL
    · unfold EtcdGrove.errVarLeaf EtcdGrove.errLeaf EtcdGrove.errMsgOk
      iunfold go_etcd_io.etcd.server.v3.lease.leaseErrVar at VTL
      iexact VTL
    iexists e; iframe He; ipureintro; exact heq

/-- **A grant dispatched at the start's chain** (with `v3`; the lease-grant plan's amendment (F1):
`dispatchStep`'s grant arm is the chain's): applied, or the backend's rejection. -/
theorem dispatchStep_start_grant (rq : apply.IRRModel) (hg : apply.grantKindOk rq)
    (log : mvcc.Log) (o : apply.Outcome)
    (h : apply.dispatchStep (apply.alarmChain false false false) rq true log o) :
    (∃ l ns, o = .applied l ns) ∨ o = .rejected .backend := by
  obtain ⟨hk, hna, -, -⟩ := hg
  unfold apply.dispatchStep at h
  rw [if_neg (by simp [hk, apply.preV3Kind]), if_pos (Or.inr hk)] at h
  simp only [apply.alarmChain, apply.baseChain, apply.chainStep, apply.authChecks, hk, hna,
    Bool.false_eq_true, ↓reduceIte, _root_.or_self, apply.backendStep] at h
  rcases h with h | h
  · exact Or.inl ⟨_, _, h⟩
  · exact Or.inr h

/-- **`apply.Apply`'s result for a grant** (given back; the lease-grant plan's amendment (E) and
the tie of `grantRes`): `nil`, or its `Err` is not `ErrNoSpace`'s, at the start's chain: the
dispatched outcome is applied (then `Err` is `nil`) or the backend's rejection (then the lessor's
error), by `dispatchStep_start_grant` (amendment (F1)). A separate lemma from
`applyResultIs_notNoSpace_M`, as `applyResultIs` holds no grant fact: the answer is `Apply`'s
`grantResA`. -/
theorem applyResultIs_notNoSpace_grant (E : apply.AEnv GF) (rq : apply.IRRModel)
    (x x' : apply.ApplyKV) (ar : Loc) (out : apply.ApplyOut) (hg : apply.grantKindOk rq)
    (hch : x.chain = apply.alarmChain false false false)
    (hs : apply.applyStep rq true x x' out) :
    go_etcd_io.etcd.server.v3.etcdserver.apply.applyErrVars (GF := GF) ⊢
      go_etcd_io.etcd.server.v3.lease.leaseInit -∗
      apply.grantResA E rq out ar -∗ apply.applyResultIs rq true x.log ar out -∗
      apply.grantResA E rq out ar ∗ apply.applyResultIs rq true x.log ar out ∗
      (⌜ar = null⌝ ∨ ∃ err : GoInterface,
        structFieldRef go_etcd_io.etcd.server.v3.etcdserver.apply.Result go!"Err" ar ↦□ err ∗
        notNoSpaceErr err) := by
  have hg' := hg
  obtain ⟨hk, hna, hns, -⟩ := hg
  iintro #Hv #Hli Hg H
  cases out with
  | skipped => exact absurd hs.1 (by rw [hns]; decide)
  | rejected => exact absurd hs.1 (by rw [hna]; decide)
  | dispatched o skip =>
    have hoo := dispatchStep_start_grant rq hg' x.log o (hch ▸ hs.2.1)
    simp only [apply.applyResultIs, apply.dispatchResult, _root_.or_true, ↓reduceIte]
    icases H with ⟨%hnn, %v, #Hvv, Hans, #HeI⟩
    simp only [apply.grantResA]
    unfold apply.grantRes
    rw [if_pos ⟨hk, hnn⟩]
    icases Hg with ⟨%v', #Hvv', Hga, Hwb, %Hap⟩
    icombine Hvv Hvv' gives %Hvv''
    subst Hvv''
    ihave ⟨Hwb, #Hn⟩ : iprop((⌜o = .rejected .backend⌝ -∗ lease.lessorErrIs v.Err') ∗
        notNoSpaceErr v.Err') $$ [Hwb]
    · rcases hoo with ha | hb
      · iframe Hwb; rw [Hap ha]; iunfold notNoSpaceErr; ileft; ipureintro; rfl
      · ihave #HL := Hwb $$ %hb
        isplitl []
        · iintro -; iexact HL
        iapply lessorErrIs_notNoSpace $$ Hv Hli HL
    isplitl [Hga Hwb]
    · iexists v; iframe Hvv Hga Hwb; ipureintro; exact Hap
    isplitl [Hans]
    · isplitr
      · ipureintro; exact hnn
      iexists v; iframe Hvv Hans HeI
    iright; iexists v.Err'; iframe Hn; iapply apply.result_err_ro; iexact Hvv

open Iris.ProofMode in
/-- **An applied grant's request from `Apply`'s answer** (the lease-expiry plan's S2–S4, F7, DRAFT
2026-11-05; given back): a grant applied with `v3` has a result (`dispatchResult`), whose answer
has no error (`grantRes`'s tie), so the success arm of `grantAnswer`, with its `leaseReqIs`. -/
theorem grantReqA_of_res (E : apply.AEnv GF) (rq : apply.IRRModel) (v3 : Bool) (log : mvcc.Log)
    (ar : Loc) (out : apply.ApplyOut) :
    apply.grantResA E rq out ar ∗ apply.applyResultIs rq v3 log ar out ⊢
      apply.grantResA E rq out ar ∗ apply.applyResultIs rq v3 log ar out ∗
        grantReqA E rq v3 out := by
  by_cases hk : apply.dispatchKind rq = .leaseGrant
  rotate_left
  · iintro ⟨Hg, H⟩; iframe Hg H; iapply grantReqA_nonGrant E rq v3 out hk
  cases v3
  · iintro ⟨Hg, H⟩; iframe Hg H; iapply grantReqA_noV3 E rq out
  cases out with
  | skipped =>
    iintro ⟨Hg, H⟩; iframe Hg H
    iapply grantReqA_vac
    rintro g ⟨-, -, -, o, sk, l, ns, h, -⟩; cases h
  | rejected =>
    iintro ⟨Hg, H⟩; iframe Hg H
    iapply grantReqA_vac
    rintro g ⟨-, -, -, o, sk, l, ns, h, -⟩; cases h
  | dispatched o sk =>
    cases o with
    | rejected e =>
      iintro ⟨Hg, H⟩; iframe Hg H
      iapply grantReqA_vac
      rintro g ⟨-, -, -, o, sk', l, ns, h, h'⟩; cases h; cases h'
    | applied l ns =>
      cases hgl : rq.leaseGrant with
      | none =>
        iintro ⟨Hg, H⟩; iframe Hg H
        iapply grantReqA_vac
        rintro g ⟨-, -, h, -⟩; rw [hgl] at h; cases h
      | some g =>
        simp only [apply.applyResultIs, apply.dispatchResult, _root_.or_true, ↓reduceIte]
        iintro ⟨Hg, ⟨%hnn, %v, #Hvv, Hans, #HeI⟩⟩
        simp only [apply.grantResA]
        unfold apply.grantRes
        rw [if_pos ⟨hk, hnn⟩]
        icases Hg with ⟨%v', #Hvv', Hga, Hwb, %Hap⟩
        have he : v'.Err' = GoInterface.nil := Hap ⟨l, ns, rfl⟩
        irevert Hga
        unfold apply.grantAnswer
        simp only [hgl]
        iintro ⟨%r, %hresp, Hor⟩
        icases Hor with (⟨%he', Hri, %i, %lc, #Hlf, #Hrq⟩ | %hne)
        rotate_left
        · exact absurd he hne
        isplitl [Hri Hwb]
        · iexists v'
          iframe Hvv' Hwb
          isplitl [Hri]
          · iexists r
            isplitr
            · ipureintro; exact hresp
            ileft
            iframe Hri
            isplitr
            · ipureintro; exact he'
            iexists i, lc
            iframe Hlf Hrq
          · ipureintro; exact Hap
        isplitl [Hans]
        · isplitr
          · ipureintro; exact hnn
          iexists v
          iframe Hvv Hans HeI
        unfold grantReqA
        iintro !> %g' %hg'
        obtain ⟨-, -, hg2, -⟩ := hg'
        rw [hgl] at hg2
        cases hg2
        iexact Hrq

/-- **`apply.Apply`'s result for a revocation** at the start's chain: applied, its error `nil` or
`ErrLeaseNotFound` (`revokeErrIs`), not `ErrNoSpace`'s. -/
theorem applyResultIs_notNoSpace_revoke (rq : apply.IRRModel) (x x' : apply.ApplyKV) (ar : Loc)
    (out : apply.ApplyOut) (hr : apply.revokeKindOk rq)
    (hch : x.chain = apply.alarmChain false false false)
    (hs : apply.applyStep rq true x x' out) :
    go_etcd_io.etcd.server.v3.etcdserver.apply.applyErrVars (GF := GF) ⊢
      go_etcd_io.etcd.server.v3.lease.leaseInit -∗
      apply.applyResultIs rq true x.log ar out -∗
      apply.applyResultIs rq true x.log ar out ∗
      (⌜ar = null⌝ ∨ ∃ err : GoInterface,
        structFieldRef go_etcd_io.etcd.server.v3.etcdserver.apply.Result go!"Err" ar ↦□ err ∗
        notNoSpaceErr err) := by
  have hr' := hr
  obtain ⟨hk, hna, hns⟩ := hr
  iintro #Hv #Hli H
  cases out with
  | skipped => exact absurd hs.1 (by rw [hns]; decide)
  | rejected => exact absurd hs.1 (by rw [hna]; decide)
  | dispatched o skip =>
    obtain ⟨l, ns, ho⟩ := dispatchStep_start_revoke rq hr' x.log o (hch ▸ hs.2.1)
    subst ho
    simp only [apply.applyResultIs, apply.dispatchResult, _root_.or_true, ↓reduceIte]
    icases H with ⟨%hnn, %v, #Hvv, Hans, #HeI⟩
    unfold apply.dispatchAnswer
    rw [hk]
    dsimp only
    icases Hans with ⟨%r, %hresp, Hrv⟩
    simp only [apply.revokeOutcomeIs]
    icases Hrv with ⟨%hrn, #HaE, #HrE⟩
    ihave #Hn : notNoSpaceErr v.Err' $$ []
    · iunfold apply.revokeErrIs at HrE
      icases HrE with (%he | ⟨%e, #He, %heq⟩)
      · iunfold notNoSpaceErr; ileft; ipureintro; exact he
      · iapply lessorErrIs_notNoSpace $$ Hv Hli
        iunfold lease.lessorErrIs
        iexists _, e
        iframe He
        ipureintro; exact ⟨Or.inl rfl, heq⟩
    isplitl []
    · isplitr
      · ipureintro; exact hnn
      iexists v
      iframe Hvv HeI
      iexists r
      isplitr
      · ipureintro; exact hresp
      (try iframe HaE)
      (try iframe HrE)
      ipureintro; exact hrn
    iright; iexists v.Err'; iframe Hn; iapply apply.result_err_ro; iexact Hvv

/-- **`apply.Apply`'s result at the start's chain, at `lg`** (given back with the grant's answer):
a covered request or a compaction (`applyResultIs_notNoSpace_M`), or an admitted grant
(`applyResultIs_notNoSpace_grant`): `nil`, or its `Err` is not `ErrNoSpace`'s. -/
theorem applyResultIs_notNoSpace_G (E : apply.AEnv GF) (lm : lease.Mode) (rq : apply.IRRModel)
    (x x' : apply.ApplyKV) (ar : Loc) (out : apply.ApplyOut) (hp : plainOrCmpG lm rq)
    (hch : x.chain = apply.alarmChain false false false)
    (hs : apply.applyStep rq true x x' out) :
    go_etcd_io.etcd.server.v3.etcdserver.apply.applyErrVars (GF := GF) ⊢
      go_etcd_io.etcd.server.v3.lease.leaseInit -∗
      apply.grantResA E rq out ar -∗ apply.applyResultIs rq true x.log ar out -∗
      apply.grantResA E rq out ar ∗ apply.applyResultIs rq true x.log ar out ∗
      (⌜ar = null⌝ ∨ ∃ err : GoInterface,
        structFieldRef go_etcd_io.etcd.server.v3.etcdserver.apply.Result go!"Err" ar ↦□ err ∗
        notNoSpaceErr err) := by
  rcases hp with hp | hg | hr
  · iintro #Hv #Hli Hg H
    iframe Hg
    iapply applyResultIs_notNoSpace_M rq x x' ar out hp hch hs $$ Hv H
  · exact applyResultIs_notNoSpace_grant E rq x x' ar out hg.2 hch hs
  · iintro #Hv #Hli Hg H
    iframe Hg
    iapply applyResultIs_notNoSpace_revoke rq x x' ar out hr.2 hch hs $$ Hv Hli H

end nospace

end EtcdGrove
end Perennial
