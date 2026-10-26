/-
**The KV model's revisions are restorable** (D22 J7b, 2026-10-26; `notes/decisions.md`, "D22 J7b"):
what `store.restore` asks of a restored log (`mvcc.restoreLogOk`) besides the store's own
well-formedness (`IdxWf`, which the image's certificate carries from the sender's store,
`imageAt`), as a pure fact of the KV model of a plain raft log: every revision an entry appends
has a change (a put appends its change, a delete or a transaction commits only changes:
`mvcc.commitLog`), and no put carries a lease (a plain put's `leaseID` is `0`, an ignored lease is
the previous key-value's, `0` by induction; a plain transaction's puts are `opPlain`'s).
Lean-first (no Rocq counterpart).

* `kvRaftOf_restorable`: from a lease-free start log, the KV model of a plain log is lease-free,
  and the revisions after the start each have a change.
* `restoreLogOk_kvRaftOf`: `restoreLogOk` of the model's tail after `NewStore`'s two revisions,
  from `IdxWf` of the model and the log plain.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVModelDefs
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreChunks

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.etcd.server.v3.etcdserver

/-- A change puts no lease. -/
def chNoLease (c : mvcc.Change) : Prop :=
  ∀ (k v : GoString) (l : w64), c = .put k v l → l = W64 0

mutual
/-- **A plain operation's changes put no lease**, on a lease-free state (`srvOp`, `srvOps`). -/
theorem srvOps_noLease (s0 : List EtcdKv) (r : w64) :
    ∀ (ops : List TxnOp) (s : List EtcdKv), txn.opsPlain ops → mvcc.LeaseZero s →
      ∀ c ∈ (txn.srvOps s0 r s ops).1, chNoLease c
  | [], s, _, _ => by simp [txn.srvOps_nil]
  | op :: ops, s, hp, hs => by
    obtain ⟨hp1, hp2⟩ := hp
    have h1 := srvOp_noLease s0 r op s hp1 hs
    have hs' : mvcc.LeaseZero (mvcc.applyChanges r s (txn.srvOp s0 r s op).1) :=
      hs.applyChanges r _ h1
    have h2 := srvOps_noLease s0 r ops _ hp2 hs'
    rw [txn.srvOps_cons]
    intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

/-- One plain operation's changes put no lease (`srvOps_noLease`). -/
theorem srvOp_noLease (s0 : List EtcdKv) (r : w64) :
    ∀ (op : TxnOp) (s : List EtcdKv), txn.opPlain op → mvcc.LeaseZero s →
      ∀ c ∈ (txn.srvOp s0 r s op).1, chNoLease c
  | .get o, s, _, _ => by simp [txn.srvOp]
  | .put k v l, s, hp, _ => by
    simp only [txn.opPlain] at hp
    subst hp
    simp only [txn.srvOp, List.mem_singleton]
    rintro c rfl k' v' l' h
    cases h; rfl
  | .putKeep k v, s, hp, _ => by simp [txn.opPlain] at hp
  | .putIgnVal k l, s, hp, _ => by
    simp only [txn.opPlain] at hp
    subst hp
    simp only [txn.srvOp, List.mem_singleton]
    rintro c rfl k' v' l' h
    cases h; rfl
  | .delete o, s, _, _ => by
    simp only [txn.srvOp]
    intro c hc k v l h
    subst h
    obtain ⟨_, _, h⟩ := List.mem_map.1 hc
    cases h
  | .txn cs ts es, s, hp, hs => by
    obtain ⟨hts, hes⟩ := hp
    rw [txn.srvOp_txn]
    split
    · exact srvOps_noLease s0 r ts s hts hs
    · exact srvOps_noLease s0 r es s hes hs
end

/-- **A restorable revision**: some change, none putting a lease. -/
def revOk (cs : List mvcc.Change) : Prop := cs ≠ [] ∧ ∀ c ∈ cs, chNoLease c

/-- `log'` is `log`, or `log` and one restorable revision. -/
def growsOk (log log' : mvcc.Log) : Prop := log' = log ∨ ∃ cs, revOk cs ∧ log' = log ++ [cs]

theorem growsOk_refl (log : mvcc.Log) : growsOk log log := Or.inl rfl

theorem growsOk_commitLog (log : mvcc.Log) (pend : List mvcc.Change)
    (h : ∀ c ∈ pend, chNoLease c) : growsOk log (mvcc.commitLog log pend) := by
  unfold mvcc.commitLog
  split
  · exact Or.inl rfl
  · rename_i hne; exact Or.inr ⟨pend, ⟨hne, h⟩, rfl⟩

/-- **A plain request's effect on a lease-free log is restorable** (`backendLog`). -/
theorem backendLog_growsOk (rq : apply.IRRModel) (log : mvcc.Log) (hp : plainCover rq)
    (hl : mvcc.LogNoLease log) : growsOk log (backendLog rq log) := by
  have hs := mvcc.stateAfter_leaseZero log hl
  unfold backendLog
  split
  · rename_i hk
    unfold plainCover at hp
    rw [hk] at hp
    obtain ⟨-, -, hlz⟩ := hp
    split
    · rename_i op hop
      split
      · exact growsOk_refl _
      · refine Or.inr ⟨_, ⟨by simp, ?_⟩, rfl⟩
        simp only [List.mem_singleton]
        rintro c rfl k v l h
        simp only [txn.putChangeOf, mvcc.Change.put.injEq] at h
        obtain ⟨-, -, rfl⟩ := h
        unfold txn.putLeaseOf
        split
        · cases hf : mvcc.findKey op.key (mvcc.stateAfter log) with
          | none => rfl
          | some kv => exact hs kv (mvcc.findKey_mem hf)
        · exact hlz op hop
    · exact growsOk_refl _
  · split
    · apply growsOk_commitLog
      intro c hc k v l h
      subst h
      obtain ⟨_, _, h⟩ := List.mem_map.1 hc
      cases h
    · exact growsOk_refl _
  · rename_i hk
    unfold plainCover at hp
    rw [hk] at hp
    obtain ⟨-, -, hpl⟩ := hp
    split
    · rename_i t ht
      split
      · apply growsOk_commitLog
        exact srvOps_noLease _ _ _ _ (txn.txnPlain_branch t _ (hpl t ht)) hs
      · exact growsOk_refl _
    · exact growsOk_refl _
  · exact growsOk_refl _

theorem chainLog_growsOk (rq : apply.IRRModel) (log : mvcc.Log) (hp : plainCover rq)
    (hl : mvcc.LogNoLease log) : ∀ c : apply.Chain, growsOk log (chainLog c rq log)
  | .backend => backendLog_growsOk rq log hp hl
  | .corrupt c => by
    simp only [chainLog]; split
    · exact growsOk_refl _
    · exact chainLog_growsOk rq log hp hl c
  | .capped c => by
    simp only [chainLog]; split
    · exact growsOk_refl _
    · exact chainLog_growsOk rq log hp hl c
  | .auth _ c => by simp only [chainLog]; exact chainLog_growsOk rq log hp hl c
  | .quota c => by simp only [chainLog]; exact chainLog_growsOk rq log hp hl c

/-- **A plain entry's effect on a lease-free log is restorable.** -/
theorem kvEntry_growsOk (c₀ : w64) (ch : apply.Chain) (log : mvcc.Log) (m : EntryModel)
    (hm : plainEntry m) (hl : mvcc.LogNoLease log) : growsOk log (kvEntry c₀ ch log m) := by
  unfold kvEntry
  split
  · rename_i ht
    split
    · exact growsOk_refl _
    · rename_i hd
      split
      · rename_i rq hdec
        have hp := (hm ht hd rq hdec).1
        unfold dispatchLog
        split
        · exact growsOk_refl _
        · split
          · exact chainLog_growsOk rq log hp hl ch
          · exact growsOk_refl _
      · exact growsOk_refl _
  · exact growsOk_refl _

/-- **The KV model of a plain log, from a lease-free start, is restorable**: lease-free, and the
revisions after the start each have a change. -/
theorem kvRaftOf_restorable (c₀ : w64) (ch : apply.Chain) :
    ∀ (log₀ : mvcc.Log) (A : List EntryModel), plainLog A → mvcc.LogNoLease log₀ →
      mvcc.LogNoLease (kvRaftOf c₀ ch log₀ A) ∧
        ∀ cs ∈ (kvRaftOf c₀ ch log₀ A).drop log₀.length, cs ≠ []
  | log₀, [], _, hl => ⟨hl, by simp [kvRaftOf_nil]⟩
  | log₀, m :: A, hA, hl => by
    have hm : plainEntry m := hA m (by simp)
    have hA' : plainLog A := fun m' h => hA m' (by simp [h])
    have hk : kvRaftOf c₀ ch log₀ (m :: A) = kvRaftOf c₀ ch (kvEntry c₀ ch log₀ m) A := rfl
    rw [hk]
    rcases kvEntry_growsOk c₀ ch log₀ m hm hl with he | ⟨cs, ⟨hne, hcs⟩, he⟩
    · rw [he]; exact kvRaftOf_restorable c₀ ch log₀ A hA' hl
    · have hl' : mvcc.LogNoLease (log₀ ++ [cs]) := by
        intro cs' h
        rcases List.mem_append.1 h with h | h
        · exact hl cs' h
        · simp only [List.mem_singleton] at h; subst h; exact hcs
      rw [he]
      obtain ⟨h1, h2⟩ := kvRaftOf_restorable c₀ ch (log₀ ++ [cs]) A hA' hl'
      refine ⟨h1, ?_⟩
      have hp := kvRaftOf_extends c₀ ch (log₀ ++ [cs]) A
      obtain ⟨T, hT⟩ := hp
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

/-- **`restoreLogOk` of the KV model's tail** (`applySnapshot.specSnap`'s `hRok`): the model of a
plain log from `NewStore`'s two empty revisions, well formed as a store's committed log
(`IdxWf`, the image's certificate's, from the sender's store). -/
theorem restoreLogOk_kvRaftOf (c₀ : w64) (ch : apply.Chain) (A : List EntryModel)
    (hA : plainLog A) (hwf : mvcc.IdxWf (kvRaftOf c₀ ch [[], []] A) []) :
    mvcc.restoreLogOk ((kvRaftOf c₀ ch [[], []] A).drop 2) := by
  have hl0 : mvcc.LogNoLease ([[], []] : mvcc.Log) := by
    intro cs hcs c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hcs
    rcases hcs with rfl | rfl <;> simp at hc
  obtain ⟨hnl, hne⟩ := kvRaftOf_restorable c₀ ch [[], []] A hA hl0
  obtain ⟨T, hT⟩ := kvRaftOf_extends c₀ ch [[], []] A
  have hsplit : [[], []] ++ (kvRaftOf c₀ ch [[], []] A).drop 2 = kvRaftOf c₀ ch [[], []] A := by
    rw [← hT]; simp
  refine ⟨fun cs hcs => hne cs (by simpa using hcs), by rw [hsplit]; exact hwf, ?_⟩
  intro cs hcs c hc k v l hcl
  exact hnl cs (List.mem_of_mem_drop hcs) c hc k v l hcl

end EtcdGrove
end Perennial
