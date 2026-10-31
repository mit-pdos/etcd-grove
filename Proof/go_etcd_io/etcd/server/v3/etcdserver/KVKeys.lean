/-
**The KV model's keys are short** (2026-10-30, `notes/keylen.md`; `notes/decisions.md`, "The
key-length law"): the KV invariant keeps, of every committed normal entry with data, that the
request it decodes to puts no key longer than `etcdKeyMax` (`logKeysOk`: what the proposer's
`MaxRequestBytes` check gives, `processInternalRaftRequestOnce`), and so the KV model of the
committed log, from a start log with no long key, has none (`kvRaftOf_keys`): a put appends its
request's key, a transaction its puts' (at any depth), a delete, a revocation and a compaction no
put. Lean-first (no Rocq counterpart); the structure of `KVModelRestore.lean`'s walk.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVModelDefs
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.LogLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.etcd.server.v3.etcdserver

/-! ## The invariant's fact -/

/-- **A committed entry's keys are short**: a normal entry's non-empty data decode to a request
whose put keys are at most `etcdKeyMax` bytes (a conf change and an empty entry carry no
request). -/
def entryKeysOk [GooseExts] (m : EntryModel) : Prop :=
  m.typ = W32 0 → m.data ≠ [] → ∀ rq, apply.irrDecode m.data = some rq →
    apply.irrKeysLe etcdKeyMax rq

/-- Every entry of the log has short keys. -/
def logKeysOk [GooseExts] (L : List EntryModel) : Prop := ∀ m ∈ L, entryKeysOk m

theorem logKeysOk_append [GooseExts] (A B : List EntryModel) :
    logKeysOk (A ++ B) ↔ logKeysOk A ∧ logKeysOk B := by
  unfold logKeysOk
  simp only [List.mem_append]
  constructor
  · intro h; exact ⟨fun m hm => h m (Or.inl hm), fun m hm => h m (Or.inr hm)⟩
  · rintro ⟨h1, h2⟩ m (hm | hm)
    · exact h1 m hm
    · exact h2 m hm

theorem logKeysOk_snoc [GooseExts] (L : List EntryModel) (e : EntryModel) (hL : logKeysOk L)
    (he : entryKeysOk e) : logKeysOk (L ++ [e]) :=
  (logKeysOk_append L [e]).2 ⟨hL, fun m hm => by rw [List.mem_singleton] at hm; subst hm; exact he⟩

/-- An entry with data that decode to a request with short keys has short keys. -/
theorem entryKeysOk_of_data [GooseExts] (e : EntryModel) (d : List w8) (rq : apply.IRRModel)
    (hd : e.data = d) (hdec : apply.irrDecode d = some rq)
    (hk : apply.irrKeysLe etcdKeyMax rq) : entryKeysOk e := by
  intro _ _ rq' h
  rw [hd, hdec] at h
  cases h
  exact hk

/-- A conf change has short keys (it carries no request). -/
theorem entryKeysOk_conf [GooseExts] (e : EntryModel) (h : e.typ ≠ W32 0) : entryKeysOk e :=
  fun ht => absurd ht h

/-! ## The model's keys -/

theorem chKeysLe_dels {α : Type} (n : Nat) (xs : List α) (f : α → GoString) :
    mvcc.ChKeysLe n (xs.map fun x => .del (f x)) := by
  intro k v l h
  obtain ⟨_, _, h⟩ := List.mem_map.1 h
  cases h

theorem chKeysLe_append {n : Nat} {a b : List mvcc.Change} (ha : mvcc.ChKeysLe n a)
    (hb : mvcc.ChKeysLe n b) : mvcc.ChKeysLe n (a ++ b) := by
  intro k v l h
  rcases List.mem_append.1 h with h | h
  · exact ha k v l h
  · exact hb k v l h

mutual
/-- **A server's run of operations puts only the operations' keys** (`srvOps`). -/
theorem srvOps_keys {n : Nat} (s0 : List EtcdKv) (r : w64) :
    ∀ (ops : List TxnOp) (s : List EtcdKv), TxnOp.opsPutKeysLe n ops →
      mvcc.ChKeysLe n (txn.srvOps s0 r s ops).1
  | [], s, _ => by simp [txn.srvOps_nil, mvcc.ChKeysLe]
  | op :: ops, s, hp => by
    rw [txn.srvOps_cons]
    exact chKeysLe_append (srvOp_keys s0 r op s hp.1) (srvOps_keys s0 r ops _ hp.2)

/-- One operation's changes put only its keys (`srvOps_keys`). -/
theorem srvOp_keys {n : Nat} (s0 : List EtcdKv) (r : w64) :
    ∀ (op : TxnOp) (s : List EtcdKv), op.putKeysLe n → mvcc.ChKeysLe n (txn.srvOp s0 r s op).1
  | .get o, s, _ => by simp [txn.srvOp, mvcc.ChKeysLe]
  | .put k v l, s, hp => by
    simp only [TxnOp.putKeysLe] at hp
    simp only [txn.srvOp, mvcc.ChKeysLe, List.mem_singleton, mvcc.Change.put.injEq]
    rintro k' v' l' ⟨rfl, -, -⟩; exact hp
  | .putKeep k v, s, hp => by
    simp only [TxnOp.putKeysLe] at hp
    simp only [txn.srvOp, mvcc.ChKeysLe, List.mem_singleton, mvcc.Change.put.injEq]
    rintro k' v' l' ⟨rfl, -, -⟩; exact hp
  | .putIgnVal k l, s, hp => by
    simp only [TxnOp.putKeysLe] at hp
    simp only [txn.srvOp, mvcc.ChKeysLe, List.mem_singleton, mvcc.Change.put.injEq]
    rintro k' v' l' ⟨rfl, -, -⟩; exact hp
  | .delete o, s, _ => by
    simp only [txn.srvOp]
    intro k v l h
    obtain ⟨_, _, h⟩ := List.mem_map.1 h
    cases h
  | .txn cs ts es, s, hp => by
    rw [txn.srvOp_txn]
    split
    · exact srvOps_keys s0 r ts s hp.1
    · exact srvOps_keys s0 r es s hp.2
end

theorem commitLog_keys {n : Nat} {log : mvcc.Log} {pend : List mvcc.Change}
    (hl : mvcc.LogKeysLe n log) (hp : mvcc.ChKeysLe n pend) :
    mvcc.LogKeysLe n (mvcc.commitLog log pend) := by
  unfold mvcc.commitLog
  split
  · exact hl
  · exact hl.snoc hp

/-- **A request with short keys appends no long key** (`backendLog`). -/
theorem backendLog_keys (lt : LeaseTable) (rq : apply.IRRModel) (log : mvcc.Log)
    (hk : apply.irrKeysLe etcdKeyMax rq) (hl : mvcc.LogKeysLe etcdKeyMax log) :
    mvcc.LogKeysLe etcdKeyMax (backendLog lt rq log) := by
  unfold backendLog
  split
  · split
    · rename_i op hop
      split
      · exact hl
      split
      · exact hl
      · apply hl.snoc
        simp only [mvcc.ChKeysLe, List.mem_singleton, txn.putChangeOf, mvcc.Change.put.injEq]
        rintro k v l ⟨rfl, -, -⟩
        exact hk.1 op hop
    · exact hl
  · split
    · exact commitLog_keys hl (by unfold txn.delChanges; exact chKeysLe_dels _ _ _)
    · exact hl
  · split
    · rename_i t ht
      split
      · apply commitLog_keys hl
        have hb := hk.2 t ht
        unfold txn.srvRunTxn TxnModel.branch
        split
        · exact srvOps_keys _ _ _ _ hb.1
        · exact srvOps_keys _ _ _ _ hb.2
      · exact hl
    · exact hl
  · split
    · rename_i id _
      split
      · apply commitLog_keys hl
        unfold revokeChanges
        exact chKeysLe_dels _ _ _
      · exact hl
    · exact hl
  · exact hl

theorem chainLog_keys (rq : apply.IRRModel) (lt : LeaseTable) (log : mvcc.Log)
    (hk : apply.irrKeysLe etcdKeyMax rq) (hl : mvcc.LogKeysLe etcdKeyMax log) :
    ∀ c : apply.Chain, mvcc.LogKeysLe etcdKeyMax (chainLog c rq lt log)
  | .backend => backendLog_keys lt rq log hk hl
  | .corrupt c => by
    simp only [chainLog]; split
    · exact hl
    · exact chainLog_keys rq lt log hk hl c
  | .capped c => by
    simp only [chainLog]; split
    · exact hl
    · exact chainLog_keys rq lt log hk hl c
  | .auth _ c => by simp only [chainLog]; exact chainLog_keys rq lt log hk hl c
  | .quota c => by simp only [chainLog]; exact chainLog_keys rq lt log hk hl c

/-- **An entry with short keys appends no long key** (`kvEntry`). -/
theorem kvEntry_keys [GooseExts] (c₀ : w64) (ch : apply.Chain) (lt : LeaseTable) (log : mvcc.Log)
    (m : EntryModel) (hm : entryKeysOk m) (hl : mvcc.LogKeysLe etcdKeyMax log) :
    mvcc.LogKeysLe etcdKeyMax (kvEntry c₀ ch lt log m) := by
  unfold kvEntry
  split
  · rename_i ht
    split
    · exact hl
    · rename_i hd
      split
      · rename_i rq hdec
        have hk := hm ht hd rq hdec
        unfold dispatchLog
        split
        · exact hl
        · split
          · exact chainLog_keys rq lt log hk hl ch
          · exact hl
      · exact hl
  · exact hl

/-- **The model of a log with short keys, from a start with none, has none** (at any lease
table). -/
theorem kvRaftSt_keys [GooseExts] (c₀ : w64) (ch : apply.Chain) :
    ∀ (s₀ : mvcc.Log × LeaseTable) (A : List EntryModel), logKeysOk A →
      mvcc.LogKeysLe etcdKeyMax s₀.1 → mvcc.LogKeysLe etcdKeyMax (kvRaftSt c₀ ch s₀ A).1
  | s₀, [], _, hl => hl
  | s₀, m :: A, hA, hl => by
    have hk : kvRaftSt c₀ ch s₀ (m :: A) = kvRaftSt c₀ ch (kvEntrySt c₀ ch s₀ m) A := rfl
    rw [hk]
    exact kvRaftSt_keys c₀ ch _ A (fun m' h => hA m' (by simp [h]))
      (kvEntry_keys c₀ ch s₀.2 s₀.1 m (hA m (by simp)) hl)

/-- **The KV model of a log with short keys, from a start with none, has none.** -/
theorem kvRaftOf_keys [GooseExts] (c₀ : w64) (ch : apply.Chain) (log₀ : mvcc.Log)
    (A : List EntryModel) (hA : logKeysOk A) (hl : mvcc.LogKeysLe etcdKeyMax log₀) :
    mvcc.LogKeysLe etcdKeyMax (kvRaftOf c₀ ch log₀ A) :=
  kvRaftSt_keys c₀ ch (log₀, []) A hA hl

end EtcdGrove
end Perennial
