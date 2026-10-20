/-
**watchkv's workload** (D23, 2026-10-20). Lean-first (no Rocq counterpart).

The server's workload parameter (`SrvWorkload`, D19q; `writes`, D23) at watchkv's instance: the
requests let into the log are puts of the plan `P` (the writers' Puts, picked before the member
starts: a key and a value of `P`, no lease, neither ignore flag) and the monitors' cluster
requests; the operations a client may deposit are those puts and reads. So the KV model of a
committed log of this workload (`kvRaftOf` at the start log `[[], []]` and the base chain) has,
at each revision from `2` on, exactly one change, a put of the plan (`WkLog`,
`kvRaftOf_wk`), which gives `NoDupKeysPerRev` (`WkLog.noDup`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVModelDefs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.HistoryLaws

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace watchkv

open go_etcd_io.etcd.server.v3.etcdserver

/-- A put of the plan `P`: its key and value one of `P`'s, no lease, no ignore flag. -/
def putOk (P : List (GoString × GoString)) (o : OpFull) : Prop :=
  (o.key, o.val) ∈ P ∧ o.leaseID = W64 0 ∧ o.ignoreValue = false ∧ o.ignoreLease = false

/-- The requests the workload lets into the log. -/
def admitsWk (P : List (GoString × GoString)) (rq : apply.IRRModel) : Prop :=
  (apply.dispatchKind rq = .put ∧ ∀ o, rq.put = some o → putOk P o) ∨
  apply.dispatchKind rq = .clusterMemberAttrSet ∨ apply.dispatchKind rq = .clusterVersionSet

/-- The operations a client may deposit: the plan's puts, and reads. -/
def writesWk (P : List (GoString × GoString)) (op : KVOp) : Prop :=
  (∃ o, op = .put o ∧ putOk P o) ∨ ∃ o, op = .range o

/-- **watchkv's workload** (see the file header). -/
def workload (P : List (GoString × GoString)) : SrvWorkload where
  admits := admitsWk P
  grant _ := False
  writes := writesWk P
  admits_header rq hm h := by
    unfold admitsWk at h ⊢
    simpa [apply.dispatchKind] using h
  admits_write rq op hk hop hw := by
    unfold admitsWk
    rcases hw with ⟨o, rfl, ho⟩ | ⟨o, rfl⟩
    · left
      rcases hk with hk | hk | hk
      · refine ⟨hk, fun o' ho' => ?_⟩
        unfold reqKVOp at hop
        rw [hk, ho'] at hop
        simp at hop
        subst hop; exact ho
      · unfold reqKVOp at hop; rw [hk] at hop
        cases h : rq.deleteRange <;> rw [h] at hop <;> simp at hop
      · unfold reqKVOp at hop; rw [hk] at hop
        cases h : rq.txn <;> rw [h] at hop <;> simp at hop
    · exfalso
      rcases hk with hk | hk | hk <;> unfold reqKVOp at hop <;> rw [hk] at hop
      · cases h : rq.put <;> rw [h] at hop <;> simp at hop
      · cases h : rq.deleteRange <;> rw [h] at hop <;> simp at hop
      · cases h : rq.txn <;> rw [h] at hop <;> simp at hop
  writes_range o := Or.inr ⟨o, rfl⟩
  admits_cluster _ h := Or.inr h

theorem workload_noGrant (P : List (GoString × GoString)) : (workload P).noGrant :=
  fun _ h => h

/-- A revision of a watchkv log from `2` on: one put of the plan, no lease. -/
def wkRev (P : List (GoString × GoString)) (cs : List mvcc.Change) : Prop :=
  ∃ k v, (k, v) ∈ P ∧ cs = [.put k v (W64 0)]

/-- **A watchkv log**: its first two revisions empty, every later one a put of the plan. -/
def WkLog (P : List (GoString × GoString)) (L : mvcc.Log) : Prop :=
  (∀ j cs, j < 2 → L[j]? = some cs → cs = []) ∧ ∀ j cs, 2 ≤ j → L[j]? = some cs → wkRev P cs

theorem WkLog.prefix {P : List (GoString × GoString)} {L L' : mvcc.Log} (h : WkLog P L)
    (hp : L' <+: L) : WkLog P L' := by
  obtain ⟨r, rfl⟩ := hp
  refine ⟨fun j cs hj hc => h.1 j cs hj ?_, fun j cs hj hc => h.2 j cs hj ?_⟩ <;>
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hc).1] <;> exact hc

/-- The start log is a watchkv log. -/
theorem WkLog.start (P : List (GoString × GoString)) : WkLog P [[], []] := by
  refine ⟨fun j cs _ h => ?_, fun j cs hj h => ?_⟩
  · rcases j with _ | _ | j <;> simp at h <;> exact h
  · rcases j with _ | _ | j
    · omega
    · omega
    · simp at h

/-- A short log's revisions are empty when it is a prefix of the start log. -/
theorem WkLog.of_start_prefix (P : List (GoString × GoString)) {L : mvcc.Log}
    (h : L <+: [[], []]) : WkLog P L := (WkLog.start P).prefix h

/-- One revision more. -/
theorem WkLog.snoc {P : List (GoString × GoString)} {L : mvcc.Log} {cs : List mvcc.Change}
    (h : WkLog P L) (hl : 2 ≤ L.length) (hc : wkRev P cs) : WkLog P (L ++ [cs]) := by
  refine ⟨fun j c hj hj' => h.1 j c hj ?_, fun j c hj hj' => ?_⟩
  · rw [List.getElem?_append_left (by omega)] at hj'; exact hj'
  · rcases Nat.lt_or_ge j L.length with hjl | hjl
    · rw [List.getElem?_append_left hjl] at hj'; exact h.2 j c hj hj'
    · rw [List.getElem?_append_right hjl] at hj'
      have : j - L.length = 0 := by
        have := (List.getElem?_eq_some_iff.mp hj').1; simp at this; omega
      rw [this] at hj'; simp at hj'; subst hj'; exact hc

/-- **A watchkv log writes each key once per revision.** -/
theorem WkLog.noDup {P : List (GoString × GoString)} {L : mvcc.Log} (h : WkLog P L) :
    txn.NoDupKeysPerRev L := by
  intro cs hcs
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hcs
  rcases Nat.lt_or_ge j 2 with h2 | h2
  · rw [h.1 j cs h2 hj]; simp
  · obtain ⟨k, v, -, rfl⟩ := h.2 j cs h2 hj
    simp

/-- The chain of a fresh server's apply (`alarmChain false false false`) is the backend's. -/
theorem chainLog_fresh (rq : apply.IRRModel) (log : mvcc.Log) :
    chainLog (apply.alarmChain false false false) rq log = backendLog rq log := by
  simp [apply.alarmChain, apply.baseChain, chainLog]

/-- **One entry of a watchkv log** (`kvEntry` of a plain entry of the workload): no revision, or
one put of the plan. -/
theorem kvEntry_wk (P : List (GoString × GoString)) (c₀ : w64) (log : mvcc.Log)
    (m : EntryModel) (hm : plainEntry (workload P) m) :
    kvEntry c₀ (apply.alarmChain false false false) log m = log ∨
      ∃ cs, wkRev P cs ∧ kvEntry c₀ (apply.alarmChain false false false) log m = log ++ [cs] := by
  unfold kvEntry
  split
  · rename_i ht
    split
    · left; rfl
    · rename_i hd
      split
      · rename_i rq hdec
        have hp := hm ht hd rq hdec
        obtain ⟨-, hadm⟩ := hp
        unfold dispatchLog
        split
        · left; rfl
        · split
          · rw [chainLog_fresh]
            unfold backendLog
            rcases hadm with ⟨hk, hput⟩ | hk | hk
            · rw [hk]
              cases hrp : rq.put with
              | none => left; rfl
              | some o =>
                obtain ⟨hkv, hl, hiv, hil⟩ := hput o hrp
                have hnp : txn.needsPrev o = false := by
                  simp [txn.needsPrev, hiv, hil]
                right
                refine ⟨[txn.putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter log))], ?_, ?_⟩
                · refine ⟨o.key, o.val, hkv, ?_⟩
                  simp [txn.putChangeOf, txn.putValOf, txn.putLeaseOf, hiv, hil, hl]
                · simp [hnp]
            · rw [hk]; left; rfl
            · rw [hk]; left; rfl
          · left; rfl
      · left; rfl
  · left; rfl

/-- **The KV model of a committed watchkv log** is a watchkv log (from the start log). -/
theorem kvRaftOf_wk (P : List (GoString × GoString)) (c₀ : w64) :
    ∀ (A : List EntryModel) (log : mvcc.Log), plainLog (workload P) A → WkLog P log →
      2 ≤ log.length → WkLog P (kvRaftOf c₀ (apply.alarmChain false false false) log A)
  | [], log, _, h, _ => h
  | m :: A, log, hA, h, hl => by
    have hm : plainEntry (workload P) m := hA m (List.mem_cons_self ..)
    have hA' : plainLog (workload P) A := fun x hx => hA x (List.mem_cons_of_mem _ hx)
    show WkLog P (kvRaftOf c₀ _ (kvEntry c₀ _ log m) A)
    rcases kvEntry_wk P c₀ log m hm with he | ⟨cs, hcs, he⟩
    · rw [he]; exact kvRaftOf_wk P c₀ A log hA' h hl
    · rw [he]
      exact kvRaftOf_wk P c₀ A _ hA' (h.snoc hl hcs) (by simp; omega)

end watchkv
end EtcdGrove
end Perennial
