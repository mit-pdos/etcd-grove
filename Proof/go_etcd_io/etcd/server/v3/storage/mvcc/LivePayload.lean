/-
The live key-value payload (etcd-io/etcd#22475, `etcd_mvcc_live_kv_payload_bytes`), the pure
model: the sum of `len(key) + len(value)` over the key-values of a state (`payload`), a key's
part of it (`liveSz`), and how one change moves both (`payload_applyChange`). The key index
keeps, beside each key's index, the key's part at the writer's log (`keyIndex.liveSize`,
`InvIndex.lean`'s `idxLockInv`), and a write transaction accumulates the change of the payload
over its pending revision (`storeTxnWrite.liveSizeDelta`, `pendDelta`). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Compact
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Hist

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

/-- A key-value's payload: `len(key) + len(value)`. -/
def kvSz (kv : EtcdKv) : Nat := kv.key.length + kv.value.length

/-- The live payload of a state: the sum of its key-values' payloads. -/
def payload (s : List EtcdKv) : Nat := (s.map kvSz).sum

/-- A key's part of the live payload: its key-value's payload, `0` if it is absent. -/
def liveSz (s : List EtcdKv) (k : GoString) : Nat := ((findKey k s).map kvSz).getD 0

/-- The key's part of the live payload after the log, as the index keeps it (`liveSize`). -/
def liveW (log : Log) (k : GoString) : w64 := W64 (liveSz (stateAfter log) k : Int)

/-- The live payload after the log. -/
def payloadW (log : Log) : w64 := W64 (payload (stateAfter log) : Int)

/-- What a write transaction has added to the live payload over its pending revision `pend`
(`storeTxnWrite.liveSizeDelta`), mod `2^64`. -/
def pendDelta (ilog : Log) (pend : List Change) : w64 := payloadW (ilog ++ [pend]) - payloadW ilog

theorem payload_cons (w : EtcdKv) (ws : List EtcdKv) : payload (w :: ws) = kvSz w + payload ws := by
  simp [payload]

theorem liveSz_cons (w : EtcdKv) (ws : List EtcdKv) (k : GoString) :
    liveSz (w :: ws) k = if w.key = k then kvSz w else liveSz ws k := by
  unfold liveSz; rw [findKey_cons]; by_cases h : w.key = k <;> simp [h]

theorem liveSz_none {s : List EtcdKv} {k : GoString} (h : findKey k s = none) : liveSz s k = 0 := by
  simp [liveSz, h]

/-- A key below the first key of a sorted state is absent. -/
theorem findKey_below : ∀ (s : List EtcdKv), s.Pairwise etcdKvLess → ∀ (w : EtcdKv) (k : GoString),
    (∀ x ∈ s, go.GoStringLt w.key x.key ∨ x = w) → go.GoStringLt k w.key → findKey k s = none
  | [], _, _, _, _, _ => rfl
  | x :: xs, hs, w, k, hall, hk => by
    rw [List.pairwise_cons] at hs
    rw [findKey_cons]
    have hx : x.key ≠ k := by
      intro hxk
      rcases hall x List.mem_cons_self with h | h
      · rw [hxk] at h; exact goStringLt_irrefl _ (goStringLt_trans hk h)
      · rw [h] at hxk; rw [hxk] at hk; exact goStringLt_irrefl _ hk
    rw [if_neg hx]
    exact findKey_below xs hs.2 w k (fun y hy => hall y (List.mem_cons_of_mem _ hy)) hk

/-- `btInsert` of a key-value into a sorted state: the payload loses the key's old part and
gains the new key-value's. -/
theorem payload_btInsert (nv : EtcdKv) :
    ∀ (s : List EtcdKv), s.Pairwise etcdKvLess →
      payload (btInsert etcdKvLess nv s) + liveSz s nv.key = payload s + kvSz nv
  | [], _ => by simp [btInsert, payload, liveSz, findKey]
  | w :: ws, hs => by
    rw [List.pairwise_cons] at hs
    unfold btInsert
    split
    · rename_i hwv
      have hne : w.key ≠ nv.key := by
        intro h; unfold etcdKvLess at hwv; rw [h] at hwv; exact goStringLt_irrefl _ hwv
      rw [payload_cons, payload_cons, liveSz_cons, if_neg hne]
      have := payload_btInsert nv ws hs.2
      omega
    · split
      · rename_i hwv hvw
        have hne : w.key ≠ nv.key := by
          intro h; unfold etcdKvLess at hvw; rw [h] at hvw; exact goStringLt_irrefl _ hvw
        have hnone : findKey nv.key ws = none :=
          findKey_below ws hs.2 w nv.key (fun x hx => Or.inl (hs.1 x hx)) hvw
        rw [payload_cons, payload_cons, liveSz_cons, if_neg hne, liveSz_none hnone]
        omega
      · rename_i hwv hvw
        have heq : w.key = nv.key := goStringLt_eq_of_not_lt hwv hvw
        rw [payload_cons, payload_cons, liveSz_cons, if_pos heq]
        omega

/-- With no key-value of `k`, filtering `k` out changes nothing. -/
theorem filter_ne_of_none : ∀ (s : List EtcdKv) (k : GoString), findKey k s = none →
    (s.filter fun x => !decide (x.key = k)) = s
  | [], _, _ => rfl
  | w :: ws, k, h => by
    rw [findKey_cons] at h
    by_cases hw : w.key = k
    · rw [if_pos hw] at h; cases h
    · rw [if_neg hw] at h
      rw [List.filter_cons, if_pos (by simp [hw]), filter_ne_of_none ws k h]

/-- Deleting `k` from a sorted state: the payload loses the key's part. -/
theorem payload_filter : ∀ (s : List EtcdKv), s.Pairwise etcdKvLess → ∀ (k : GoString),
    payload (s.filter fun x => !decide (x.key = k)) + liveSz s k = payload s
  | [], _, _ => by simp [payload, liveSz, findKey]
  | w :: ws, hs, k => by
    rw [List.pairwise_cons] at hs
    rw [List.filter_cons, liveSz_cons]
    by_cases hw : w.key = k
    · have hnone : findKey k ws = none := by
        rw [← hw]
        exact findKey_below ws hs.2 w w.key (fun x hx => Or.inl (hs.1 x hx)) |> fun f => by
          cases hf : findKey w.key ws with
          | none => rfl
          | some kv =>
            exfalso
            have hk := findKey_key hf
            have hm := List.mem_of_find?_eq_some (by unfold findKey at hf; exact hf)
            have := hs.1 kv hm
            unfold etcdKvLess at this
            rw [hk] at this
            exact goStringLt_irrefl _ this
      simp only [hw, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [filter_ne_of_none ws k hnone, payload_cons]
      omega
    · simp only [hw, decide_false, Bool.not_false, ↓reduceIte, payload_cons]
      have := payload_filter ws hs.2 k
      omega

/-- The key-value `putKv` writes has the put's key and value. -/
theorem putKv_nv (r : w64) (k v : GoString) (l : w64) (s : List EtcdKv) :
    ∃ nv : EtcdKv, putKv r k v l s = btInsert etcdKvLess nv s ∧ nv.key = k ∧ nv.value = v := by
  unfold putKv
  cases h : s.find? (fun v => decide (v.key = k)) with
  | none => exact ⟨_, rfl, rfl, rfl⟩
  | some w =>
    have hk : w.key = k := by simpa using List.find?_some h
    exact ⟨_, rfl, hk, rfl⟩

/-- **One change moves the payload by the key's part** (on a sorted state). -/
theorem payload_applyChange {s : List EtcdKv} (hs : s.Pairwise etcdKvLess) (r : w64) (c : Change) :
    payload (applyChange r s c) + liveSz s c.key = payload s + liveSz (applyChange r s c) c.key := by
  cases c with
  | put k v l =>
    obtain ⟨nv, hput, hk, hv⟩ := putKv_nv r k v l s
    simp only [applyChange, Change.key]
    rw [hput]
    have h1 := payload_btInsert nv s hs
    have h2 : liveSz (btInsert etcdKvLess nv s) k = kvSz nv := by
      unfold liveSz
      rw [findKey_btInsert nv s hs k, if_pos hk]
      rfl
    rw [h2, ← hk]
    exact h1
  | del k =>
    simp only [applyChange, Change.key]
    have h1 := payload_filter s hs k
    have h2 : liveSz (s.filter fun x => !decide (x.key = k)) k = 0 :=
      liveSz_none (by rw [findKey_filter_ne]; simp)
    rw [h2]
    omega

/-- After a put, the key's part is the put's `len(key) + len(value)`. -/
theorem liveSz_put_self {s : List EtcdKv} (hs : s.Pairwise etcdKvLess) (r : w64) (k v : GoString)
    (l : w64) : liveSz (applyChange r s (.put k v l)) k = k.length + v.length := by
  obtain ⟨nv, hput, hk, hv⟩ := putKv_nv r k v l s
  simp only [applyChange]
  rw [hput]
  unfold liveSz
  rw [findKey_btInsert nv s hs k, if_pos hk]
  simp [kvSz, hk, hv]

/-- After a delete, the key's part is `0`. -/
theorem liveSz_del_self (r : w64) (s : List EtcdKv) (k : GoString) :
    liveSz (applyChange r s (.del k)) k = 0 :=
  liveSz_none (by simp only [applyChange]; rw [findKey_filter_ne]; simp)

/-- A change leaves the other keys' parts alone. -/
theorem liveSz_applyChange_other {s : List EtcdKv} (hs : s.Pairwise etcdKvLess) (r : w64) (c : Change)
    (k : GoString) (hne : c.key ≠ k) : liveSz (applyChange r s c) k = liveSz s k := by
  cases c with
  | put k' v l =>
    unfold liveSz
    simp only [applyChange]
    rw [findKey_putKv_other hs r k k' v l hne]
  | del k' =>
    unfold liveSz
    simp only [applyChange]
    rw [findKey_filter_ne, if_neg (show ¬ k' = k from hne)]

/-- The writer's next change, as a state step. -/
theorem stateAfter_snoc (ilog : Log) (pend : List Change) (c : Change) :
    stateAfter (ilog ++ [pend ++ [c]]) =
      applyChange (W64 ilog.length) (stateAfter (ilog ++ [pend])) c := by
  rw [stateAfter_append, stateAfter_append]
  unfold applyChanges
  rw [List.foldl_append]
  rfl

/-- The key's part through the writer's next change, of another key. -/
theorem liveW_snoc_other (ilog : Log) (pend : List Change) (c : Change) (k : GoString)
    (hne : c.key ≠ k) : liveW (ilog ++ [pend ++ [c]]) k = liveW (ilog ++ [pend]) k := by
  unfold liveW
  rw [stateAfter_snoc, liveSz_applyChange_other (stateAfter_sorted _) _ c k hne]

theorem liveW_snoc_put (ilog : Log) (pend : List Change) (k v : GoString) (l : w64) :
    liveW (ilog ++ [pend ++ [.put k v l]]) k = W64 ((k.length + v.length : Nat) : Int) := by
  unfold liveW
  rw [stateAfter_snoc, liveSz_put_self (stateAfter_sorted _)]

theorem liveW_snoc_del (ilog : Log) (pend : List Change) (k : GoString) :
    liveW (ilog ++ [pend ++ [.del k]]) k = W64 0 := by
  unfold liveW
  rw [stateAfter_snoc, liveSz_del_self]
  rfl

theorem W64_natCast_add (a b : Nat) :
    W64 ((a + b : Nat) : Int) = W64 (a : Int) + W64 (b : Int) := by
  rw [Int.natCast_add]; exact BitVec.ofInt_add _ _

/-- **The transaction's delta through a change**: what the change adds to the payload is the
key's part after it less the key's part before it. -/
theorem pendDelta_snoc (ilog : Log) (pend : List Change) (c : Change) :
    pendDelta ilog (pend ++ [c]) =
      pendDelta ilog pend + (liveW (ilog ++ [pend ++ [c]]) c.key - liveW (ilog ++ [pend]) c.key) := by
  unfold pendDelta payloadW liveW
  have h := payload_applyChange (stateAfter_sorted (ilog ++ [pend])) (W64 ilog.length) c
  rw [← stateAfter_snoc] at h
  have h' := congrArg (fun n : Nat => W64 (n : Int)) h
  simp only [W64_natCast_add] at h'
  generalize W64 (payload (stateAfter (ilog ++ [pend ++ [c]])) : Int) = a at h' ⊢
  generalize W64 (payload (stateAfter (ilog ++ [pend])) : Int) = b at h' ⊢
  generalize W64 (liveSz (stateAfter (ilog ++ [pend ++ [c]])) c.key : Int) = x at h' ⊢
  generalize W64 (liveSz (stateAfter (ilog ++ [pend])) c.key : Int) = y at h' ⊢
  generalize W64 (payload (stateAfter ilog) : Int) = p
  bv_omega

/-- An empty pending revision adds nothing. -/
theorem pendDelta_nil (ilog : Log) : pendDelta ilog [] = W64 0 := by
  unfold pendDelta payloadW
  rw [stateAfter_append]
  simp [applyChanges]

theorem pendDelta_nil' (ilog : Log) : pendDelta ilog [] = (0 : w64) := by
  rw [pendDelta_nil]; rfl

/-- An empty pending revision leaves the payload (etcd-io/etcd#22096: the write transaction's
counter starts at the committed log's payload). -/
theorem payloadW_nil (ilog : Log) : payloadW (ilog ++ [[]]) = payloadW ilog := by
  have h := pendDelta_nil' ilog
  unfold pendDelta at h
  generalize payloadW (ilog ++ [[]]) = a at h ⊢
  generalize payloadW ilog = b at h ⊢
  bv_omega

/-- **The payload through a change** (etcd-io/etcd#22096: the counter's update by `put` and
`delete`): the payload before it plus the key's part after it less its part before it. -/
theorem payloadW_snoc (ilog : Log) (pend : List Change) (c : Change) :
    payloadW (ilog ++ [pend ++ [c]]) =
      payloadW (ilog ++ [pend]) + (liveW (ilog ++ [pend ++ [c]]) c.key - liveW (ilog ++ [pend]) c.key) := by
  have h := pendDelta_snoc ilog pend c
  unfold pendDelta at h
  generalize payloadW (ilog ++ [pend ++ [c]]) = a at h ⊢
  generalize payloadW (ilog ++ [pend]) = b at h ⊢
  generalize payloadW ilog = p at h ⊢
  generalize liveW (ilog ++ [pend ++ [c]]) c.key - liveW (ilog ++ [pend]) c.key = d at h ⊢
  bv_omega

/-- The initial log's payload (`NewStore`'s, revision 0 and 1, empty). -/
theorem payloadW_init : payloadW ([[], []] : Log) = (0 : w64) := by
  unfold payloadW
  rfl

/-- **A key without an index has no live part**: the index holds the events of a well-formed
log `log`, compacted at levels at most `cmax` below its last revision; a key it has no index of
is absent from the state after `log`. -/
theorem liveW_absent (log : Log) (hb : LogB log) (hwf : LogWf' log) (hne : log ≠ []) {cmax : Int}
    {idx : IndexM} (h : IdxCRep cmax (evsOf log) idx) (hc : cmax < log.length) (k : GoString)
    (hk : idxGet idx k = none) : liveW log k = W64 0 := by
  have hlen := hb.1
  have hpos : 0 < log.length := List.length_pos_iff.2 hne
  have hz : cmax ≤ sint.Z (W64 ((log.length - 1 : Nat) : Int)) := by
    have : sint.Z (W64 ((log.length - 1 : Nat) : Int)) = (log.length - 1 : Nat) := by word
    omega
  have hat := IdxCRep.kiAt log hb h _ hz k
  unfold kiAt at hat
  rw [hk] at hat
  simp only [Option.getD_none, kiGet_kiEmpty] at hat
  have hlink := keyLink_of_rev k log.reverse (by simp; exact hlen)
    (fun cs hcs => hb.2 cs (List.mem_reverse.1 hcs)) (by rw [List.reverse_reverse]; exact hwf)
  rw [List.reverse_reverse] at hlink
  have hm := hlink.match_ (log.length - 1) (by omega)
  rw [← hat] at hm
  have := KvMatch_none_left hm
  rw [stateAt_last] at this
  unfold liveW
  rw [liveSz_none this]
  rfl

/-! ### The state is a function of the events -/

/-- The state the events build: each change applied at its event's main revision. -/
def stateOfEvs (evs : List Ev) : List EtcdKv :=
  evs.foldl (fun s e => applyChange e.rev.main s e.change) []

theorem foldl_zipIdx_fst {α β : Type} (f : β → α → β) : ∀ (cs : List α) (n : Nat) (s : β),
    (cs.zipIdx n).foldl (fun s p => f s p.1) s = cs.foldl f s
  | [], _, _ => rfl
  | c :: cs, n, s => by
    rw [List.zipIdx_cons, List.foldl_cons, List.foldl_cons]
    exact foldl_zipIdx_fst f cs (n + 1) (f s c)

theorem foldl_evsOfRev (r : Nat) (cs : List Change) (s : List EtcdKv) :
    (evsOfRev r cs).foldl (fun s e => applyChange e.rev.main s e.change) s = applyChanges (W64 r) s cs := by
  unfold evsOfRev applyChanges
  rw [List.foldl_map]
  exact foldl_zipIdx_fst (applyChange (W64 r)) cs 0 s

theorem stateAfter_eq_stateOfEvs_rev : ∀ (rl : Log),
    stateAfter rl.reverse = stateOfEvs (evsOf rl.reverse)
  | [] => rfl
  | cs :: rl => by
    rw [List.reverse_cons, stateAfter_append, evsOf_append, stateAfter_eq_stateOfEvs_rev rl]
    unfold stateOfEvs
    rw [List.foldl_append, foldl_evsOfRev]

theorem stateAfter_eq_stateOfEvs (log : Log) : stateAfter log = stateOfEvs (evsOf log) := by
  have := stateAfter_eq_stateOfEvs_rev log.reverse
  rw [List.reverse_reverse] at this
  exact this

/-- Two logs of the same events have the same live parts. -/
theorem liveW_congr_evs {log log' : Log} (h : evsOf log = evsOf log') (k : GoString) :
    liveW log k = liveW log' k := by
  unfold liveW; rw [stateAfter_eq_stateOfEvs, stateAfter_eq_stateOfEvs, h]

end mvcc
end EtcdGrove
end Perennial
