/-
Lean-first (no Rocq counterpart).

**The history of the compactors' key** (`notes/k8s-compactor-plan.md`): when the only writes to
`compactRevKey` are the compactors' rounds (`casTxn ev rev`), every event of the key in a
`KVState`'s history, and its current value, hold `FormatInt(c, 10)` of some revision `c` a
compactor wrote (`KeyHist σ C`).

- `KeyHist.mono`: more revisions keep it;
- `KeyHist_put_other`: a client's plain put of another key keeps it;
- `KeyHist_cas`: a round `casTxn ev rev` keeps it, with `rev` added;
- `KeyHist_nil_changes`, `KeyHist_boot`: a state whose changes are all empty and which lacks the
  key has it (a fresh member's start state, `kvStateOf [[], []]`, revision `1`).

The pure facts on the way: `evsOfRevM_mem` (an event of a revision is one of its changes', a put's
carrying the value it wrote), `revEvents_commit_le` and `changesAt_commit_new` (a commit keeps the
earlier revisions' events and adds its changes at the next revision).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.CasModel
public import Proof.go_etcd_io.etcd.client.v3.WatchStateDefs
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.CompactNoDup

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_compactor

open go_etcd_io.etcd.server.v3.etcdserver mvcc k8s linkv

section kv
variable [GooseExts]

/-- Every event of `compact_rev_key` in `σ`'s history (through its revision) holds `fmtInt c` of
some `c ∈ C`, and its current value too. -/
def KeyHist (σ : KVState) (C : List w64) : Prop :=
  (∀ v, keyValue σ compactRevKey = some v → ∃ c ∈ C, v = fmtInt c (W64 10)) ∧
  (∀ (r : Nat) (ev : mvcc.EvM), r ≤ σ.rev → ev ∈ σ.revEvents r → ev.kv.key = compactRevKey →
    ∃ c ∈ C, ev.kv.value = fmtInt c (W64 10))

theorem KeyHist.mono {σ : KVState} {C C' : List w64} (h : KeyHist σ C) (hs : C ⊆ C') :
    KeyHist σ C' := by
  refine ⟨fun v hv => ?_, fun r ev hr hev hk => ?_⟩
  · obtain ⟨c, hc, he⟩ := h.1 v hv
    exact ⟨c, hs hc, he⟩
  · obtain ⟨c, hc, he⟩ := h.2 r ev hr hev hk
    exact ⟨c, hs hc, he⟩

/-! ## Events and commits (pure) -/

/-- The key-value a put leaves at its key holds the key and the value it wrote. -/
theorem findKey_putKv_kv {s : List EtcdKv} (r : w64) (k v : GoString) (l : w64) {kv : EtcdKv}
    (hs : s.Pairwise etcdKvLess) (h : mvcc.findKey k (putKv r k v l s) = some kv) :
    kv.key = k ∧ kv.value = v := by
  unfold putKv at h
  rw [mvcc.findKey_btInsert _ s hs] at h
  split at h
  · rename_i w hw
    have hk : w.key = k := by simpa using List.find?_some hw
    simp only [hk, ↓reduceIte, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩
  · simp only [↓reduceIte, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩

/-- **An event of a revision is one of its changes'**: the change's key, and a put's value. -/
theorem evsOfRevM_mem {r : Nat} {before : List EtcdKv} {cs : List mvcc.Change}
    (hs : before.Pairwise etcdKvLess) {ev : mvcc.EvM} (h : ev ∈ mvcc.evsOfRevM r before cs) :
    ∃ c ∈ cs, ev.kv.key = c.key ∧ ∀ k v l, c = .put k v l → ev.kv.value = v := by
  unfold mvcc.evsOfRevM at h
  simp only [List.mem_filterMap, List.mem_range, Option.map_eq_some_iff] at h
  obtain ⟨i, -, kv, hkv, rfl⟩ := h
  have hev : (mvcc.evOfKv r kv).kv.key = kv.key ∧ (mvcc.evOfKv r kv).kv.value = kv.value := by
    unfold mvcc.evOfKv; split <;> simp
  rw [hev.1, hev.2]
  unfold mvcc.changeKv at hkv
  cases hc : cs[i]? with
  | none => rw [hc] at hkv; cases hkv
  | some c =>
    refine ⟨c, List.mem_of_getElem? hc, ?_⟩
    rw [hc] at hkv
    cases c with
    | put k v l =>
      simp only at hkv
      rw [List.take_add_one, hc, Option.toList_some] at hkv
      simp only [mvcc.applyChanges, List.foldl_append, List.foldl_cons, List.foldl_nil] at hkv
      have hsrt := mvcc.applyChanges_sorted (W64 r) (cs.take i) hs
      unfold mvcc.applyChanges at hsrt
      obtain ⟨hk, hv⟩ := findKey_putKv_kv (W64 r) k v l hsrt hkv
      refine ⟨hk, ?_⟩
      intro k' v' l' he
      cases he
      exact hv
    | del k =>
      simp only [Option.some.injEq] at hkv
      subst hkv
      refine ⟨rfl, ?_⟩
      intro k' v' l' he
      cases he

/-- A commit keeps the events of the revisions up to the current one. -/
theorem revEvents_commit_le (σ : KVState) (cs : List mvcc.Change) (r : Nat) (hr : r ≤ σ.rev) :
    (σ.commit cs).revEvents r = σ.revEvents r := by
  unfold KVState.revEvents
  rw [KVState.commit_at σ cs (r - 1) (by omega), KVState.commit_changesAt σ cs r hr]

/-- A commit's changes are those of the next revision. -/
theorem changesAt_commit_new (σ : KVState) (cs : List mvcc.Change) (h : cs ≠ []) :
    (σ.commit cs).changesAt (σ.rev + 1) = cs := by
  unfold KVState.commit KVState.changesAt KVState.rev
  have hlt : ¬ (σ.compacted + σ.changes.length + 1 ≤ σ.compacted) := by omega
  simp only [h, hlt, ↓reduceIte]
  rw [show σ.compacted + σ.changes.length + 1 - σ.compacted - 1 =
    σ.changes.length by omega, List.getElem?_append_right (Nat.le_refl _)]
  simp

/-- **A commit keeps `KeyHist`** if the new value is one of `C`'s and its only changes of the key
are puts of one of `C`'s values. -/
theorem KeyHist_commit {σ : KVState} {C : List w64} (cs : List mvcc.Change) (h : KeyHist σ C)
    (hv : ∀ v, keyValue (σ.commit cs) compactRevKey = some v → ∃ c ∈ C, v = fmtInt c (W64 10))
    (hcs : ∀ c ∈ cs, c.key = compactRevKey →
      ∃ v l, c = .put compactRevKey v l ∧ ∃ x ∈ C, v = fmtInt x (W64 10)) :
    KeyHist (σ.commit cs) C := by
  refine ⟨hv, ?_⟩
  intro r ev hr hev hk
  by_cases hc : cs = []
  · subst hc
    rw [KVState.commit_nil] at hr hev
    exact h.2 r ev hr hev hk
  by_cases hle : r ≤ σ.rev
  · rw [revEvents_commit_le σ cs r hle] at hev
    exact h.2 r ev hle hev hk
  · rw [KVState.commit_rev σ cs hc] at hr
    obtain rfl : r = σ.rev + 1 := by omega
    unfold KVState.revEvents at hev
    rw [changesAt_commit_new σ cs hc] at hev
    obtain ⟨c, hcm, hkey, hval⟩ := evsOfRevM_mem (KVStore.kvs_sorted _) hev
    obtain ⟨v, l, rfl, x, hx, rfl⟩ := hcs c hcm (by rw [← hkey]; exact hk)
    exact ⟨x, hx, hval _ _ _ rfl⟩

/-! ## The operations -/

/-- **A client's plain put of another key keeps `KeyHist`.** -/
theorem KeyHist_put_other {σ : KVState} {C : List w64} (k v : GoString) (hk : k ≠ compactRevKey)
    (h : KeyHist σ C) :
    KeyHist (kvOpStep (.put (putWireOf (opPutModel k v []))) σ) C := by
  have hv := keyValue_put_other k v σ hk
  have hst : kvOpStep (.put (putWireOf (opPutModel k v []))) σ = σ ∨
      ∃ cs : List mvcc.Change, kvOpStep (.put (putWireOf (opPutModel k v []))) σ = σ.commit cs ∧
        ∀ c ∈ cs, c.key ≠ compactRevKey := by
    simp only [kvOpStep]
    split
    · exact Or.inl rfl
    split
    · exact Or.inl rfl
    · refine Or.inr ⟨_, rfl, ?_⟩
      intro c hc
      simp only [List.mem_singleton] at hc
      subst hc
      exact hk
  rcases hst with hst | ⟨cs, hst, hcs⟩
  · rw [hst]; exact h
  · rw [hst] at hv ⊢
    refine KeyHist_commit cs h (by rw [hv]; exact h.1) ?_
    intro c hc hck
    exact absurd hck (hcs c hc)

/-- **A winning round commits one put of `FormatInt(rev, 10)` at the key** (or nothing, if the
server rejects the transaction). -/
theorem kvOpStep_cas_win (ev rev : w64) (σ : KVState) (hw : casWins ev rev σ = true) :
    kvOpStep (.txn (casTxn ev rev)) σ = σ ∨
      kvOpStep (.txn (casTxn ev rev)) σ =
        σ.commit [.put compactRevKey (fmtInt rev (W64 10)) (W64 0)] := by
  have hok : txn.txnOk σ.kvs (casTxn ev rev) = true := hw
  simp only [kvOpStep]
  split
  · right
    unfold txn.srvRunTxn
    rw [hok, txnOf_branch]
    simp [tOpOf, txn.srvOps, txn.srvOp]
  · left; rfl

/-- **A compactor's round keeps `KeyHist`, with its revision added**: a losing round changes
nothing; a winning one puts `FormatInt(rev, 10)` at the key. -/
theorem KeyHist_cas {σ : KVState} {C : List w64} (ev rev : w64) (h : KeyHist σ C) :
    KeyHist (kvOpStep (.txn (casTxn ev rev)) σ) (rev :: C) := by
  have h' : KeyHist σ (rev :: C) := h.mono (List.subset_cons_self rev C)
  cases hw : casWins ev rev σ with
  | false => rw [casTxn_lose_same ev rev σ hw]; exact h'
  | true =>
    have hv := casTxn_win_value ev rev σ hw
    have hst := kvOpStep_cas_win ev rev σ hw
    have hvC : ∀ v, keyValue (kvOpStep (.txn (casTxn ev rev)) σ) compactRevKey = some v →
        ∃ c ∈ rev :: C, v = fmtInt c (W64 10) := by
      intro v hv'
      rw [hv] at hv'
      cases hv'
      exact ⟨rev, List.mem_cons_self, rfl⟩
    rcases hst with hst | hst
    · rw [hst] at hvC ⊢
      exact ⟨hvC, h'.2⟩
    · rw [hst] at hvC ⊢
      refine KeyHist_commit _ h' hvC ?_
      intro c hc _
      simp only [List.mem_singleton] at hc
      subst hc
      exact ⟨_, _, rfl, rev, List.mem_cons_self, rfl⟩

/-! ## The start state -/

/-- **A state with no change and without the key has `KeyHist`.** -/
theorem KeyHist_nil_changes {C : List w64} (σ : KVState) (h : ∀ cs ∈ σ.changes, cs = [])
    (hk : keyValue σ compactRevKey = none) : KeyHist σ C := by
  refine ⟨by simp [hk], ?_⟩
  intro r ev _ hev _
  have hc : σ.changesAt r = [] := by
    unfold KVState.changesAt
    split
    · rfl
    · cases hg : σ.changes[r - σ.compacted - 1]? with
      | none => rfl
      | some cs => simpa using h cs (List.mem_of_getElem? hg)
  unfold KVState.revEvents at hev
  rw [hc] at hev
  simp [mvcc.evsOfRevM] at hev

/-- A fresh member's start state lacks the key. -/
theorem keyValue_boot : keyValue (kvStateOf [[], []]) compactRevKey = none := by
  unfold keyValue; rw [kvStateOf_kvs]; rfl

/-- **A fresh member's start state has `KeyHist`** (no revision written). -/
theorem KeyHist_boot : KeyHist (kvStateOf [[], []]) [] :=
  KeyHist_nil_changes _ (by simp [kvStateOf]) keyValue_boot

/-- A fresh member's start state is at revision `1`. -/
theorem kvStateOf_boot_rev : (kvStateOf [[], []]).rev = 1 := by
  rw [kvStateOf_rev]; rfl

/-! ## At most one change a revision -/

/-- Every revision of `σ` has at most one change. -/
def OneChange (σ : KVState) : Prop := ∀ cs ∈ σ.changes, cs.length ≤ 1

/-- A commit of at most one change keeps `OneChange`. -/
theorem OneChange_commit {σ : KVState} (cs : List mvcc.Change) (h : OneChange σ)
    (hcs : cs.length ≤ 1) : OneChange (σ.commit cs) := by
  unfold KVState.commit
  split
  · exact h
  · intro cs' hm
    simp only [List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | rfl
    · exact h cs' hm
    · exact hcs

/-- **A client's plain put keeps `OneChange`** (of any key). -/
theorem OneChange_put {σ : KVState} (k v : GoString) (h : OneChange σ) :
    OneChange (kvOpStep (.put (putWireOf (opPutModel k v []))) σ) := by
  simp only [kvOpStep]
  split
  · exact h
  split
  · exact h
  · exact OneChange_commit _ h (by simp)

/-- **A compactor's round keeps `OneChange`.** -/
theorem OneChange_cas {σ : KVState} (ev rev : w64) (h : OneChange σ) :
    OneChange (kvOpStep (.txn (casTxn ev rev)) σ) := by
  cases hw : casWins ev rev σ with
  | false => rw [casTxn_lose_same ev rev σ hw]; exact h
  | true =>
    rcases kvOpStep_cas_win ev rev σ hw with hst | hst <;> rw [hst]
    · exact h
    · exact OneChange_commit _ h (by simp)

/-- **A fresh member's start state has `OneChange`.** -/
theorem OneChange_boot : OneChange (kvStateOf [[], []]) := by
  intro cs hm
  simp [kvStateOf] at hm
  subst hm
  simp

/-- At most one change has no duplicate key. -/
theorem nodup_keys_of_length_le_one (cs : List mvcc.Change) (h : cs.length ≤ 1) :
    (cs.map mvcc.Change.key).Nodup := by
  match cs, h with
  | [], _ => simp
  | [_], _ => simp
  | _ :: _ :: _, h => simp at h

/-- **A sealed log, prefix of a log whose revisions after `0` have at most one change each,
changes each key at most once a revision** (`etcd_compactwatch.oneChange_of_oneVal`'s analogue). -/
theorem oneChangePerKey_of_one (L C : mvcc.Log) (hov : ∀ cs ∈ C.drop 1, cs.length ≤ 1)
    (hp : L <+: C) (hwf : mvcc.LogWf' L) : mvcc.oneChangePerKey L := by
  intro c cs _ hcs
  have hlt : c.toNat < L.length := (List.getElem?_eq_some_iff.1 hcs).1
  by_cases h0 : c.toNat = 0
  · have hL0 := hwf.1 (by intro h; rw [h] at hlt; simp at hlt)
    rw [h0, hL0] at hcs
    cases hcs
    simp
  · obtain ⟨t, rfl⟩ := hp
    have hC : ((L ++ t).drop 1)[c.toNat - 1]? = some cs := by
      rw [List.getElem?_drop, show 1 + (c.toNat - 1) = c.toNat by omega,
        List.getElem?_append_left hlt]
      exact hcs
    exact nodup_keys_of_length_le_one cs (hov cs (List.mem_of_getElem? hC))

end kv

end k8s_compactor
end EtcdGrove
end Perennial
