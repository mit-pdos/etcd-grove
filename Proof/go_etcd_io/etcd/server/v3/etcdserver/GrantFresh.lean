/-
**A revocable-mode grant's id is fresh in the history** (auth-lease S4, the thaw of 2026-11-18 approved
by the user, option (A)): in the mode-`on` model of a log `A` from a start whose log attaches no key
to a lease, every lease attached to a key at any revision is one of `A`'s revocable-mode grant ids
(`logRevGrantIds .revocable A`), and so is every lease of the table. Since the KV invariant keeps the
log's grant ids distinct (`kvGrantIds`), a grant's id is attached to no key at any revision before its
entry: what `writeGrantG` tells a grant's update (`ProposeOn.lean`).

No compaction premise is needed: the model's log keeps every revision (`kvStateOf` has `compacted =
0`), and a compaction entry does not shorten it.

Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVAuthModel

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode Iris.Std go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [GooseExts]

/-- **The backend's table grows only by a grant's id.** -/
theorem backendTable_ids_sub (rq : apply.IRRModel) (lt : LeaseTable) :
    ∀ i ∈ (backendTable rq lt).ids,
      i ∈ lt.ids ∨ (apply.dispatchKind rq = .leaseGrant ∧ rq.leaseGrant.map (·.id) = some i) := by
  intro i hi
  unfold backendTable at hi
  revert hi
  cases hk : apply.dispatchKind rq <;> simp only [] <;> try exact Or.inl
  case leaseGrant =>
    cases hg : rq.leaseGrant with
    | none => exact Or.inl
    | some g =>
      simp only []
      split
      · intro hi
        unfold LeaseTable.ids at hi
        rw [List.map_append, List.mem_append] at hi
        rcases hi with hi | hi
        · exact Or.inl hi
        · right
          simp only [List.map_cons, List.map_nil, List.mem_singleton] at hi
          exact ⟨trivial, by simp [hi]⟩
      · exact Or.inl
  case leaseRevoke =>
    cases rq.leaseRevoke with
    | none => exact Or.inl
    | some id =>
      simp only []
      split
      · intro hi
        left
        unfold LeaseTable.ids at hi ⊢
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hi
        exact List.mem_map.2 ⟨p, (List.mem_filter.1 hp).1, rfl⟩
      · exact Or.inl

/-- **The chain's table grows only by a grant's id.** -/
theorem chainTable_ids_sub (rq : apply.IRRModel) :
    ∀ (c : apply.Chain) (lt : LeaseTable), ∀ i ∈ (chainTable c rq lt).ids,
      i ∈ lt.ids ∨ (apply.dispatchKind rq = .leaseGrant ∧ rq.leaseGrant.map (·.id) = some i)
  | .backend, lt, i, hi => backendTable_ids_sub rq lt i hi
  | .auth _ c, lt, i, hi => chainTable_ids_sub rq c lt i hi
  | .quota c, lt, i, hi => chainTable_ids_sub rq c lt i hi
  | .capped c, lt, i, hi => by
    simp only [chainTable] at hi; split at hi
    · exact Or.inl hi
    · exact chainTable_ids_sub rq c lt i hi
  | .corrupt c, lt, i, hi => by
    simp only [chainTable] at hi; split at hi
    · exact Or.inl hi
    · exact chainTable_ids_sub rq c lt i hi

/-- **An entry's table grows only by its revocable-mode grant id** (`entryRevGrantId .revocable`). -/
theorem kvTable_ids_sub (c₀ : w64) (ch : apply.Chain) (lt : LeaseTable) (m : EntryModel) :
    ∀ i ∈ (kvTable c₀ ch lt m).ids, i ∈ lt.ids ∨ entryRevGrantId .revocable m = some i := by
  intro i hi
  unfold kvTable at hi
  by_cases ht : m.typ = W32 0
  · simp only [ht, ↓reduceIte] at hi
    by_cases hd : m.data = []
    · simp only [hd, ↓reduceIte] at hi; exact Or.inl hi
    · simp only [hd, ↓reduceIte] at hi
      cases hdec : apply.irrDecode m.data with
      | none => rw [hdec] at hi; exact Or.inl hi
      | some rq =>
        rw [hdec] at hi
        simp only [] at hi
        unfold dispatchTable at hi
        split at hi
        · exact Or.inl hi
        · rcases chainTable_ids_sub rq ch lt i hi with h | ⟨hk, hg⟩
          · exact Or.inl h
          · right
            unfold entryRevGrantId
            simp only [ht, ↓reduceIte, hdec, Option.bind_some]
            unfold rqRevGrantId
            simp only [hk, and_self, ↓reduceIte]
            exact hg
  · simp only [ht, ↓reduceIte] at hi; exact Or.inl hi

/-- **The mode-`on` step's table grows only by the entry's revocable-mode grant id.** -/
theorem kvEntryOn_ids_sub (c₀ : w64) (ch : apply.Chain) (s : OnState) (m : EntryModel) :
    ∀ i ∈ (kvEntryOn c₀ ch s m).2.2.ids, i ∈ s.2.2.ids ∨ entryRevGrantId .revocable m = some i := by
  intro i hi
  unfold kvEntryOn at hi
  split at hi
  · split at hi
    · split at hi
      · exact Or.inl hi
      · split at hi
        · exact Or.inl hi
        · split at hi
          · exact Or.inl hi
          · exact kvTable_ids_sub c₀ ch s.2.2 m i hi
    · exact Or.inl hi
  · exact kvTable_ids_sub c₀ ch s.2.2 m i hi

/-- **The history's leases, from the grant ids `G`**: the table's ids among `G`, the current state's
leases live in the table, and every revision's leases `0` or in `G`. -/
def histLeasesIn (G : List w64) (s : OnState) : Prop :=
  (∀ i ∈ s.2.2.ids, i ∈ G) ∧ liveSt s.2.2.ids (mvcc.stateAfter s.2.1) ∧
    ∀ r < s.2.1.length, liveSt G (mvcc.stateAt s.2.1 r)

theorem histLeasesIn_kvEntryOn (c₀ : w64) (ch : apply.Chain) (G : List w64) (s : OnState)
    (m : EntryModel) (h : histLeasesIn G s) :
    histLeasesIn (G ++ (entryRevGrantId .revocable m).toList) (kvEntryOn c₀ ch s m) := by
  obtain ⟨ht, hl, hh⟩ := h
  have hG : ∀ i ∈ G, i ∈ G ++ (entryRevGrantId .revocable m).toList :=
    fun i hi => List.mem_append_left _ hi
  have ht' : ∀ i ∈ (kvEntryOn c₀ ch s m).2.2.ids, i ∈ G ++ (entryRevGrantId .revocable m).toList := by
    intro i hi
    rcases kvEntryOn_ids_sub c₀ ch s m i hi with h | h
    · exact hG i (ht i h)
    · exact List.mem_append_right _ (by rw [h]; simp)
  have hl' := liveSt_kvEntryOn c₀ ch s m hl
  refine ⟨ht', hl', fun r hr => ?_⟩
  rcases kvEntryOn_grow c₀ ch s m with he | ⟨cs, he⟩
  · rw [he] at hr ⊢; exact liveSt_mono hG (hh r hr)
  · rw [he] at hr ⊢
    by_cases hlt : r < s.2.1.length
    · rw [mvcc.stateAt_append_lt _ _ hlt]; exact liveSt_mono hG (hh r hlt)
    · rw [mvcc.stateAt_append_ge _ _ (by omega), ← mvcc.stateAfter_append, ← he]
      exact liveSt_mono ht' hl'

theorem histLeasesIn_kvRaftOfOn (c₀ : w64) (ch : apply.Chain) :
    ∀ (A : List EntryModel) (G : List w64) (s : OnState), histLeasesIn G s →
      histLeasesIn (G ++ logRevGrantIds .revocable A) (kvRaftOfOn c₀ ch s A)
  | [], G, s, h => by simpa [logRevGrantIds, kvRaftOfOn_nil] using h
  | m :: A, G, s, h => by
    have h1 := histLeasesIn_kvEntryOn c₀ ch G s m h
    have h2 := histLeasesIn_kvRaftOfOn c₀ ch A _ _ h1
    have he : logRevGrantIds .revocable (m :: A) =
        (entryRevGrantId .revocable m).toList ++ logRevGrantIds .revocable A := by
      unfold logRevGrantIds
      cases hm : entryRevGrantId .revocable m <;> simp [hm]
    rw [he, ← List.append_assoc]
    exact h2

/-- The start: a log attaching no key to a lease, the empty table. -/
theorem histLeasesIn_start (st₀ : auth.AuthState) (log₀ : mvcc.Log) (h : mvcc.LogNoLease log₀) :
    histLeasesIn [] (st₀, log₀, []) := by
  refine ⟨fun i hi => by simp [LeaseTable.ids] at hi, fun kv hkv => Or.inl
    (mvcc.stateAfter_leaseZero log₀ h kv hkv), fun r _ kv hkv => Or.inl ?_⟩
  refine mvcc.stateAfter_leaseZero (log₀.take (r + 1)) (fun cs hcs => h cs (List.mem_of_mem_take hcs))
    kv hkv

/-- **Every lease attached at any revision of the mode-`on` model of `A` is one of `A`'s
revocable-mode grant ids** (from a start whose log attaches no key to a lease). -/
theorem kvRaftOfOn_hist_leases (c₀ : w64) (ch : apply.Chain) (st₀ : auth.AuthState) (log₀ : mvcc.Log)
    (A : List EntryModel) (h : mvcc.LogNoLease log₀) (r : Nat)
    (hr : r < (kvRaftOfOn c₀ ch (st₀, log₀, []) A).2.1.length)
    (kv : EtcdKv) (hkv : kv ∈ mvcc.stateAt (kvRaftOfOn c₀ ch (st₀, log₀, []) A).2.1 r)
    (h0 : kv.lease ≠ W64 0) : kv.lease ∈ logRevGrantIds .revocable A := by
  have H := histLeasesIn_kvRaftOfOn c₀ ch A [] _ (histLeasesIn_start st₀ log₀ h)
  rw [List.nil_append] at H
  rcases H.2.2 r hr kv hkv with h' | h'
  · exact absurd h' h0
  · exact h'

/-- **A grant's id is fresh in the history of the state before its entry**: at the revocable mode,
a grant id `g` not among the committed log `L`'s grant ids is the lease of no key at any revision of
`L`'s state (`kvStateOf` of the mode-`on` model). -/
theorem kvStateOf_grant_fresh (γk : KVNames) (st₀ : auth.AuthState) (L : List EntryModel)
    (h0 : mvcc.LogNoLease γk.log0) (hne : γk.log0 ≠ []) (hrev : γk.lm = .revocable) (g : w64)
    (hg : g ∉ logRevGrantIds γk.lm L) :
    ∀ r ≤ (kvStateOf (kvModelOn γk st₀ L) (kvLeasesOn γk st₀ L)).rev,
      ∀ kv ∈ ((kvStateOf (kvModelOn γk st₀ L) (kvLeasesOn γk st₀ L)).at r).kvs,
        kv.lease ≠ W64 0 → kv.lease ≠ g := by
  intro r hr kv hkv hk0 he
  rw [kvStateOf_rev] at hr
  have hlen : 0 < (kvModelOn γk st₀ L).length := by
    have h1 := (kvRaftOfOn_extends γk.c0 γk.ch0 (st₀, γk.log0, []) L).length_le
    have h2 := List.length_pos_iff.2 hne
    unfold kvModelOn; simp only at h1; omega
  rw [kvStateOf_at_kvs _ r hr] at hkv
  have := kvRaftOfOn_hist_leases γk.c0 γk.ch0 st₀ γk.log0 L h0 r (by unfold kvModelOn at hr hlen; omega)
    kv hkv hk0
  rw [hrev] at hg
  exact hg (he ▸ this)

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- The log's grant ids are distinct (`kvGrantIds_nodup_of`), the resource kept. -/
theorem kvGrantIds_nodup (γk : KVNames) (L : List EntryModel) :
    kvGrantIds (GF := GF) γk L ⊢ ⌜(logRevGrantIds γk.lm L).Nodup⌝ ∗ kvGrantIds γk L := by
  iintro HG
  iunfold kvGrantIds at HG
  icases HG with ⟨%U, %HU, HUs⟩
  isplitr
  · ipureintro; exact kvGrantIds_nodup_of HU
  iunfold kvGrantIds
  iexists U
  iframe HUs
  ipureintro; exact HU

end defs
