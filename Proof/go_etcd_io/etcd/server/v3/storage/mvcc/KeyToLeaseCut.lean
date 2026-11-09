/-
**`restore`'s map of keys to leases, from a compacted image** (2026-11-06). Lean-first (no Rocq
counterpart). Pure.

`restoreChunk` builds `keyToLease` from the `Key` bucket's entries in revision order (`ktlApply`,
`KeyToLease.lean`). Over a compacted image of the log `L` (`entsCutAt L c ents`), the map it builds
is the lessor's item map of `L`'s final state (`ktlApply_cut`): a key's value is its last entry's;
the image drops, per key, a prefix of the entries, and drops all of a key's entries only when the
key is absent from the final state (a live key's latest revision is one compaction keeps,
`named_not_del`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.KeyToLease
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.LeaseItems
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.CutDefs
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvIndexRestore
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.SyncModel

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open go_etcd_io.etcd.server.v3.lease

/-- The value an entry leaves for its key in `keyToLease`: none for a tombstone or lease `0`. -/
def ktlVal (e : KvEnt) : Option w64 := if e.tomb then none else kvLease e.kv

/-- The last of the entries `es` of key `k`. -/
def ktlLast (k : GoString) (es : List KvEnt) : Option KvEnt :=
  (es.filter fun e => decide (e.kv.key = k)).getLast?

theorem ktlStep_lookup (M : GMap GoString w64) (e : KvEnt) (k : GoString) :
    (ktlStep M e).lookup k = if e.kv.key = k then ktlVal e else M.lookup k := by
  unfold ktlStep ktlVal kvLease
  by_cases ht : e.tomb = true <;> by_cases hl : e.kv.lease = W64 0 <;> by_cases hk : e.kv.key = k <;>
    simp only [ht, hl, hk, Bool.false_eq_true, ↓reduceIte] <;> simp [hk]

/-- **A key's value is its last entry's** (`M`'s if it has none). -/
theorem ktlApply_lookup (k : GoString) (es : List KvEnt) :
    ∀ (M : GMap GoString w64), (ktlApply M es).lookup k = (ktlLast k es).elim (M.lookup k) ktlVal := by
  refine snoc_induction (P := fun es => ∀ M : GMap GoString w64,
    (ktlApply M es).lookup k = (ktlLast k es).elim (M.lookup k) ktlVal) ?_ ?_ es
  · intro M; rfl
  · intro es e ih M
    rw [ktlApply_snoc, ktlStep_lookup]
    unfold ktlLast
    rw [List.filter_append]
    by_cases hk : e.kv.key = k
    · simp [hk]
    · rw [if_neg hk, ih M]
      unfold ktlLast
      simp [hk]

/-- `M` holds the leases of the state `s`, key by key. -/
def ktlAgree (M : GMap GoString w64) (s : List EtcdKv) : Prop :=
  ∀ k, M.lookup k = (findKey k s).bind kvLease

/-- **One revision's entries** keep the map the leases of the state. -/
theorem ktlAgree_rev (r : Nat) (b : List EtcdKv) (hb : b.Pairwise etcdKvLess) (cs : List Change)
    (M : GMap GoString w64) (hM : ktlAgree M b) : ∀ i, i ≤ cs.length →
    ktlAgree (ktlApply M ((List.range i).filterMap fun j =>
      (changeKv (W64 r) b cs j).map fun kv =>
        (⟨⟨W64 r, W64 j⟩, (cs.getD j (.del [])).isDel, kv⟩ : KvEnt)))
      (applyChanges (W64 r) b (cs.take i))
  | 0, _ => by simpa [applyChanges, ktlApply] using hM
  | i + 1, hi => by
    have hlt : i < cs.length := by omega
    have ih := ktlAgree_rev r b hb cs M hM i (by omega)
    obtain ⟨c, hc⟩ : ∃ c, cs[i]? = some c := ⟨_, List.getElem?_eq_getElem hlt⟩
    obtain ⟨kv, hkv⟩ := changeKv_isSome (W64 r) b hb cs hlt
    rw [List.range_succ, List.filterMap_append, ktlApply_append]
    simp only [List.filterMap_cons, List.filterMap_nil, hkv, Option.map_some]
    rw [show cs.getD i (.del []) = c by simp [List.getD_eq_getElem?_getD, hc]]
    rw [take_succ_getElem cs i c hc, applyChanges_append_singleton]
    have hs := applyChanges_sorted (W64 r) (cs.take i) hb
    intro k
    show (ktlStep _ _).lookup k = _
    rw [ktlStep_lookup, ih k]
    unfold changeKv at hkv
    rw [hc] at hkv
    cases c with
    | del k' =>
      simp only [Option.some.injEq] at hkv
      subst hkv
      simp only [applyChange, ktlVal, Change.isDel, zeroKv]
      rw [findKey_filter_ne]
      by_cases h : k' = k <;> simp [h]
    | put k' v l =>
      simp only at hkv
      rw [take_succ_getElem cs i _ hc, applyChanges_append_singleton] at hkv
      simp only [applyChange] at hkv ⊢
      have hkk := findKey_key hkv
      by_cases h : k' = k
      · subst h
        rw [if_pos hkk, hkv]
        simp [ktlVal, Change.isDel]
      · rw [if_neg (by rw [hkk]; exact h), findKey_putKv_other hs _ k k' v l h]

/-- **The whole log's entries** give the leases of its final state. -/
theorem ktlAgree_logEnts (L : Log) (h0 : L ≠ [] → L[0]? = some []) :
    ktlAgree (ktlApply ∅ (logEnts L 0 L.length)) (stateAfter L) := by
  revert h0
  refine snoc_induction (P := fun L => (L ≠ [] → L[0]? = some []) →
    ktlAgree (ktlApply ∅ (logEnts L 0 L.length)) (stateAfter L)) ?_ ?_ L
  · intro _ k; rfl
  · intro log cs ih h0
    have ih' := ih (fun hne => by
      have := h0 (by simp)
      rw [List.getElem?_append_left (by cases log <;> simp_all)] at this
      exact this)
    have hbefore : stateAt (log ++ [cs]) (log.length - 1) = stateAfter log ∧
        (log = [] → cs = []) := by
      by_cases hne : log = []
      · subst hne
        have : cs = [] := by simpa using h0 (by simp)
        subst this
        exact ⟨rfl, fun _ => rfl⟩
      · refine ⟨?_, fun h => absurd h hne⟩
        have hl : 0 < log.length := List.length_pos_iff.2 hne
        rw [stateAt_append_lt log cs (by omega)]
        unfold stateAt
        rw [List.take_of_length_le (by omega)]
    rw [List.length_append, List.length_singleton, logEnts_snoc, hbefore.1, ktlApply_append,
      stateAfter_append, entsOfRev_range]
    have := ktlAgree_rev log.length (stateAfter log) (stateAfter_sorted log) cs _ ih' cs.length
      (Nat.le_refl _)
    rwa [List.take_length] at this

/-- `Rev.lt` is irreflexive. -/
theorem Rev.lt_irrefl (a : Rev) : ¬ Rev.lt a a := by
  unfold Rev.lt; omega

/-- The last element of a strictly sorted list, if in a sublist, is the sublist's last. -/
theorem getLast?_sublist_of_mem {α : Type} {R : α → α → Prop} (hirr : ∀ a, ¬ R a a)
    {l' l : List α} {x : α} (hs : l'.Sublist l) (hp : l.Pairwise R) (hl : l.getLast? = some x)
    (hx : x ∈ l') : l'.getLast? = some x := by
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.1 hl
  obtain ⟨l1, l2, rfl, h1, h2⟩ := List.sublist_append_iff.1 hs
  rcases l2 with _ | ⟨y, t⟩
  · exfalso
    simp only [List.append_nil] at hx
    exact hirr x ((List.pairwise_append.1 hp).2.2 x (h1.subset hx) x (by simp))
  · have hlen := h2.length_le
    have hy : y ∈ [x] := h2.subset (by simp)
    simp only [List.length_cons, List.length_nil] at hlen
    have ht : t = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst ht
    simp only [List.mem_singleton] at hy
    subst hy
    simp

/-- **A live key keeps an entry in the image**: the key's latest revision is the one a read at the
last revision names, which compaction never deletes (`named_not_del`). -/
theorem cut_live_ent (L : Log) (c : Int) (ents : List KvEnt) (hb : LogB L) (hwf : LogWf L)
    (hcut : entsCutAt L c ents) (k : GoString) (kv : EtcdKv)
    (hf : findKey k (stateAfter L) = some kv) : ∃ e ∈ ents, e.kv.key = k := by
  have hne : L ≠ [] := by
    intro h; subst h; have := hwf.1; simp at this
  have hl : 0 < L.length := List.length_pos_iff.2 hne
  have hlen := hb.1
  have hS : stateAt L (L.length - 1) = stateAfter L := by
    unfold stateAt; rw [List.take_of_length_le (by omega)]
  have hm := kiGet_indexOf L hb.1 hb.2 hwf k (L.length - 1) (by omega)
  rw [idxGet_indexOf_bind, hS, hf] at hm
  generalize hg : kiGet (kiOfKey (evsOf L) k) (W64 ((L.length - 1 : Nat) : Int)) = o at hm
  rcases o with _ | ⟨rev, cr, v⟩
  · exact absurd hm id
  obtain ⟨-, -, -, cs, hcs, hkv⟩ := hm
  obtain ⟨ch, hch⟩ : ∃ ch, cs[rev.sub.toNat]? = some ch := by
    unfold changeKv at hkv
    cases h : cs[rev.sub.toNat]? with
    | none => rw [h] at hkv; cases hkv
    | some ch => exact ⟨ch, rfl⟩
  have hmain : W64 (rev.main.toNat : Int) = rev.main := by word
  have hsub : W64 (rev.sub.toNat : Int) = rev.sub := by word
  have hjl : rev.main.toNat < L.length := (List.getElem?_eq_some_iff.1 hcs).1
  have hF : (⟨rev, ch.isDel, kv⟩ : KvEnt) ∈ logEnts L 0 L.length := by
    rw [mem_logEnts]
    refine ⟨rev.main.toNat, Nat.zero_le _, hjl, ?_⟩
    have hgd : L.getD rev.main.toNat [] = cs := by
      rw [List.getD_eq_getElem?_getD, hcs]; rfl
    rw [hgd, mem_entsOfRev]
    refine ⟨rev.sub.toNat, ch, kv, hch, ?_, ?_⟩
    · rw [hmain]; exact hkv
    · rw [hmain, hsub]
  refine ⟨⟨rev, ch.isDel, kv⟩, ?_, findKey_key hf⟩
  apply Classical.byContradiction
  intro hn
  have hdel := hcut.2.1 _ hF hn
  obtain ⟨hcL, r', t', hrb, h0, h1, -⟩ := id hdel
  have hca : c ≤ sint.Z (W64 ((L.length - 1 : Nat) : Int)) := by
    have : sint.Z (W64 ((L.length - 1 : Nat) : Int)) = ((L.length - 1 : Nat) : Int) := by word
    omega
  exact named_not_del L hb c (by omega) k _ hca rev cr v hg ch.isDel hdel

section items
variable [GooseExts]

/-- **`restore`'s `keyToLease` over a compacted image is the final state's item map**: the map
`restoreChunk` builds from the image `ents` of the log `L` compacted at `c` (`entsCutAt`) agrees,
key by key, with the lessor's item map of `L`'s final state. -/
theorem ktlApply_cut (L : Log) (c : Int) (ents : List KvEnt) (hb : LogB L) (hwf : LogWf L)
    (hcut : entsCutAt L c ents) :
    ∀ it : LeaseItem, (pendItems L []).lookup it = (ktlApply ∅ ents).lookup it.Key' := by
  intro it
  generalize hk : it.Key' = k
  have hL : (pendItems L []).lookup it = (findKey k (stateAfter L)).bind kvLease := by
    rw [← hk]; rfl
  rw [hL]
  have hA := ktlAgree_logEnts L (fun _ => hwf.1) k
  rw [ktlApply_lookup] at hA
  rw [ktlApply_lookup]
  simp only [GMap.lookup_empty] at hA ⊢
  have h0 : L.getD 0 [] = [] := by simp [List.getD_eq_getElem?_getD, hwf.1]
  have hsort := (logEnts_restoreOk L hb.1 hb.2 h0).1
  have hsubk := hcut.1.filter (fun e => decide (e.kv.key = k))
  have hsortk := hsort.filter (fun e => decide (e.kv.key = k))
  unfold ktlLast at hA ⊢
  cases hFl : ((logEnts L 0 L.length).filter fun e => decide (e.kv.key = k)).getLast? with
  | none =>
    have hF0 := List.getLast?_eq_none_iff.1 hFl
    rw [hF0] at hsubk
    rw [List.eq_nil_of_sublist_nil hsubk]
    rw [hFl] at hA
    exact hA.symm
  | some eL =>
    rw [hFl] at hA
    obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.1 hFl
    have heL : eL ∈ (logEnts L 0 L.length).filter fun e => decide (e.kv.key = k) := by
      rw [hys]; simp
    have heL' := List.mem_filter.1 heL
    by_cases hin : eL ∈ ents
    · rw [getLast?_sublist_of_mem (fun a => Rev.lt_irrefl a.rev) hsubk hsortk hFl
        (List.mem_filter.2 ⟨hin, heL'.2⟩)]
      exact hA.symm
    · have hE : (ents.filter fun e => decide (e.kv.key = k)) = [] := by
        apply List.eq_nil_iff_forall_not_mem.2
        intro e he
        have he' := List.mem_filter.1 he
        have heF := hsubk.subset he
        have heF' := List.mem_filter.1 heF
        rw [hys] at heF hsortk
        rcases List.mem_append.1 heF with hy | hy
        · have hlt := (List.pairwise_append.1 hsortk).2.2 e hy eL (by simp)
          exact hcut.2.2 e heF'.1 eL heL'.1
            (by rw [of_decide_eq_true heF'.2, of_decide_eq_true heL'.2]) hlt hin he'.1
        · simp only [List.mem_singleton] at hy
          subst hy
          exact hin he'.1
      rw [hE]
      cases hf : findKey k (stateAfter L) with
      | none => rfl
      | some kv =>
        obtain ⟨e, he, hek⟩ := cut_live_ent L c ents hb hwf hcut k kv hf
        have : e ∈ ents.filter fun e => decide (e.kv.key = k) :=
          List.mem_filter.2 ⟨he, decide_eq_true hek⟩
        rw [hE] at this
        cases this

/-- `ktlApply_cut` under `restore`'s hypotheses on its log (`restoreLogOk`'s `IdxWf L []`). -/
theorem ktlApply_cut_of_idxWf (L : Log) (c : Int) (ents : List KvEnt) (hne : L ≠ [])
    (hidx : IdxWf L []) (hcut : entsCutAt L c ents) :
    ∀ it : LeaseItem, (pendItems L []).lookup it = (ktlApply ∅ ents).lookup it.Key' := by
  have hwf' : LogWf' L := LogWf'.prefix hidx.1
  exact ktlApply_cut L c ents ⟨by have := hidx.2.1; omega, hidx.2.2.2⟩ ⟨hwf'.1 hne, hwf'.2⟩ hcut

end items

end mvcc
end EtcdGrove
end Perennial
