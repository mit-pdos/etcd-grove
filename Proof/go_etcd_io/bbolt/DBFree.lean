/-
The writer frees a page of its view (`node.free`: `db.freelist.Free(tx.meta.Txid(), page)`):
`Free` does not panic (`canFree`: the page's slots are neither free nor pending, it was
allocated before the writer's transaction, the freelist has room) and the database's facts
are kept (`dbOK_free`), its freelist lent to `Free` (`ownDB_free`).

The page goes pending for the writer's txid (newer than every view), with the transaction
that allocated it. A reader seeing one of its slots sees the same page there
(`viewsAgree`), so saw that allocation: MVCC holds.
-/
module

public import Proof.go_etcd_io.bbolt.DBAlloc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section free
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

/-- The pairs of the pending entries after `Free`: those before, and the run's (for `txid`, with
the transaction that allocated its first page). -/
theorem freePages_pairs (fl : FLState) (txid x : w64) (n : Nat)
    (hl : ∀ pd, fl.pending !! txid = some pd → pd.ids.length = pd.alloctx.length)
    (t : w64) (pd' : Pending) (p : w64 × w64)
    (ht : (fl.freePages txid x n).pending !! t = some pd') (hp : p ∈ pd'.pairs) :
    (∃ pd, fl.pending !! t = some pd ∧ p ∈ pd.pairs) ∨
    (t = txid ∧ p.1 ∈ runIds x n ∧ p.2 = (fl.allocs !! x).getD 0) := by
  unfold FLState.freePages at ht
  simp only at ht
  rw [GMap.lookup_insert_Some] at ht
  rcases ht with ⟨htt, rfl⟩ | ⟨_, ht⟩
  · subst htt
    have hlen : ((fl.pending !! txid).getD ⟨[], [], 0⟩).ids.length =
        ((fl.pending !! txid).getD ⟨[], [], 0⟩).alloctx.length := by
      cases hpd : fl.pending !! txid with
      | none => rfl
      | some pd => exact hl pd hpd
    unfold Pending.pairs at hp
    simp only at hp
    rw [List.zip_append hlen] at hp
    rcases List.mem_append.1 hp with h | h
    · left
      cases hpd : fl.pending !! txid with
      | none => rw [hpd] at h; simp at h
      | some pd => rw [hpd] at h; exact ⟨pd, rfl, h⟩
    · right
      have h' := List.of_mem_zip h
      exact ⟨rfl, h'.1, List.eq_of_mem_replicate h'.2⟩
  · exact Or.inl ⟨pd', ht, hp⟩

theorem freePages_allocs (fl : FLState) (txid x : w64) (n : Nat) (k a : w64)
    (h : (fl.freePages txid x n).allocs !! k = some a) : fl.allocs !! k = some a := by
  unfold FLState.freePages at h
  simp only at h
  exact ((GMap.lookup_delete_Some _ _ _ _).1 h).2

theorem w64_add_nat (a b : Nat) (h : a + b < 2 ^ 64) :
    W64 (a : Int) + W64 (b : Int) = W64 ((a + b : Nat) : Int) := by
  word

theorem w64_nat_inj (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : W64 (a : Int) = W64 (b : Int)) : a = b := by
  have h1 : uint.Z (W64 (a : Int)) = a := by word
  have h2 : uint.Z (W64 (b : Int)) = b := by word
  rw [h] at h1; omega

/-- The run's ids are the slots from `id` on. -/
theorem runIds_slot (id n : Nat) (hn : id + n < 2 ^ 64) (x : w64) (hx : x ∈ runIds (W64 id) n) :
    ∃ k < n, x = W64 ((id + k : Nat) : Int) := by
  unfold runIds at hx
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
  rw [List.mem_range] at hk
  exact ⟨k, hk, w64_add_nat id k (by omega)⟩

/-- A slot (below `2^64`) one of the run's ids names is in the run. -/
theorem slot_in_run (id n s : Nat) (hn : id + n < 2 ^ 64) (hs : s < 2 ^ 64)
    (hx : W64 (s : Int) ∈ runIds (W64 id) n) : id ≤ s ∧ s < id + n := by
  obtain ⟨k, hk, he⟩ := runIds_slot id n hn _ hx
  have := w64_nat_inj s (id + k) hs (by omega) he
  omega

/-- A list of distinct ids below `B` has at most `B` of them. -/
theorem nodup_length_le (l : List w64) (B : Nat) (hnd : l.Nodup) (hb : ∀ x ∈ l, uint.Z x < B) :
    l.length ≤ B := by
  have hnd' : (l.map (fun x => uint.nat x)).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    refine hnd.imp (fun {a b} hne e => hne ?_)
    word
  have hsub : l.map (fun x => uint.nat x) ⊆ List.range B := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    have := hb x hx
    rw [List.mem_range]; word
  have := hnd'.length_le_of_subset hsub
  simpa using this

/-- An MVCC view (older than `txid`) keeps the rule when `txid` frees a run whose allocation it
saw (for the slots it covers). -/
theorem mvccView_free (σ : DBState) (txid x : w64) (n : Nat)
    (hl : ∀ pd, σ.fl.pending !! txid = some pd → pd.ids.length = pd.alloctx.length)
    (T : w64) (P : GMap Nat (List w8)) (h : mvccView σ T P) (hlt : uint.Z T < uint.Z txid)
    (ha : ∀ s, coversSlot P s → W64 (s : Int) ∈ runIds x n →
      uint.Z ((σ.fl.allocs !! x).getD 0) ≤ uint.Z T) :
    mvccView { σ with fl := σ.fl.freePages txid x n } T P := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun id pg hid a hal => h1 id pg hid a (freePages_allocs _ _ _ _ _ _ hal),
    fun s hs => ⟨(h2 s hs).1, (h2 s hs).2.1, fun t pd' a ht hp => ?_⟩⟩
  rcases freePages_pairs σ.fl txid x n hl t pd' _ ht hp with ⟨pd, ht0, hp0⟩ | ⟨rfl, hr, hal⟩
  · exact (h2 s hs).2.2 t pd a ht0 hp0
  · simp only at hr hal
    subst hal
    exact ⟨ha s hs hr, hlt⟩

theorem w64_nat_z (a : Nat) (h : a < 2 ^ 64) : uint.Z (W64 (a : Int)) = a := by word

theorem txid_succ_z (a b : w64) (h : uint.Z a + 1 < 2 ^ 64) (hb : b = a + W64 1) :
    uint.Z b = uint.Z a + 1 := by
  subst hb; word

/-- An allocating transaction (`0` if unknown) bounded where known. -/
theorem allocs_getD_le (allocs : GMap w64 w64) (k T : w64)
    (h : ∀ a, allocs !! k = some a → uint.Z a ≤ uint.Z T) :
    uint.Z ((allocs !! k).getD 0) ≤ uint.Z T := by
  cases hal : allocs !! k with
  | none => show uint.Z (W64 0) ≤ _; word
  | some a => exact h a hal

/-- The writer frees a page of its view, for its txid: `Free` does not panic, and the database's
facts are kept. -/
theorem dbOK_free (σ : DBState) (v0 v1 : internal.common.Meta) (h : dbOK σ v0 v1)
    (hwf : σ.fl.WF) (w : Reader) (hw : σ.wr = some w) (txid : w64) (htx : txid = w.txid + W64 1)
    (htb : uint.Z w.txid + 1 < 2 ^ 64) (id : Nat) (pg : List w8) (hpg : w.pages !! id = some pg)
    (hnew : ∀ pd, σ.fl.pending !! txid = some pd →
      ∀ x ∈ runIds (W64 id) (1 + pageOverflow pg), x ∉ pd.ids) :
    σ.fl.canFree txid (W64 id) (1 + pageOverflow pg) ∧
    dbOK { σ with fl := σ.fl.freePages txid (W64 id) (1 + pageOverflow pg) } v0 v1 := by
  have h' := h
  obtain ⟨hps, hps2, hns, hsz, hdc, hm0, hm1, hv, hcur, hrd, hmv, hsl, hfl, hro, hrs, hwr⟩ := h'
  obtain ⟨cwf, cdisj, cin, calloc, cfree, cbelow, ⟨va1, va2⟩⟩ := hcur
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := cbelow
  have hwo := writer_readerOK σ v0 v1 h w hw
  have hwm := (hwr.2 w hw).2
  have hps16 : 16 ≤ σ.ps := by omega
  have hin := hwo.2.2 id pg hpg
  have hspan := span_of_pageAt σ.bs σ.ps id pg hps16 hin.1.symm
  have hns62 : σ.nslots < 2 ^ 62 :=
    Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (by omega))
      (Nat.lt_of_le_of_lt (nslots_mul_le σ) hsz.2)
  have hrun : id + (1 + pageOverflow pg) ≤ σ.nslots := by have := hin.2; omega
  have hidz := w64_nat_z id (by omega)
  have htxz := txid_succ_z w.txid txid htb htx
  have hmt := congrArg (fun x : w64 => uint.Z x) (b4 w hw).2
  have hl : ∀ t pd, σ.fl.pending !! t = some pd → pd.ids.length = pd.alloctx.length :=
    hwf.2.2.2.2
  have ha0 : uint.Z ((σ.fl.allocs !! W64 (id : Int)).getD 0) ≤ uint.Z w.txid :=
    allocs_getD_le _ _ _ (fun a hal => hwm.1 id pg hpg a hal)
  have hcov : ∀ k < 1 + pageOverflow pg, coversSlot w.pages (id + k) :=
    fun k hk => ⟨id, pg, hpg, by omega, by omega⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hidz]; have := (hwm.2 id (covers_self _ _ _ hpg)).1; omega
  · rw [hidz]; omega
  · -- the run is neither free nor pending (the writer's own pending pages are others)
    intro x hx hc
    obtain ⟨k, hk, rfl⟩ := runIds_slot id _ (by omega) x hx
    have hm := hwm.2 _ (hcov k hk)
    unfold FLState.cached FLState.allIds at hc
    rcases List.mem_append.1 hc with hf | hp
    · exact hm.2.1 hf
    · rw [pendingIds_eq, mem_flatIds] at hp
      obtain ⟨t, pd, ht, hxi⟩ := hp
      obtain ⟨a, ha⟩ := mem_pairs_of_mem_ids pd _ (hl t pd ht) hxi
      have hlt := (hm.2.2 t pd a ht ha).2
      rcases b3 t pd _ ht ha with hle | ⟨w', hw', rfl, -⟩
      · omega
      · obtain rfl := Option.some.inj (hw.symm.trans hw')
        exact hnew pd (by rw [htx]; exact ht) _ hx hxi
  · intro he; rw [he] at ha0; omega
  · -- room: the freelist's ids are distinct and below 2^62, and so is the run's length
    have hall : ∀ x ∈ σ.fl.allIds, uint.Z x < ((2 ^ 62 : Nat) : Int) := by
      intro x hx
      rcases List.mem_append.1 hx with hf | hp
      · have := b6 x hf; omega
      · rw [pendingIds_eq, mem_flatIds] at hp
        obtain ⟨t, pd, ht, hxi⟩ := hp
        obtain ⟨a, ha⟩ := mem_pairs_of_mem_ids pd _ (hl t pd ht) hxi
        have := b7 t pd (x, a) ht ha; simp only at this; omega
    have := nodup_length_le _ (2 ^ 62) hwf.1 hall
    omega
  · refine ⟨hps, hps2, hns, hsz, hdc, hm0, hm1, hv,
      ⟨cwf, cdisj, cin, fun id' pg' h a hal => calloc id' pg' h a (freePages_allocs _ _ _ _ _ _ hal),
        fun s hs => ⟨(cfree s hs).1, (cfree s hs).2.1, fun t pd' a ht hp => ?_⟩,
        ⟨b1, fun t pd' p ht hp hle => ?_, fun t pd' p ht hp => ?_, b4, b5, b6,
          fun t pd' p ht hp => ?_⟩, ⟨va1, va2⟩⟩,
      hrd, fun k r hk => ?_, hsl, hfl, hro, hrs, ⟨hwr.1, fun w' hw' => ?_⟩⟩
    · -- the current tree: the writer's pending pages are its own
      rcases freePages_pairs σ.fl _ _ _ (fun pd h => hl _ pd h) t pd' _ ht hp with
        ⟨pd, ht0, hp0⟩ | ⟨rfl, _, hal⟩
      · exact (cfree s hs).2.2 t pd a ht0 hp0
      · simp only at hal
        subst hal
        exact ⟨⟨w, hw, htx⟩, by omega⟩
    · rcases freePages_pairs σ.fl _ _ _ (fun pd h => hl _ pd h) t pd' _ ht hp with
        ⟨pd, ht0, hp0⟩ | ⟨rfl, _, _⟩
      · exact b2 t pd p ht0 hp0 hle
      · omega
    · rcases freePages_pairs σ.fl _ _ _ (fun pd h => hl _ pd h) t pd' _ ht hp with
        ⟨pd, ht0, hp0⟩ | ⟨rfl, _, hal⟩
      · exact b3 t pd p ht0 hp0
      · rw [hal]; exact Or.inr ⟨w, hw, htx, ha0⟩
    · rcases freePages_pairs σ.fl _ _ _ (fun pd h => hl _ pd h) t pd' _ ht hp with
        ⟨pd, ht0, hp0⟩ | ⟨_, hr, _⟩
      · exact b7 t pd p ht0 hp0
      · obtain ⟨k, hk, he⟩ := runIds_slot id _ (by omega) _ hr
        rw [he, w64_nat_z _ (by omega)]
        omega
    · -- a reader: older than the writer's txid, and it saw the run's allocation (the same page)
      refine mvccView_free σ txid (W64 (id : Int)) _ (fun pd h => hl _ pd h) r.txid r.pages
        (hmv k r hk) (by have := (va1 k r hk).1; omega) (fun s hs hr => ?_)
      obtain ⟨j, pj, hj, h1, h2⟩ := hs
      have hrin := (hrd k r hk).2.2 j pj hj
      have hjspan := span_of_pageAt σ.bs σ.ps j pj hps16 hrin.1.symm
      have hsr := slot_in_run id _ s (by omega) (by omega) hr
      have hij := (va2 w hw).2 k r hk id pg j pj s hpg hj hsr.1 (by omega) h1 h2
      subst hij
      exact allocs_getD_le _ _ _ (fun a hal => (hmv k r hk).1 id pj hj a hal)
    · -- the writer
      obtain rfl := Option.some.inj (hw.symm.trans hw')
      exact ⟨(hwr.2 w hw).1, mvccView_free σ txid (W64 (id : Int)) _ (fun pd h => hl _ pd h)
        w.txid w.pages hwm (by omega) (fun _ _ _ => ha0)⟩

open Iris.ProofMode in
/-- The writer frees a page of its view (`node.free`): the database's freelist lent to `Free`
(which does not panic), and the database with the page pending given back. -/
theorem ownDB_free (I : FLImpl (GF := GF)) (dbl : Loc) (γ : DBNames) (σ : DBState)
    (w : Reader) (hw : σ.wr = some w) (txid : w64) (htx : txid = w.txid + W64 1)
    (htb : uint.Z w.txid + 1 < 2 ^ 64) (id : Nat) (pg : List w8) (hpg : w.pages !! id = some pg)
    (hnew : ∀ pd, σ.fl.pending !! txid = some pd →
      ∀ x ∈ runIds (W64 id) (1 + pageOverflow pg), x ∉ pd.ids) :
    ownDB I dbl γ σ ⊢ ∃ (fls : Loc),
      ⌜σ.fl.canFree txid (W64 id) (1 + pageOverflow pg)⌝ ∗ ownFL I fls σ.fl ∗
      (ownFL I fls (σ.fl.freePages txid (W64 id) (1 + pageOverflow pg)) -∗
        ownDB I dbl γ { σ with fl := σ.fl.freePages txid (W64 id) (1 + pageOverflow pg) }) := by
  iintro Hdb
  isimp only [ownDB] at Hdb
  iNamed Hdb
  isimp only [ownFL] at Hfl
  icases Hfl with ⟨#Hh, Hsh, Ho⟩
  ihave Hsh := ownShared_wf _ _ _ $$ Hsh
  icases Hsh with ⟨Hsh, %hwf⟩
  obtain ⟨hcan, hok'⟩ := dbOK_free σ v0 v1 Hok hwf w hw txid htx htb id pg hpg hnew
  iexists fls
  isplitr
  · ipureintro; exact hcan
  isplitl [Hsh Ho]
  · simp only [ownFL]; iframe; iframe #
  iintro Hfl'
  simp only [ownDB]
  iexists dv, fls, v0, v1, dl
  isplitr
  · ipureintro; exact Hdv
  isplitr
  · ipureintro; exact hok'
  isplitr
  · ipureintro; exact Hdr
  iframe
  iframe #
  try (ipureintro; exact Hlog)

end free

end bbolt
end EtcdGrove
end Perennial
