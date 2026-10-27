/-
Proof of `Spec/.../mvcc/restoreIntoIndex.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.restoreIntoIndex
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__put
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__tombstone
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__restore
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__restoreTombstone
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__KeyIndex
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__Insert
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.BytesToRev
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.isTombstone
public import Spec.go_etcd_io.etcd.client.pkg.v3.verify.Verify
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Warn
public import Proof.ReceiptTactics

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section loopdefs
variable [GooseExts]

/-- The rebuild's cache holds pointers to key indexes of the tree, at their keys. -/
def mvcc.rstCacheOk (L : List mvcc.IdxEntry) (cache : GMap GoString Loc) : Prop :=
  ∀ k p, cache !! k = some p → ∃ ki, (p, k, ki) ∈ L

/-- The key indexes of the tree the rebuild made of the entries `pre`: each has a revision, the
last one (`modified`) an entry's. -/
def mvcc.rstLInv (L : List mvcc.IdxEntry) (pre : List mvcc.KvEnt) : Prop :=
  ∀ z ∈ L, z.1 ≠ null ∧ z.2.2.gens ≠ [] ∧ mvcc.kiIsEmpty z.2.2 = false ∧ ∃ e ∈ pre, z.2.2.modified = e.rev

/-- The next entry's main revision is at least the last one's (`verify.Verify`'s check). -/
theorem mvcc.restoreLastRev_le {ents : List mvcc.KvEnt} (hs : mvcc.RestoreEntsOk ents) (n : Nat)
    {e : mvcc.KvEnt} (he : ents[n]? = some e) :
    sint.Z (mvcc.restoreLastRev (ents.take n)) ≤ sint.Z e.rev.main := by
  have hpos := (hs.2 e (List.mem_of_getElem? he)).1
  cases n with
  | zero =>
    show sint.Z (W64 1) ≤ _
    have : sint.Z (W64 1) = 1 := by decide
    omega
  | succ m =>
    have hlt : m + 1 < ents.length := (List.getElem?_eq_some_iff.1 he).1
    have hl : (ents.take (m + 1)).getLast? = some ents[m] := by
      rw [List.getLast?_eq_getElem?]
      simp only [List.length_take, Nat.min_eq_left (by omega : m + 1 ≤ ents.length),
        Nat.add_sub_cancel, List.getElem?_take]
      simp [show m < m + 1 by omega]
    simp only [mvcc.restoreLastRev, hl]
    have he2 : ents[m + 1] = e := (List.getElem?_eq_some_iff.1 he).2
    have hrl := List.pairwise_iff_getElem.1 hs.1 m (m + 1) (by omega) hlt (by omega)
    rw [he2] at hrl
    unfold mvcc.Rev.lt at hrl
    rcases hrl with h | ⟨h, -⟩
    · omega
    · rw [h]; exact Int.le_refl _

theorem mvcc.take_succ_of_getElem? {ents : List mvcc.KvEnt} {n : Nat} {e : mvcc.KvEnt}
    (he : ents[n]? = some e) : ents.take (n + 1) = ents.take n ++ [e] := by
  rw [List.take_add_one, he]; rfl

theorem mvcc.restoreLastRev_take_succ {ents : List mvcc.KvEnt} {n : Nat} {e : mvcc.KvEnt}
    (he : ents[n]? = some e) : mvcc.restoreLastRev (ents.take (n + 1)) = e.rev.main := by
  rw [mvcc.take_succ_of_getElem? he]
  simp [mvcc.restoreLastRev]

theorem mvcc.idxRestore_take_succ {ents : List mvcc.KvEnt} {n : Nat} {e : mvcc.KvEnt}
    (he : ents[n]? = some e) :
    mvcc.idxRestore (ents.take (n + 1)) = mvcc.idxRestoreEnt (mvcc.idxRestore (ents.take n)) e := by
  rw [mvcc.take_succ_of_getElem? he]
  unfold mvcc.idxRestore
  rw [List.foldl_append]; rfl

/-- In sorted entries, an entry is the one `find?` finds for its key. -/
theorem mvcc.find?_of_mem_sorted : ∀ {L : List mvcc.IdxEntry}, L.Pairwise mvcc.entryLess →
    ∀ {z : mvcc.IdxEntry}, z ∈ L → L.find? (fun w => decide (w.2.1 = z.2.1)) = some z
  | [], _, _, hz => by cases hz
  | w :: ws, hs, z, hz => by
    rw [List.find?_cons]
    rcases List.mem_cons.1 hz with rfl | hz'
    · simp
    · have hlt : mvcc.entryLess w z := List.rel_of_pairwise_cons hs hz'
      have hne : w.2.1 ≠ z.2.1 := fun h => by
        unfold mvcc.entryLess at hlt; rw [h] at hlt; exact go.goStringLt_irrefl _ hlt
      simp only [hne, _root_.decide_false]
      exact mvcc.find?_of_mem_sorted (List.Pairwise.of_cons hs) hz'

theorem mvcc.rstCacheOk_set {L : List mvcc.IdxEntry} {c : GMap GoString Loc} (h : mvcc.rstCacheOk L c)
    {i : Nat} {z : mvcc.IdxEntry} (hz : L[i]? = some z) (ki : mvcc.KeyIndex) :
    mvcc.rstCacheOk (L.set i (z.1, z.2.1, ki)) c := by
  intro k p hk
  obtain ⟨x, hx⟩ := h k p hk
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
  by_cases hij : j = i
  · subst hij
    rw [hz] at hj
    cases hj
    exact ⟨ki, List.mem_iff_getElem?.2 ⟨j, by
      rw [List.getElem?_set_self (List.getElem?_eq_some_iff.1 hz).1]⟩⟩
  · exact ⟨x, List.mem_iff_getElem?.2 ⟨j, by rw [List.getElem?_set_ne (Ne.symm hij)]; exact hj⟩⟩

theorem mvcc.rstCacheOk_btInsert {L : List mvcc.IdxEntry} {c : GMap GoString Loc}
    (h : mvcc.rstCacheOk L c) (p : Loc) (k : GoString) (m : mvcc.KeyIndex)
    (hnew : ∀ w ∈ L, mvcc.entryLess w (p, k, m) ∨ mvcc.entryLess (p, k, m) w) :
    mvcc.rstCacheOk (btInsert mvcc.entryLess (p, k, m) L) (<[k := p]> c) := by
  have hperm := mvcc.btInsert_perm_of_new (p, k, m) L hnew
  intro k' p' hk
  by_cases hkk : k' = k
  · subst hkk
    rw [GMap.lookup_insert] at hk
    cases hk
    exact ⟨m, hperm.mem_iff.2 List.mem_cons_self⟩
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm hkk)] at hk
    obtain ⟨x, hx⟩ := h k' p' hk
    exact ⟨x, hperm.mem_iff.2 (List.mem_cons_of_mem _ hx)⟩

/-- A key index the rebuild made has its last change at an earlier entry's revision. -/
theorem mvcc.rst_modified_lt {ents : List mvcc.KvEnt} (hs : mvcc.RestoreEntsOk ents) {n : Nat}
    {e : mvcc.KvEnt} (he : ents[n]? = some e) {ki : mvcc.KeyIndex}
    (hm : ∃ e' ∈ ents.take n, ki.modified = e'.rev) : mvcc.Rev.lt ki.modified e.rev := by
  obtain ⟨e', he', hmod⟩ := hm
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 he'
  have hjn : j < n := by
    have := (List.getElem?_eq_some_iff.1 hj).1; simp at this; omega
  rw [List.getElem?_take, if_pos hjn] at hj
  have hnl : n < ents.length := (List.getElem?_eq_some_iff.1 he).1
  have h := List.pairwise_iff_getElem.1 hs.1 j n (by omega) hnl hjn
  rw [(List.getElem?_eq_some_iff.1 hj).2, (List.getElem?_eq_some_iff.1 he).2] at h
  rw [hmod]; exact h

theorem mvcc.rstLInv_mono {L : List mvcc.IdxEntry} {pre : List mvcc.KvEnt} (h : mvcc.rstLInv L pre)
    (e : mvcc.KvEnt) : mvcc.rstLInv L (pre ++ [e]) := by
  intro z hz
  obtain ⟨h1, h2, h3, e', he', hm⟩ := h z hz
  exact ⟨h1, h2, h3, e', List.mem_append_left _ he', hm⟩

theorem mvcc.rstLInv_set {L : List mvcc.IdxEntry} {pre : List mvcc.KvEnt} (h : mvcc.rstLInv L pre)
    {i : Nat} {z : mvcc.IdxEntry} (hz : L[i]? = some z) (e : mvcc.KvEnt) (ki : mvcc.KeyIndex)
    (hg : ki.gens ≠ []) (he : mvcc.kiIsEmpty ki = false)
    (hm : ki.modified = e.rev ∨ ki.modified = z.2.2.modified) :
    mvcc.rstLInv (L.set i (z.1, z.2.1, ki)) (pre ++ [e]) := by
  intro x hx
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
  have hzL : z ∈ L := List.mem_of_getElem? hz
  by_cases hij : j = i
  · subst hij
    rw [List.getElem?_set_self (List.getElem?_eq_some_iff.1 hz).1] at hj
    cases hj
    obtain ⟨h1, -, -, e', he', hm'⟩ := h z hzL
    refine ⟨h1, hg, he, ?_⟩
    rcases hm with hm | hm
    · exact ⟨e, List.mem_append_right _ List.mem_cons_self, hm⟩
    · exact ⟨e', List.mem_append_left _ he', hm.trans hm'⟩
  · rw [List.getElem?_set_ne (Ne.symm hij)] at hj
    exact mvcc.rstLInv_mono h e x (List.mem_of_getElem? hj)

theorem mvcc.rstLInv_btInsert {L : List mvcc.IdxEntry} {pre : List mvcc.KvEnt}
    (h : mvcc.rstLInv L pre) (e : mvcc.KvEnt) (p : Loc) (k : GoString) (m : mvcc.KeyIndex)
    (hp : p ≠ null) (hg : m.gens ≠ []) (he : mvcc.kiIsEmpty m = false) (hm : m.modified = e.rev)
    (hnew : ∀ w ∈ L, mvcc.entryLess w (p, k, m) ∨ mvcc.entryLess (p, k, m) w) :
    mvcc.rstLInv (btInsert mvcc.entryLess (p, k, m) L) (pre ++ [e]) := by
  have hperm := mvcc.btInsert_perm_of_new (p, k, m) L hnew
  intro x hx
  rcases List.mem_cons.1 (hperm.mem_iff.1 hx) with rfl | hx'
  · exact ⟨hp, hg, he, e, List.mem_append_right _ List.mem_cons_self, hm⟩
  · exact mvcc.rstLInv_mono h e x hx'

theorem mvcc.itemsOfEntries_set_same (L : List mvcc.IdxEntry) {i : Nat} {z : mvcc.IdxEntry}
    (hz : L[i]? = some z) (ki : mvcc.KeyIndex) :
    mvcc.itemsOfEntries (L.set i (z.1, z.2.1, ki)) = mvcc.itemsOfEntries L := by
  unfold mvcc.itemsOfEntries
  rw [List.map_set]
  have hlt : i < L.length := (List.getElem?_eq_some_iff.1 hz).1
  have hget : (L.map fun z => (z.1, z.2.1))[i]'(by simpa using hlt) = (z.1, z.2.1) := by
    rw [List.getElem_map, (List.getElem?_eq_some_iff.1 hz).2]
  simp only
  rw [← hget, List.set_getElem_self]

end loopdefs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.restoreIntoIndex.wp_proof
    (hKIput : mvcc.keyIndex.put.spec (GF := GF) (hG := hG))
    (hKItomb : mvcc.keyIndex.tombstone.spec (GF := GF) (hG := hG))
    (hKIrestore : mvcc.keyIndex.restore.spec (GF := GF) (hG := hG))
    (hKIrestoreT : mvcc.keyIndex.restoreTombstone.spec (GF := GF) (hG := hG))
    (hKeyIndex : mvcc.treeIndex.KeyIndex.spec (GF := GF) (hG := hG))
    (hInsert : mvcc.treeIndex.Insert.spec (GF := GF) (hG := hG))
    (hB2R : mvcc.BytesToRev.spec (GF := GF) (hG := hG))
    (hTomb : mvcc.isTombstone.spec (GF := GF) (hG := hG))
    (hVerify : verify.Verify.spec (GF := GF) (hG := hG))
    (hZE : zap.Error.spec (GF := GF) (hG := hG))
    (hWarn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    mvcc.restoreIntoIndex.spec (GF := GF) (hG := hG) := by
  intro lg ti ents Rd Tok e0
  wp_start as ⟨%Hlg, Hix, #Hrc, Htok, %Hok, #Herr⟩
  ihave Hinit : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #HrCK, -⟩
  wp_auto
  wp_apply chan.wp_make2 (V := revKeyValue) (W64 10000) as %rkvc %γc ⟨#Hch, %Hcap, Hoc⟩
  · ipureintro; decide
  ihave Hoc : ownChan γc revKeyValue (.Buffered []) $$ Hoc
  imod start_spsc rkvc (mvcc.rkvProt Rd ents) (fun sent => iprop(⌜sent.length = ents.length⌝)) γc
    $$ Hch [Hoc] with ⟨%γ, #Hsp, Hprod, Hcons⟩
  · iright; iexact Hoc
  wp_apply chan.wp_make2 (V := w64) (W64 1) as %revc %γrc ⟨#Hrch, %Hrcap, Hroc⟩
  · ipureintro; decide
  ihave Hroc : ownChan γrc w64 (.Buffered []) $$ Hroc
  imod start_spsc revc (mvcc.revProt ti Tok ents) (fun _ => iprop(False)) γrc
    $$ Hrch [Hroc] with ⟨%γr, #Hrsp, Hrprod, Hrcons⟩
  · iright; iexact Hroc
  ipersist rkvc
  ipersist revc
  ipersist idx
  ipersist lg
  wp_apply wp_fork $$ [Hix Htok Hcons Hrprod]
  · -- the goroutine: rebuild the index
    wp_auto
    wp_apply wp_with_defer
    iintro %defer Hdefer
    (try wp_auto)
    wp_apply (wp_map_make2 (K := GoString) (V := Loc) (W64 10000) go.string
      (go.GoType.PointerType keyIndex.ty)) as %cm Hcm
    (try wp_auto)
    imod (receipt_zero (GF := GF)) with Hr0
    ihave IH : iprop(∃ (n : Nat) (recv : List revKeyValue) (L : List mvcc.IdxEntry)
        (cache : GMap GoString Loc) (cmv : Loc) (rk : revKeyValue),
        "Hcons" ∷ spscConsumer γ recv ∗ "Hix" ∷ mvcc.ownIdxPriv ti L ∗
        "kiCache" ∷ kiCache_ptr ↦ cmv ∗ "Hcm" ∷ cmv ↦$ cache ∗
        "currentRev" ∷ currentRev_ptr ↦ mvcc.restoreLastRev (ents.take n) ∗
        "rkv" ∷ rkv_ptr ↦ rk ∗ "Htok" ∷ Tok ∗ "Hrcpt" ∷ ⧗ n ∗
        "%Hn" ∷ ⌜recv.length = n ∧ n ≤ ents.length ∧
          mvcc.idxOfEntries L = mvcc.idxRestore (ents.take n) ∧
          mvcc.rstLInv L (ents.take n) ∧ mvcc.rstCacheOk L cache⌝)
        $$ [Hcons Hix kiCache Hcm currentRev rkv Htok Hr0]
    · iexists 0, [], [], ∅, cm, zero_val revKeyValue
      simp only [named, List.take_zero]
      rw [show mvcc.restoreLastRev [] = W64 1 from rfl]
      iframe Hcons Hix kiCache Hcm rkv Htok currentRev Hr0
      ipureintro
      refine ⟨rfl, Nat.zero_le _, rfl, ?_, ?_⟩
      · intro z hz; simp at hz
      · intro k p h; rw [GMap.lookup_empty] at h; cases h
    wp_for IH
    try simp only [eq_self_iff_true, _root_.decide_true, ↓reduceIte]
    (try wp_auto)
    wp_apply (wp_spsc_receive γ rkvc (mvcc.rkvProt Rd ents)
      (fun sent => iprop(⌜sent.length = ents.length⌝)) recv) $$ [$Hsp $Hcons] as %rkv1 %okr Hr
    cases okr
    · -- the channel closed: every entry received
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hr with ⟨%Hlen, %Hz⟩
      obtain ⟨Hrl, -, Hidx, -, -⟩ := Hn
      have hn : n = ents.length := by omega
      subst hn
      rw [List.take_length] at Hidx
      rw [List.take_length]
      (try wp_auto)
      wp_for_post
      -- the deferred `revc <- currentRev`
      wp_apply (wp_spsc_send γr revc (mvcc.revProt ti Tok ents) (fun _ => iprop(False)) []
        (mvcc.restoreLastRev ents)) $$ [$Hrsp $Hrprod Htok Hrcpt Hix] as -
      · iunfold mvcc.revProt
        iframe Htok Hrcpt
        isplitl []
        · ipureintro; exact ⟨rfl, rfl⟩
        iexists L
        iframe Hix
        ipureintro; exact Hidx
      itrivial
    · simp only [↓reduceIte]
      icases Hr with ⟨Hp, Hcons⟩
      iunfold mvcc.rkvProt at Hp
      icases Hp with ⟨%e, %He, Hrkv⟩
      obtain ⟨Hrl, Hnle, Hidx, HLinv, Hcache⟩ := Hn
      have He' : ents[n]? = some e := by rw [← Hrl]; simpa using He.1
      iunfold mvcc.rkvIs at Hrkv
      icases Hrkv with ⟨#HRdk, %Hkstr, %ks, %vs, %uf, %st, %sc, Hmsg, #Hks, #Hvs⟩
      (try wp_auto)
      rw [Hkstr]
      wp_apply (wp_map_lookup2 go.string (go.GoType.PointerType keyIndex.ty) cmv cache e.kv.key)
        $$ [$Hcm] as Hcm
      (try wp_auto)
      -- the purge of a full cache on a miss: the cache only shrinks
      wp_bind (If _ _ _)
      iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ kiCache_ptr ↦ cmv ∗
          ∃ cache' : GMap GoString Loc, cmv ↦$ cache' ∗ ⌜(∀ k p, cache' !! k = some p → cache !! k = some p) ∧
            ((cache !! e.kv.key).isSome → cache' = cache)⌝))) $$ [Hcm kiCache]
      · cases hc : cache !! e.kv.key with
        | some p =>
          simp only [Option.isSome_some, _root_.decide_true]
          wp_auto
          isplitr
          · ipureintro; rfl
          iframe kiCache
          iexists cache
          iframe Hcm
          ipureintro; exact ⟨fun _ _ h => h, fun _ => rfl⟩
        | none =>
          simp only [Option.isSome_none, Bool.false_eq_true, _root_.decide_false]
          wp_auto
          wp_apply (wp_map_len cmv cache (DFrac.own 1)) $$ [$Hcm] as Hcm
          (try wp_auto)
          wp_if_destruct
          · -- full: delete keys until ten are gone (or none is left)
            (try wp_auto)
            wp_func_lits
            wp_bind (App (App (Val (map.forRange _ _)) _) _)
            iapply (wp_map_for_range_mut_keys (fun (_ : List GoString) (j : Nat) m' =>
                iprop(∃ kv : GoString, "i" ∷ i_ptr ↦ W64 (10 - (j : Int)) ∗ "k" ∷ k_ptr ↦ kv ∗
                  "kiCache" ∷ kiCache_ptr ↦ cmv ∗
                  "%Hj" ∷ ⌜j < 10 ∧ ∀ k p, m' !! k = some p → cache !! k = some p⌝))) $$ Hcm
            iintro %keys %Hkeys
            isplitl [i k kiCache]
            · iexists _
              simp only [named]
              rw [show (W64 (10 - ((0 : Nat) : Int)) : w64) = W64 10 from rfl]
              iframe i k kiCache
              ipureintro; exact ⟨by decide, fun _ _ h => h⟩
            isplitr
            · imodintro
              iintro %j %key %pv %m' %Hjm HP Hm
              iNamed HP
              (try wp_auto)
              wp_apply (wp_mapDelete cmv m' key go.string (go.GoType.PointerType keyIndex.ty)) $$ [$Hm]
                as Hm
              (try wp_auto)
              have hsub : ∀ k p, (GMap.delete key m') !! k = some p → cache !! k = some p := by
                intro k p h
                by_cases hk : k = key
                · subst hk; rw [GMap.lookup_delete] at h; cases h
                · rw [GMap.lookup_delete_ne _ (Ne.symm hk)] at h; exact Hj.2 k p h
              wp_if_destruct
              · -- the tenth: break
                unfold forMapPostcondition
                iright; iright; ileft
                isplitr
                · ipureintro; rfl
                isplitr
                · itrivial
                iframe kiCache
                iexists (GMap.delete key m')
                iframe Hm
                ipureintro; exact ⟨hsub, fun h => by simp at h⟩
              · unfold forMapPostcondition
                iright; ileft
                isplitr
                · ipureintro; rfl
                iexists (GMap.delete key m')
                iframe Hm
                isplitl [i k kiCache]
                · iexists key
                  simp only [named]
                  rw [show (W64 (10 - (j : Int)) : w64) - W64 1 = W64 (10 - ((j + 1 : Nat) : Int)) by
                    push_cast; word]
                  iframe i k kiCache
                  ipureintro
                  refine ⟨?_, fun k p h => ?_⟩
                  · have : (W64 (10 - (j : Int)) : w64) - W64 1 ≠ W64 0 := Hif
                    have hj := Hj.1
                    rcases Nat.lt_or_ge (j + 1) 10 with h | h
                    · exact h
                    · have hj9 : j = 9 := by omega
                      subst hj9; exact absurd (by decide) this
                  · by_cases hk : k = key
                    · subst hk; rw [GMap.lookup_delete] at h; cases h
                    · rw [GMap.lookup_delete_ne _ (Ne.symm hk)] at h; exact Hj.2 k p h
                ipureintro
                intro k hk
                rw [GMap.lookup_delete_ne _ (Ne.symm hk)]
            · iintro %m' HP Hm
              iNamed HP
              isplitr
              · ipureintro; rfl
              iframe kiCache
              iexists m'
              iframe Hm
              ipureintro; exact ⟨Hj.2, fun h => by simp at h⟩
          · -- not full: no purge
            isplitr
            · itrivial
            iframe kiCache
            iexists cache
            iframe Hcm
            ipureintro; exact ⟨fun _ _ h => h, fun h => by simp at h⟩
      iintro %v1 ⟨%Hv1, kiCache, %cache', Hcm, %Hc'⟩
      subst Hv1
      have Hcache' : mvcc.rstCacheOk L cache' := fun k p h => Hcache k p (Hc'.1 k p h)
      iStructNamedPrefix Hmsg "M"
      ipersist MKey
      ipersist MCreateRevision
      ipersist MVersion
      (try wp_auto)
      -- on a miss, the key's index in the tree, if any; the rest goes on from one state
      wp_bind (If _ _ _)
      iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ ∃ (p : Loc) (okb : Bool)
          (cache2 : GMap GoString Loc), ki_ptr ↦ p ∗ ok_ptr ↦ okb ∗ kiCache_ptr ↦ cmv ∗
          rkv_ptr ↦ rkv1 ∗
          cmv ↦$ cache2 ∗ mvcc.ownIdxPriv ti L ∗ ⌜mvcc.rstCacheOk L cache2⌝ ∗
          (if okb then iprop(⌜∃ ki, (p, e.kv.key, ki) ∈ L⌝)
           else iprop(⌜(∀ z ∈ L, z.2.1 ≠ e.kv.key) ∧ p ≠ null⌝ ∗ mvcc.kiKey p e.kv.key ∗
             mvcc.ownKi p slice.nil mvcc.KeyIndex.fresh (DFrac.own 1)))))) $$ [ki ok kiCache Hcm Hix rkv]
      · cases hc : cache !! e.kv.key with
        | some p =>
          simp only [Option.isSome_some, _root_.decide_true, Option.getD_some]
          wp_auto
          isplitr
          · itrivial
          iexists p, true, cache'
          iframe ki ok kiCache Hcm Hix rkv
          simp only [↓reduceIte]
          isplitl []
          · ipureintro; exact Hcache'
          ipureintro
          obtain ⟨ki, hki⟩ := Hcache e.kv.key p hc
          exact ⟨ki, hki⟩
        | none =>
          simp only [Option.isSome_none, Bool.false_eq_true, _root_.decide_false, Option.getD_none]
          wp_auto
          ihave %Hnn0 := typedPointsto_not_null _ _ _ $$ «$r0»
          iStructNamedPrefix «$r0» "N"
          ipersist Nkey
          ihave #Hkk : mvcc.kiKey (GF := GF) «$r0_ptr» e.kv.key $$ []
          · iunfold mvcc.kiKey
            iexists ks
            iframe Nkey Hks
          wp_apply (hKeyIndex ti L «$r0_ptr» e.kv.key) $$ [$Hix $Hkk] as %p' ⟨Hix, %Hp'⟩
          (try wp_auto)
          cases hf : L.find? (fun z => decide (z.2.1 = e.kv.key)) with
          | some z =>
            -- the tree has the key: cache its index
            rw [hf, Option.map_some, Option.getD_some] at Hp'
            subst Hp'
            have hz := List.mem_of_find?_eq_some hf
            have hzk : z.2.1 = e.kv.key := by simpa using List.find?_some hf
            have hzn : z.1 ≠ null := (HLinv z hz).1
            simp only [hzn, _root_.decide_false, Bool.not_false]
            wp_auto
            rw [Hkstr]
            wp_apply (wp_mapInsert go.string cmv cache' e.kv.key z.1) $$ [$Hcm] as Hcm
            (try wp_auto)
            isplitr
            · first | itrivial | (ipureintro; rfl)
            iexists z.1, true, <[e.kv.key := z.1]> cache'
            iframe ki ok kiCache Hcm Hix rkv
            simp only [↓reduceIte]
            isplitl []
            · ipureintro
              intro k p hk
              by_cases hkk : k = e.kv.key
              · subst hkk
                rw [GMap.lookup_insert] at hk
                cases hk
                exact ⟨z.2.2, by rw [← hzk]; exact hz⟩
              · rw [GMap.lookup_insert_ne _ _ (Ne.symm hkk)] at hk
                exact Hcache' k p hk
            ipureintro
            exact ⟨z.2.2, by rw [← hzk]; exact hz⟩
          | none =>
            -- a new key: the fresh key index
            rw [hf, Option.map_none, Option.getD_none] at Hp'
            subst Hp'
            simp only [_root_.decide_true, Bool.not_true]
            (try wp_auto)
            isplitr
            · first | itrivial | (ipureintro; rfl)
            iexists «$r0_ptr», false, cache'
            iframe ki ok kiCache Hcm Hix rkv
            simp only [Bool.false_eq_true, ↓reduceIte]
            isplitl []
            · ipureintro; exact Hcache'
            iframe Hkk
            isplitl []
            · ipureintro
              refine ⟨fun z hz hzk => ?_, Hnn0⟩
              have := List.find?_eq_none.1 hf z hz
              simp [hzk] at this
            iunfold mvcc.ownKi
            iframe Ngenerations
            isplitl [Nmodified]
            · rw [show mvcc.revVal mvcc.KeyIndex.fresh.modified = (zeroValDef : Revision) from rfl]
              iexact Nmodified
            iunfold mvcc.ownGens
            iexists []
            isplitl []
            · iapply ownSlice_nil
            isplitl []
            · iapply ownSliceCap_nil
            simp only [mvcc.KeyIndex.fresh, mvcc.ownGensL]
            itrivial
      iintro %v2 ⟨%Hv2, %p, %okb, %cache2, ki, ok, kiCache, rkv, Hcm, Hix, %Hcache2, Hkst⟩
      subst Hv2
      have Hem : e ∈ ents := List.mem_of_getElem? He'
      have Hpos := Hok.2 e Hem
      wp_auto
      -- `rev := BytesToRev(rkv.key)`
      have hrb : mvcc.revBytes e.rev e.tomb =
          mvcc.revBytes e.rev false ++ (if e.tomb then [mvcc.markTomb] else []) := by
        cases e.tomb
        · simp
        · simp [mvcc.revBytes_true]
      iunfold mvcc.rdCap at Hrc
      icases Hrc $$ %rkv1.key' %(mvcc.revBytes e.rev e.tomb) HRdk Htok with ⟨%dqk, Hkb, Hkback⟩
      rw [hrb]
      wp_apply (hB2R rkv1.key' e.rev (if e.tomb then [mvcc.markTomb] else []) dqk
        (by cases e.tomb <;> simp) (by omega) (by omega)) $$ [$Hkb] as Hkb
      rw [← hrb]
      ihave Htok := Hkback $$ Hkb
      (try wp_auto)
      -- `verify.Verify(...)`: revisions arrive in increasing order
      wp_apply (hVerify _ _ iprop(rev_ptr ↦ mvcc.revVal e.rev ∗
          currentRev_ptr ↦ mvcc.restoreLastRev (ents.take n))) $$ [rev currentRev]
        as ⟨rev, currentRev⟩
      · iframe rev currentRev
        iintro ⟨rev, currentRev⟩
        wp_auto
        wp_apply (wp_map_make1 (K := GoString) (V := GoInterface) go.string go.any) as %mm Hmm
        (try wp_auto)
        wp_apply (wp_mapInsert go.string mm _ _ _) $$ [$Hmm] as Hmm
        (try wp_auto)
        wp_apply (wp_mapInsert go.string mm _ _ _) $$ [$Hmm] as Hmm
        (try wp_auto)
        rw [decide_eq_true (mvcc.restoreLastRev_le Hok n He')]
        iexists _
        iframe rev currentRev
        ipureintro; rfl
      (try wp_auto)
      have Hrl1 : (recv ++ [rkv1]).length = n + 1 := by simp [Hrl]
      have Hlast := mvcc.restoreLastRev_take_succ He'
      have Hstep := mvcc.idxRestore_take_succ He'
      have Hnlt : n < ents.length := (List.getElem?_eq_some_iff.1 He').1
      iunfold mvcc.ownIdxPriv at Hix
      icases Hix with ⟨%t, %lg', #Htree, #Hlg', %Hlgnn, Hmu, Htr⟩
      icases mvcc.ownTree_sorted t L 1 $$ Htr with ⟨Htr, %Hsorted⟩
      have Hsorted' := (mvcc.itemsOfEntries_sorted_iff L).1 Hsorted
      cases okb
      · -- a new key
        simp only [Bool.false_eq_true, ↓reduceIte]
        -- the receipt of the entry, from the next resolution (`isTombstone`)
        wp_take_receipt as Hr1
        ihave Hrcpt : iprop(⧗ (n + 1)) $$ [Hrcpt Hr1]
        · iapply (receipt_add _ 1).2; iframe
        -- `isTombstone(rkv.key)`
        icases Hrc $$ %rkv1.key' %(mvcc.revBytes e.rev e.tomb) HRdk Htok with ⟨%dqk2, Hkb, Hkback⟩
        wp_apply (hTomb rkv1.key' (mvcc.revBytes e.rev e.tomb) dqk2) $$ [$Hkb] as Hkb
        ihave Htok := Hkback $$ Hkb
        rw [mvcc.isTomb_revBytes_self]
        icases Hkst with ⟨%Hnp, #Hpk, Hki⟩
        obtain ⟨Hnew, Hpn⟩ := Hnp
        cases ht : e.tomb
        · -- `ki.restore(lg, Revision{Main: rkv.kv.CreateRevision}, rev, rkv.kv.Version)`
          try simp only [Bool.false_eq_true, ↓reduceIte]
          (try wp_auto)
          rw [show ({ Main' := e.kv.createRev, Sub' := 0 } : Revision) =
            mvcc.revVal ⟨e.kv.createRev, W64 0⟩ from rfl]
          wp_apply (hKIrestore p slice.nil mvcc.KeyIndex.fresh lg ⟨e.kv.createRev, W64 0⟩ e.rev
            e.kv.version) $$ [$Hki] as %r Hr
          · ipureintro; exact Hlg
          try simp only [show mvcc.KeyIndex.fresh.gens = [] from rfl, ↓reduceIte]
          icases Hr with ⟨%Hr, %gs', Hki⟩
          subst Hr
          (try wp_auto)
          -- `idx.Insert(ki)` and `kiCache[rkv.kstr] = ki`
          ihave Hix : mvcc.ownIdxPriv (GF := GF) ti L $$ [Hmu Htr]
          · iunfold mvcc.ownIdxPriv
            iexists t, lg'
            iframe Hmu Htr
            iframe #
            ipureintro; exact Hlgnn
          wp_apply (hInsert ti L p e.kv.key gs' (mvcc.kiRestore e.kv.createRev e.rev e.kv.version)) $$ [$Hix $Hpk $Hki] as Hix
          · ipureintro; exact ⟨Hpn, Hnew⟩
          (try wp_auto)
          try rw [Hkstr]
          wp_apply (wp_mapInsert go.string cmv cache2 e.kv.key p) $$ [$Hcm] as Hcm
          (try wp_auto)
          wp_for_post
          iframe Hrprod Hdefer
          iexists n + 1, recv ++ [rkv1], btInsert mvcc.entryLess (p, e.kv.key, mvcc.kiRestore e.kv.createRev e.rev e.kv.version) L,
            <[e.kv.key := p]> cache2, cmv, rkv1
          simp only [named]
          rw [Hlast]
          iframe Hcons kiCache Hcm currentRev rkv Htok Hrcpt Hix
          ipureintro
          have hnew' : ∀ w ∈ L, mvcc.entryLess w (p, e.kv.key, mvcc.kiRestore e.kv.createRev e.rev e.kv.version) ∨
              mvcc.entryLess (p, e.kv.key, mvcc.kiRestore e.kv.createRev e.rev e.kv.version) w := by
            intro w hw
            have hne : w.2.1 ≠ e.kv.key := Hnew w hw
            by_cases h1 : go.GoStringLt w.2.1 e.kv.key
            · exact Or.inl h1
            · by_cases h2 : go.GoStringLt e.kv.key w.2.1
              · exact Or.inr h2
              · exact absurd (go.goStringLt_eq_of_not_lt h1 h2) hne
          have hnone : mvcc.idxGet (mvcc.idxOfEntries L) e.kv.key = none := by
            rw [mvcc.idxGet_entries L Hsorted]
            have : L.find? (fun z => decide (z.2.1 = e.kv.key)) = none := by
              rw [List.find?_eq_none]; intro z hz; simpa using Hnew z hz
            rw [this]; rfl
          refine ⟨Hrl1, Hnlt, ?_, ?_, ?_⟩
          · rw [Hstep, ← Hidx, mvcc.idxOfEntries_btInsert]
            unfold mvcc.idxRestoreEnt
            rw [hnone, ht]
            rfl
          · rw [mvcc.take_succ_of_getElem? He']
            exact mvcc.rstLInv_btInsert HLinv e p e.kv.key _ Hpn (by simp [mvcc.kiRestore,
              mvcc.kiRestoreTombstone]) (by simp [mvcc.kiIsEmpty, mvcc.kiRestore,
              mvcc.kiRestoreTombstone]) rfl hnew'
          · exact mvcc.rstCacheOk_btInsert Hcache2 p e.kv.key _ hnew'
        · -- `ki.restoreTombstone(lg, rev.Main, rev.Sub)`
          try simp only [↓reduceIte]
          (try wp_auto)
          wp_apply (hKIrestoreT p slice.nil mvcc.KeyIndex.fresh lg e.rev.main e.rev.sub) $$ [$Hki]
            as %r Hr
          · ipureintro; exact Hlg
          try simp only [show mvcc.KeyIndex.fresh.gens = [] from rfl, ↓reduceIte]
          icases Hr with ⟨%Hr, %gs', Hki⟩
          subst Hr
          (try wp_auto)
          -- `idx.Insert(ki)` and `kiCache[rkv.kstr] = ki`
          ihave Hix : mvcc.ownIdxPriv (GF := GF) ti L $$ [Hmu Htr]
          · iunfold mvcc.ownIdxPriv
            iexists t, lg'
            iframe Hmu Htr
            iframe #
            ipureintro; exact Hlgnn
          wp_apply (hInsert ti L p e.kv.key gs' (mvcc.kiRestoreTombstone e.rev)) $$ [$Hix $Hpk $Hki] as Hix
          · ipureintro; exact ⟨Hpn, Hnew⟩
          (try wp_auto)
          try rw [Hkstr]
          wp_apply (wp_mapInsert go.string cmv cache2 e.kv.key p) $$ [$Hcm] as Hcm
          (try wp_auto)
          wp_for_post
          iframe Hrprod Hdefer
          iexists n + 1, recv ++ [rkv1], btInsert mvcc.entryLess (p, e.kv.key, mvcc.kiRestoreTombstone e.rev) L,
            <[e.kv.key := p]> cache2, cmv, rkv1
          simp only [named]
          rw [Hlast]
          iframe Hcons kiCache Hcm currentRev rkv Htok Hrcpt Hix
          ipureintro
          have hnew' : ∀ w ∈ L, mvcc.entryLess w (p, e.kv.key, mvcc.kiRestoreTombstone e.rev) ∨
              mvcc.entryLess (p, e.kv.key, mvcc.kiRestoreTombstone e.rev) w := by
            intro w hw
            have hne : w.2.1 ≠ e.kv.key := Hnew w hw
            by_cases h1 : go.GoStringLt w.2.1 e.kv.key
            · exact Or.inl h1
            · by_cases h2 : go.GoStringLt e.kv.key w.2.1
              · exact Or.inr h2
              · exact absurd (go.goStringLt_eq_of_not_lt h1 h2) hne
          have hnone : mvcc.idxGet (mvcc.idxOfEntries L) e.kv.key = none := by
            rw [mvcc.idxGet_entries L Hsorted]
            have : L.find? (fun z => decide (z.2.1 = e.kv.key)) = none := by
              rw [List.find?_eq_none]; intro z hz; simpa using Hnew z hz
            rw [this]; rfl
          refine ⟨Hrl1, Hnlt, ?_, ?_, ?_⟩
          · rw [Hstep, ← Hidx, mvcc.idxOfEntries_btInsert]
            unfold mvcc.idxRestoreEnt
            rw [hnone, ht]
            rfl
          · rw [mvcc.take_succ_of_getElem? He']
            exact mvcc.rstLInv_btInsert HLinv e p e.kv.key _ Hpn (by simp [mvcc.kiRestore,
              mvcc.kiRestoreTombstone]) (by simp [mvcc.kiIsEmpty, mvcc.kiRestore,
              mvcc.kiRestoreTombstone]) rfl hnew'
          · exact mvcc.rstCacheOk_btInsert Hcache2 p e.kv.key _ hnew'
      · -- the key's index is in the tree
        simp only [↓reduceIte]
        -- the receipt of the entry, from the next resolution (`isTombstone`)
        wp_take_receipt as Hr1
        ihave Hrcpt : iprop(⧗ (n + 1)) $$ [Hrcpt Hr1]
        · iapply (receipt_add _ 1).2; iframe
        -- `isTombstone(rkv.key)`
        icases Hrc $$ %rkv1.key' %(mvcc.revBytes e.rev e.tomb) HRdk Htok with ⟨%dqk2, Hkb, Hkback⟩
        wp_apply (hTomb rkv1.key' (mvcc.revBytes e.rev e.tomb) dqk2) $$ [$Hkb] as Hkb
        ihave Htok := Hkback $$ Hkb
        rw [mvcc.isTomb_revBytes_self]
        icases Hkst with %Hin
        obtain ⟨kiM, Hin⟩ := Hin
        have Hfind := mvcc.find?_of_mem_sorted Hsorted' Hin
        obtain ⟨i, hi, -⟩ := mvcc.find?_entry_getElem? L _ _ Hfind
        have Hget : mvcc.idxGet (mvcc.idxOfEntries L) e.kv.key = some kiM := by
          rw [mvcc.idxGet_entries L Hsorted]; simp only at Hfind; rw [Hfind]; rfl
        obtain ⟨Hpn, Hgens, Hne, Hmod⟩ := HLinv _ Hin
        have Hlt := mvcc.rst_modified_lt Hok He' Hmod
        icases mvcc.ownTree_entry t L 1 _ Hin $$ Htr with ⟨Htr, -, #Hpk⟩
        iunfold mvcc.ownTree at Htr
        icases Htr with ⟨-, Ht, Hkis⟩
        icases BigSepL.bigSepL_lookup_acc (Φ := fun _ z => mvcc.ownEntry (GF := GF) z 1) hi |>.1 $$ Hkis
          with ⟨Hz, Hback⟩
        iunfold mvcc.ownEntry at Hz
        icases Hz with ⟨-, %gs, Hki⟩
        cases ht : e.tomb
        · -- `ki.put(lg, rev.Main, rev.Sub)`
          simp only [Bool.false_eq_true, ↓reduceIte]
          (try wp_auto)
          wp_apply (hKIput p gs kiM lg e.rev.main e.rev.sub) $$ [$Hki] as %r Hr
          · ipureintro; exact Hlg
          simp only [show mvcc.Rev.lt kiM.modified ⟨e.rev.main, e.rev.sub⟩ from Hlt, ↓reduceIte]
          icases Hr with ⟨%Hr, %gs', Hki⟩
          subst Hr
          (try wp_auto)
          wp_for_post
          iframe Hrprod Hdefer
          iexists n + 1, recv ++ [rkv1], L.set i (p, e.kv.key, mvcc.kiPut kiM e.rev), cache2, cmv, rkv1
          simp only [named]
          rw [Hlast]
          iframe Hcons kiCache Hcm currentRev rkv Htok Hrcpt
          isplitl [Hmu Ht Hback Hki]
          · iunfold mvcc.ownIdxPriv
            iexists t, lg'
            iframe Hmu
            iframe #
            isplitl []
            · ipureintro; exact Hlgnn
            iunfold mvcc.ownTree
            have hset := mvcc.itemsOfEntries_set_same L hi (mvcc.kiPut kiM e.rev)
            simp only at hset
            rw [hset]
            isplitl []
            · ipureintro; exact Hsorted
            iframe Ht
            iapply Hback
            iunfold mvcc.ownEntry
            isplitl []
            · ipureintro; exact Hpn
            iexists gs'
            iexact Hki
          ipureintro
          refine ⟨Hrl1, Hnlt, ?_, ?_, ?_⟩
          · rw [Hstep, ← Hidx]
            unfold mvcc.idxRestoreEnt
            rw [Hget, ht]
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact (mvcc.btInsert_idx_set L Hsorted i _ ⟨_, (List.getElem?_eq_some_iff.1 hi).2⟩ _).symm
          · rw [mvcc.take_succ_of_getElem? He']
            exact mvcc.rstLInv_set HLinv hi e _ (mvcc.kiPut_gens_ne_nil _ _)
              (mvcc.kiIsEmpty_kiPut _ _) (Or.inl rfl)
          · exact mvcc.rstCacheOk_set Hcache2 hi _
        · -- `err := ki.tombstone(lg, rev.Main, rev.Sub)`
          simp only [↓reduceIte]
          (try wp_auto)
          wp_apply (hKItomb p gs kiM e.kv.key lg e.rev.main e.rev.sub e0) $$ [$Hki $Hpk $Herr]
            as %r Hr
          · ipureintro; exact ⟨Hlg, Hgens⟩
          simp only [Hne, Bool.false_eq_true, ↓reduceIte]
          have hsame : L.set i (p, e.kv.key, kiM) = L := by
            rw [← (List.getElem?_eq_some_iff.1 hi).2]; exact List.set_getElem_self _
          cases hle : mvcc.kiLastEmpty kiM
          · -- the key's last generation ends with the tombstone
            simp only [Bool.false_eq_true, ↓reduceIte,
              show mvcc.Rev.lt kiM.modified ⟨e.rev.main, e.rev.sub⟩ from Hlt]
            icases Hr with ⟨%Hr, %gs', Hki⟩
            subst Hr
            (try wp_auto)
            wp_for_post
            iframe Hrprod Hdefer
            iexists n + 1, recv ++ [rkv1], L.set i (p, e.kv.key, mvcc.kiTombstone kiM e.rev), cache2,
              cmv, rkv1
            simp only [named]
            rw [Hlast]
            iframe Hcons kiCache Hcm currentRev rkv Htok Hrcpt
            isplitl [Hmu Ht Hback Hki]
            · iunfold mvcc.ownIdxPriv
              iexists t, lg'
              iframe Hmu
              iframe #
              isplitl []
              · ipureintro; exact Hlgnn
              iunfold mvcc.ownTree
              have hset := mvcc.itemsOfEntries_set_same L hi (mvcc.kiTombstone kiM e.rev)
              simp only at hset
              rw [hset]
              isplitl []
              · ipureintro; exact Hsorted
              iframe Ht
              iapply Hback
              iunfold mvcc.ownEntry
              isplitl []
              · ipureintro; exact Hpn
              iexists gs'
              iexact Hki
            ipureintro
            refine ⟨Hrl1, Hnlt, ?_, ?_, ?_⟩
            · rw [Hstep, ← Hidx]
              unfold mvcc.idxRestoreEnt
              rw [Hget, ht]
              simp only [hle, Bool.false_eq_true, ↓reduceIte]
              exact (mvcc.btInsert_idx_set L Hsorted i _ ⟨_, (List.getElem?_eq_some_iff.1 hi).2⟩ _).symm
            · rw [mvcc.take_succ_of_getElem? He']
              have hg : (mvcc.kiTombstone kiM e.rev).gens ≠ [] := by
                rw [mvcc.kiTombstone_gens]; simp
              exact mvcc.rstLInv_set HLinv hi e _ hg (mvcc.kiIsEmpty_kiTombstone _ _) (Or.inl rfl)
            · exact mvcc.rstCacheOk_set Hcache2 hi _
          · -- the last generation already empty: logged, nothing changes
            simp only [↓reduceIte]
            icases Hr with ⟨%Hr, Hki⟩
            subst Hr
            (try wp_auto)
            ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
            · iPkgInit
            wp_apply hZE as %fld -
            (try wp_auto)
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %flds -
            (try wp_auto)
            wp_apply (hWarn lg) $$ []
            · iframe #; ipureintro; exact Hlg
            (try wp_auto)
            wp_for_post
            iframe Hrprod Hdefer
            iexists n + 1, recv ++ [rkv1], L, cache2, cmv, rkv1
            simp only [named]
            rw [Hlast]
            iframe Hcons kiCache Hcm currentRev rkv Htok Hrcpt
            isplitl [Hmu Ht Hback Hki]
            · iunfold mvcc.ownIdxPriv
              iexists t, lg'
              iframe Hmu
              iframe #
              isplitl []
              · ipureintro; exact Hlgnn
              iunfold mvcc.ownTree
              isplitl []
              · ipureintro; exact Hsorted
              iframe Ht
              ihave Hall : iprop([∗list] z ∈ L.set i (p, e.kv.key, kiM), mvcc.ownEntry z 1)
                  $$ [Hback Hki]
              · iapply Hback
                iunfold mvcc.ownEntry
                isplitl []
                · ipureintro; exact Hpn
                iexists gs
                iexact Hki
              rw [hsame]
              iexact Hall
            ipureintro
            refine ⟨Hrl1, Hnlt, ?_, ?_, Hcache2⟩
            · rw [Hstep, ← Hidx]
              unfold mvcc.idxRestoreEnt
              rw [Hget, ht]
              simp only [hle, ↓reduceIte]
            · rw [mvcc.take_succ_of_getElem? He']
              exact mvcc.rstLInv_mono HLinv e
  (try wp_auto)
  iapply HΦ
  iexists γ, γr
  iframe Hprod Hrcons
  iframe #

end proof

end EtcdGrove
end Perennial
