/-
Lemmas for the lease cache's proofs (`Add`, `Update`, `delete`, `Delete`): the entries map's
lookup, and how `LeaseCacheSt.modify` keeps the state's invariants. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeaseCache

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

/-! ## `modify` -/

section pure
variable [ext : FfiSyntax]

/-- The zero `Loc` is nil. -/
theorem zero_val_loc : (zero_val Loc : Loc) = null := rfl

/-- The entries after `modify`. -/
theorem modify_entries (k : GoString) (f : LeaseEntry → LeaseEntry) (st : LeaseCacheSt) :
    (st.modify k f).entries =
      match st.entries !! k with
      | some e => GMap.insert k (f e) st.entries
      | none => st.entries := by
  unfold LeaseCacheSt.modify
  split <;> rename_i h <;> rw [h]

/-- `modify` changes only the entries. -/
theorem modify_other (k : GoString) (f : LeaseEntry → LeaseEntry) (st : LeaseCacheSt) :
    (st.modify k f).emap = st.emap ∧ (st.modify k f).rmap = st.rmap ∧
    (st.modify k f).revokes = st.revokes ∧ (st.modify k f).header = st.header ∧
    (st.modify k f).hm = st.hm ∧ (st.modify k f).frozen = st.frozen ∧
    (st.modify k f).installed = st.installed := by
  unfold LeaseCacheSt.modify
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `modify` of a missing key changes nothing. -/
theorem modify_none (k : GoString) (f : LeaseEntry → LeaseEntry) (st : LeaseCacheSt)
    (h : st.entries !! k = none) : st.modify k f = st := by
  unfold LeaseCacheSt.modify
  rw [h]

/-- `modify` of a present key. -/
theorem modify_some (k : GoString) (f : LeaseEntry → LeaseEntry) (st : LeaseCacheSt)
    (e : LeaseEntry) (h : st.entries !! k = some e) :
    st.modify k f = { st with entries := GMap.insert k (f e) st.entries } := by
  unfold LeaseCacheSt.modify
  rw [h]

/-- A change of an entry that keeps its `*leaseKey` keeps the map's contents. -/
theorem modify_lis (k : GoString) (f : LeaseEntry → LeaseEntry) (st : LeaseCacheSt)
    (hf : ∀ e, (f e).li = e.li) : (st.modify k f).lis = st.lis := by
  unfold LeaseCacheSt.modify LeaseCacheSt.lis
  split
  · rename_i e he
    apply GMap.ext
    intro k'
    simp only [GMap.lookup_fmap]
    by_cases hk : k = k'
    · subst hk; rw [GMap.lookup_insert, he]; simp [hf]
    · rw [GMap.lookup_insert_ne _ _ hk]
  · rfl

/-- A change of an entry that keeps its `*leaseKey` keeps the state well formed. -/
theorem modify_wf (k : GoString) (f : LeaseEntry → LeaseEntry) (st : LeaseCacheSt)
    (hf : ∀ e, (f e).li = e.li) (hwf : LeaseCacheWf st) : LeaseCacheWf (st.modify k f) := by
  unfold LeaseCacheSt.modify
  split
  · rename_i e he
    have look : ∀ k' e', (GMap.insert k (f e) st.entries) !! k' = some e' →
        ∃ e0, st.entries !! k' = some e0 ∧ e'.li = e0.li := by
      intro k' e' h'
      by_cases hk : k = k'
      · subst hk; rw [GMap.lookup_insert] at h'; cases h'; exact ⟨e, he, hf e⟩
      · rw [GMap.lookup_insert_ne _ _ hk] at h'; exact ⟨e', h', rfl⟩
    constructor
    · intro k1 k2 e1 e2 h1 h2 hli
      obtain ⟨a1, ha1, hl1⟩ := look k1 e1 h1
      obtain ⟨a2, ha2, hl2⟩ := look k2 e2 h2
      exact hwf.li_inj k1 k2 a1 a2 ha1 ha2 (by rw [← hl1, ← hl2, hli])
    · intro k' e' h' fr hfr
      obtain ⟨a, ha, hl⟩ := look k' e' h'
      rw [hl]; exact hwf.li_not_frozen k' a ha fr hfr
    · intro k' li hin
      rcases hwf.installed k' li hin with ⟨a, ha, hl⟩ | hfr
      · left
        by_cases hk : k = k'
        · subst hk; rw [he] at ha; cases ha
          exact ⟨f e, GMap.lookup_insert _ _ _, by rw [hf]; exact hl⟩
        · exact ⟨a, by rw [GMap.lookup_insert_ne _ _ hk]; exact ha, hl⟩
      · right; exact hfr
    · intro k' e' h'
      obtain ⟨a, ha, hl⟩ := look k' e' h'
      rw [hl]; exact hwf.entries_installed k' a ha
    · intro k' e' h'
      obtain ⟨a, ha, hl⟩ := look k' e' h'
      rw [hl]; exact hwf.li_ne k' a ha
    · intro hnil
      have := hwf.empty_if_nil hnil
      rw [this] at he
      simp at he
  · exact hwf

/-- `Update`'s first step on an entry: with no cached key-value, the fresh one appended (in the
new slice `sl'`) and the count `1`. -/
def _root_.Perennial.EtcdGrove.LeaseEntry.upd1 (e : LeaseEntry) (fresh : CachedKv) (sl' : GoSlice) : LeaseEntry :=
  if e.kvs = [] then { e with kvsSl := sl', kvs := [fresh], count := W64 1 } else e

theorem update_upd1 (e : LeaseEntry) (fresh : CachedKv) (sl' h : _) (hm : HdrM) (valSl : GoSlice)
    (val : GoString) :
    e.update fresh sl' h hm valSl val =
      match (e.upd1 fresh sl').kvs with
      | c :: cs =>
        if sint.Z c.kv.modRev < sint.Z hm.revision then
          { e.upd1 fresh sl' with kvs := c.bump hm.revision valSl val :: cs, hdr := h, hm := hm }
        else { e.upd1 fresh sl' with kvs := c.bump hm.revision valSl val :: cs }
      | [] => e.upd1 fresh sl' := rfl

/-- `Update` keeps an entry's `*leaseKey`, revision, waiter, response, `More` and ghost fields. -/
theorem update_fields (e : LeaseEntry) (fresh : CachedKv) (sl' h : _) (hm : HdrM)
    (valSl : GoSlice) (val : GoString) :
    let e' := e.update fresh sl' h hm valSl val
    e'.li = e.li ∧ e'.rev = e.rev ∧ e'.waitc = e.waitc ∧ e'.resp = e.resp ∧ e'.more = e.more ∧
      e'.lease = e.lease ∧ e'.acq = e.acq := by
  simp only [update_upd1]
  unfold LeaseEntry.upd1
  split <;> (split <;> (try split) <;> simp_all)

/-- The entries after `add`. -/
theorem add_entries (k : GoString) (e : LeaseEntry) (st : LeaseCacheSt) :
    (st.add k e).entries = GMap.insert k e st.entries := by
  unfold LeaseCacheSt.add LeaseCacheSt.removeEntry
  split
  · exact GMap.insert_delete _ _ _
  · rfl

/-- The frozen entries after `add`: the replaced entry, if any. -/
theorem add_frozen (k : GoString) (e : LeaseEntry) (st : LeaseCacheSt) :
    (st.add k e).frozen = match st.entries !! k with
      | some old => (k, old) :: st.frozen
      | none => st.frozen := by
  unfold LeaseCacheSt.add LeaseCacheSt.removeEntry
  split <;> rename_i h <;> rw [h]

/-- What `add` keeps. -/
theorem add_other (k : GoString) (e : LeaseEntry) (st : LeaseCacheSt) :
    (st.add k e).emap = st.emap ∧ (st.add k e).rmap = st.rmap ∧
    (st.add k e).revokes = st.revokes ∧
    (st.add k e).installed = st.installed ++ [(k, e.li)] := by
  unfold LeaseCacheSt.add LeaseCacheSt.removeEntry
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem add_header (k : GoString) (e : LeaseEntry) (st : LeaseCacheSt) :
    let newer := decide (st.header = null ∨ sint.Z st.hm.revision < sint.Z e.hm.revision)
    (st.add k e).header = (if newer then e.hdr else st.header) ∧
    (st.add k e).hm = (if newer then e.hm else st.hm) := by
  unfold LeaseCacheSt.add LeaseCacheSt.removeEntry
  split <;> exact ⟨rfl, rfl⟩

/-- `add` of an entry with a fresh `*leaseKey` keeps the state well formed. -/
theorem add_wf (k : GoString) (e : LeaseEntry) (st : LeaseCacheSt) (hwf : LeaseCacheWf st)
    (hfresh : ∀ k' e', st.entries !! k' = some e' → e'.li ≠ e.li)
    (hfresh' : ∀ f ∈ st.frozen, f.2.li ≠ e.li) (hnn : e.li ≠ null) (hmap : st.emap ≠ map.nil) :
    LeaseCacheWf (st.add k e) := by
  have hent := add_entries k e st
  have hfr := add_frozen k e st
  obtain ⟨hemap, -, -, hinst⟩ := add_other k e st
  have look : ∀ k' e', (st.add k e).entries !! k' = some e' →
      (k' = k ∧ e' = e) ∨ (k' ≠ k ∧ st.entries !! k' = some e') := by
    intro k' e' h'
    rw [hent] at h'
    by_cases hk : k = k'
    · subst hk; rw [GMap.lookup_insert] at h'; cases h'; exact Or.inl ⟨rfl, rfl⟩
    · rw [GMap.lookup_insert_ne _ _ hk] at h'; exact Or.inr ⟨Ne.symm hk, h'⟩
  have frozen_mem : ∀ f, f ∈ (st.add k e).frozen →
      f ∈ st.frozen ∨ ∃ old, st.entries !! k = some old ∧ f = (k, old) := by
    intro f hf
    rw [hfr] at hf
    split at hf
    · rename_i old hold
      rcases List.mem_cons.1 hf with rfl | h
      · exact Or.inr ⟨old, hold, rfl⟩
      · exact Or.inl h
    · exact Or.inl hf
  constructor
  · intro k1 k2 e1 e2 h1 h2 hli
    rcases look k1 e1 h1 with ⟨rfl, rfl⟩ | ⟨hk1, h1'⟩ <;>
      rcases look k2 e2 h2 with ⟨rfl, rfl⟩ | ⟨hk2, h2'⟩
    · rfl
    · exact absurd hli.symm (hfresh _ _ h2')
    · exact absurd hli (hfresh _ _ h1')
    · exact hwf.li_inj k1 k2 e1 e2 h1' h2' hli
  · intro k' e' h' f hf
    rcases look k' e' h' with ⟨rfl, rfl⟩ | ⟨hk', h''⟩
    · rcases frozen_mem f hf with hf' | ⟨old, hold, rfl⟩
      · exact hfresh' f hf'
      · exact hfresh k' old hold
    · rcases frozen_mem f hf with hf' | ⟨old, hold, rfl⟩
      · exact hwf.li_not_frozen k' e' h'' f hf'
      · intro heq
        exact hk' (hwf.li_inj k k' old e' hold h'' heq).symm
  · intro k' li hin
    rw [hinst] at hin
    rcases List.mem_append.1 hin with hin | hin
    · rcases hwf.installed k' li hin with ⟨e', he', hl⟩ | ⟨e', hfe, hl⟩
      · by_cases hk : k' = k
        · subst hk
          right
          refine ⟨e', ?_, hl⟩
          rw [hfr, he']; exact List.mem_cons_self
        · left
          refine ⟨e', ?_, hl⟩
          rw [hent, GMap.lookup_insert_ne _ _ (Ne.symm hk)]; exact he'
      · right
        refine ⟨e', ?_, hl⟩
        rw [hfr]
        split
        · exact List.mem_cons_of_mem _ hfe
        · exact hfe
    · rcases List.mem_singleton.1 hin with hin
      cases hin
      left
      exact ⟨e, by rw [hent, GMap.lookup_insert], rfl⟩
  · intro k' e' h'
    rw [hinst]
    rcases look k' e' h' with ⟨rfl, rfl⟩ | ⟨_, h''⟩
    · exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact List.mem_append_left _ (hwf.entries_installed k' e' h'')
  · intro k' e' h'
    rcases look k' e' h' with ⟨rfl, rfl⟩ | ⟨_, h''⟩
    · exact hnn
    · exact hwf.li_ne k' e' h''
  · intro hnil
    rw [hemap] at hnil
    exact absurd hnil hmap

theorem add_lis (k : GoString) (e : LeaseEntry) (st : LeaseCacheSt) :
    (st.add k e).lis = GMap.insert k e.li st.lis := by
  unfold LeaseCacheSt.lis
  rw [add_entries]
  exact GMap.fmap_insert _ _ _ _

end pure

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-! ### Unfolding one instance at a time (`rw`, not `unfold`, which also unfolds the
postcondition's instances) -/

theorem entryOwn_def (e : LeaseEntry) (dq : DFrac) :
    entryOwn (GF := GF) e dq = iprop(⌜e.li ≠ null⌝ ∗
      structFieldRef leaseKey go!"response" e.li ↦{dq} e.resp ∗
      structFieldRef leaseKey go!"rev" e.li ↦{dq} e.rev ∗
      structFieldRef leaseKey go!"waitc" e.li ↦{dq} e.waitc ∗ respOwn e dq ∗ waitcOk e.waitc) := rfl

theorem respOwn_def (e : LeaseEntry) (dq : DFrac) :
    respOwn (GF := GF) e dq = iprop(⌜e.resp ≠ null⌝ ∗
      structFieldRef etcdserverpb.RangeResponse go!"Header" e.resp ↦{dq} e.hdr ∗ hdrFull e.hdr e.hm ∗
      structFieldRef etcdserverpb.RangeResponse go!"Kvs" e.resp ↦{dq} e.kvsSl ∗
      e.kvsSl ↦*{dq} (e.kvs.map CachedKv.p) ∗ ownSliceCap Loc e.kvsSl dq ∗
      ([∗list] c ∈ e.kvs, cachedKvOwn c dq) ∗
      structFieldRef etcdserverpb.RangeResponse go!"More" e.resp ↦{dq} e.more ∗
      structFieldRef etcdserverpb.RangeResponse go!"Count" e.resp ↦{dq} e.count) := rfl

theorem hdrFull_def (h : Loc) (m : HdrM) :
    hdrFull (GF := GF) h m = iprop(⌜h ≠ null⌝ ∗
      structFieldRef etcdserverpb.ResponseHeader go!"ClusterId" h ↦□ m.clusterId ∗
      structFieldRef etcdserverpb.ResponseHeader go!"MemberId" h ↦□ m.memberId ∗
      structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦□ m.revision ∗
      structFieldRef etcdserverpb.ResponseHeader go!"RaftTerm" h ↦□ m.raftTerm ∗
      structFieldRef etcdserverpb.ResponseHeader go!"LeaderId" h ↦□ m.leaderId) := rfl

theorem cachedKvOwn_def (c : CachedKv) (dq : DFrac) :
    cachedKvOwn (GF := GF) c dq = iprop(⌜c.p ≠ null⌝ ∗
      structFieldRef mvccpb.KeyValue go!"Key" c.p ↦{dq} c.keySl ∗ c.keySl ↦*□ c.kv.key ∗
      structFieldRef mvccpb.KeyValue go!"CreateRevision" c.p ↦{dq} c.kv.createRev ∗
      structFieldRef mvccpb.KeyValue go!"ModRevision" c.p ↦{dq} c.kv.modRev ∗
      structFieldRef mvccpb.KeyValue go!"Version" c.p ↦{dq} c.kv.version ∗
      structFieldRef mvccpb.KeyValue go!"Value" c.p ↦{dq} c.valSl ∗ c.valSl ↦*□ c.kv.value ∗
      structFieldRef mvccpb.KeyValue go!"Lease" c.p ↦{dq} c.kv.lease) := rfl

theorem lcOwn_def (lc : Loc) (st : LeaseCacheSt) (dq : DFrac) :
    lcOwn (GF := GF) lc st dq = iprop(
      structFieldRef leaseCache go!"entries" lc ↦{dq} st.emap ∗ emapOwn st dq ∗
      structFieldRef leaseCache go!"revokes" lc ↦{dq} st.rmap ∗ st.rmap ↦${dq} st.revokes ∗
      structFieldRef leaseCache go!"header" lc ↦{dq} st.header ∗ headerOk st.header st.hm ∗
      ([∗map] _k ↦ e ∈ st.entries, entryOwn e dq) ∗
      ([∗list] f ∈ st.frozen, entryOwn f.2 DFrac.discard)) := rfl

theorem headerOk_of_hdrFull (h : Loc) (m : HdrM) : hdrFull (GF := GF) h m ⊢ headerOk h m := by
  rw [hdrFull_def]
  iintro ⟨%Hnn, #H1, #H2, #H3, #H4, #H5⟩
  unfold headerOk
  simp only [Hnn, ↓reduceIte]
  rw [hdrFull_def]
  iframe #
  ipureintro; exact Hnn

/-- A pure consequence, keeping the resources. -/
theorem keep_pure {P : IProp GF} {φ : Prop} (h : P ⊢ ⌜φ⌝) : P ⊢ ⌜φ⌝ ∗ P :=
  (and_intro h .rfl).trans persistent_and_sep.1

/-- A wholly owned `int64` cell has no other points-to. -/
theorem w64_ptsto_excl (l : Loc) (v1 v2 : w64) (dq : DFrac) :
    (l ↦{DFrac.own 1} v1 : IProp GF) ∗ l ↦{dq} v2 ⊢ False := by
  rw [typedPointsto_unseal]; unfold typedPointstoWrap
  rw [typedPointstoDef_heap, typedPointstoDef_heap]
  iintro ⟨⟨H1, -⟩, ⟨H2, -⟩⟩
  icombine H1 H2 gives %Hv
  exfalso
  have := DFrac.valid_own_op Hv.1
  simp at this

/-- A freshly allocated `*leaseKey` (its `rev` field, owned) is no entry's. -/
theorem entries_fresh (m : GMap GoString LeaseEntry) (li : Loc) (v : w64) :
    ([∗map] _k ↦ e ∈ m, entryOwn (GF := GF) e (DFrac.own 1)) ∗
      structFieldRef leaseKey go!"rev" li ↦ v ⊢ ⌜∀ k e, m !! k = some e → e.li ≠ li⌝ := by
  refine leasing_pure_forall_intro fun k => leasing_pure_forall_intro fun e => ?_
  by_cases hk : m !! k = some e
  · by_cases heq : e.li = li
    · iintro ⟨Hm, Hl⟩
      icases (BigSepM.bigSepM_lookup_acc hk).1 $$ Hm with ⟨He, -⟩
      rw [entryOwn_def]
      icases He with ⟨-, -, Hrev, -⟩
      rw [heq]
      iexfalso
      iapply w64_ptsto_excl $$ [$Hl $Hrev]
    · iintro _; ipureintro; intro _; exact heq
  · iintro _; ipureintro; intro h; exact absurd h hk

/-- A freshly allocated `*leaseKey` is no frozen entry's. -/
theorem frozen_fresh (l : List (GoString × LeaseEntry)) (li : Loc) (v : w64) :
    ([∗list] f ∈ l, entryOwn (GF := GF) f.2 DFrac.discard) ∗
      structFieldRef leaseKey go!"rev" li ↦ v ⊢ ⌜∀ f ∈ l, f.2.li ≠ li⌝ := by
  refine leasing_pure_forall_intro fun f => ?_
  by_cases hf : f ∈ l
  · by_cases heq : f.2.li = li
    · iintro ⟨Hl, Hr⟩
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hf
      icases (BigSepL.bigSepL_lookup_acc hi).1 $$ Hl with ⟨He, -⟩
      rw [entryOwn_def]
      icases He with ⟨-, -, Hrev, -⟩
      rw [heq]
      iexfalso
      iapply w64_ptsto_excl $$ [$Hr $Hrev]
    · iintro _; ipureintro; intro _; exact heq
  · iintro _; ipureintro; intro h; exact absurd h hf

/-- Installing the entry `e` under `k`: the entries' resources with `e`, and the replaced entry's
resources frozen (read-only). -/
theorem entries_insert_freeze (m : GMap GoString LeaseEntry) (k : GoString) (e : LeaseEntry) :
    ([∗map] _k ↦ x ∈ m, entryOwn (GF := GF) x (DFrac.own 1)) ∗ entryOwn e (DFrac.own 1) ⊢ |==>
      (([∗map] _k ↦ x ∈ GMap.insert k e m, entryOwn x (DFrac.own 1)) ∗
      (match m !! k with | some old => entryOwn old DFrac.discard | none => True)) := by
  cases hk : m !! k with
  | none =>
    iintro ⟨Hm, He⟩
    imodintro
    simp only
    isplitl
    · iapply (BigSepM.bigSepM_insert hk).2
      iframe
    · itrivial
  | some old =>
    iintro ⟨Hm, He⟩
    icases (BigSepM.bigSepM_delete hk).1 $$ Hm with ⟨Hold, Hm⟩
    imod (entryOwn_dfractional (GF := GF) old).dfractional_persist _ $$ Hold with Hold
    imodintro
    simp only
    iframe Hold
    iapply BigSepM.bigSepM_insert_delete.2
    iframe

/-- The facts after installing `e` (with its facts) under `k`: the replaced entry's move to the
frozen list. -/
theorem add_facts (pfx k : GoString) (e : LeaseEntry) (st : LeaseCacheSt) :
    lcFacts (GF := GF) pfx st ∗ entryFacts pfx k e ⊢ lcFacts pfx (st.add k e) := by
  unfold lcFacts
  rw [add_entries, add_frozen]
  cases hk : st.entries !! k with
  | none =>
    iintro ⟨⟨#Hm, #Hl⟩, #He⟩
    simp only
    iframe Hl
    iapply (BigSepM.bigSepM_insert hk).2
    iframe #
  | some old =>
    iintro ⟨⟨#Hm, #Hl⟩, #He⟩
    icases (BigSepM.bigSepM_delete hk).1 $$ Hm with ⟨#Hold, #Hm'⟩
    simp only
    isplitl
    · iapply BigSepM.bigSepM_insert_delete.2
      iframe #
    · iapply BigSepL.bigSepL_cons.2
      iframe #

/-- **Putting the state back after `add`**: the new entry's resources installed, the replaced
entry's frozen, the header possibly replaced. -/
theorem lcOwn_add_intro (lc : Loc) (st : LeaseCacheSt) (k : GoString) (e : LeaseEntry)
    (hmap : st.emap ≠ map.nil) :
    structFieldRef leaseCache go!"entries" lc ↦ st.emap ∗ st.emap ↦$ GMap.insert k e.li st.lis ∗
      structFieldRef leaseCache go!"revokes" lc ↦ st.rmap ∗ st.rmap ↦$ st.revokes ∗
      structFieldRef leaseCache go!"header" lc ↦
        (if decide (st.header = null ∨ sint.Z st.hm.revision < sint.Z e.hm.revision) then e.hdr
          else st.header) ∗
      headerOk st.header st.hm ∗ hdrFull e.hdr e.hm ∗
      ([∗map] _k ↦ x ∈ GMap.insert k e st.entries, entryOwn x (DFrac.own 1)) ∗
      (match st.entries !! k with | some old => entryOwn old DFrac.discard | none => True) ∗
      ([∗list] f ∈ st.frozen, entryOwn f.2 DFrac.discard) ⊢
    lcOwn (GF := GF) lc (st.add k e) (DFrac.own 1) := by
  obtain ⟨hemap, hrmap, hrev, -⟩ := add_other k e st
  obtain ⟨hhdr, hhm⟩ := add_header k e st
  rw [lcOwn_def, hemap, hrmap, hrev, hhdr, hhm, add_entries, add_frozen]
  unfold emapOwn
  rw [hemap, add_lis]
  simp only [hmap, ↓reduceIte]
  iintro ⟨He, Hm, Hr, Hrm, Hh, #Hok, #Hfull, Hents, Hold, #Hfr⟩
  iframe
  isplitl []
  · split
    · iapply headerOk_of_hdrFull; iexact Hfull
    · iexact Hok
  · cases hk : st.entries !! k with
    | none => iframe #
    | some old =>
      iapply BigSepL.bigSepL_cons.2
      iframe
      iframe #

/-- **Putting the state back after changing an entry** (keeping its `*leaseKey`): the cache's
resources with the changed entry are the changed state's. -/
theorem lcOwn_modify_intro (lc : Loc) (st : LeaseCacheSt) (k : GoString) (f : LeaseEntry → LeaseEntry)
    (e : LeaseEntry) (dq : DFrac) (hk : st.entries !! k = some e) (hf : ∀ e, (f e).li = e.li) :
    structFieldRef leaseCache go!"entries" lc ↦{dq} st.emap ∗ emapOwn st dq ∗
      structFieldRef leaseCache go!"revokes" lc ↦{dq} st.rmap ∗ st.rmap ↦${dq} st.revokes ∗
      structFieldRef leaseCache go!"header" lc ↦{dq} st.header ∗ headerOk st.header st.hm ∗
      ([∗map] _k ↦ e ∈ GMap.insert k (f e) st.entries, entryOwn e dq) ∗
      ([∗list] fr ∈ st.frozen, entryOwn fr.2 DFrac.discard) ⊢
    lcOwn (GF := GF) lc (st.modify k f) dq := by
  have hlis := modify_lis k f st hf
  have hemap := (modify_other k f st).1
  have hemp : emapOwn (GF := GF) (st.modify k f) dq = emapOwn st dq := by
    unfold emapOwn; rw [hlis, hemap]
  rw [lcOwn_def, hemp, modify_some k f st e hk]

/-- A change of an entry that keeps its revision, lease and acquisition record keeps the facts. -/
theorem modify_facts (pfx k : GoString) (f : LeaseEntry → LeaseEntry) (st : LeaseCacheSt)
    (hf : ∀ e, (f e).rev = e.rev ∧ (f e).lease = e.lease ∧ (f e).acq = e.acq) :
    lcFacts (GF := GF) pfx st ⊢ lcFacts pfx (st.modify k f) := by
  unfold LeaseCacheSt.modify
  split
  · rename_i e he
    unfold lcFacts
    iintro ⟨#Hm, #Hl⟩
    iframe Hl
    have hfe : entryFacts (GF := GF) pfx k (f e) = entryFacts pfx k e := by
      unfold entryFacts
      rw [(hf e).1, (hf e).2.1, (hf e).2.2]
    icases (BigSepM.bigSepM_insert_acc he) $$ Hm with ⟨He, Hback⟩
    iapply Hback
    rw [hfe]
    iexact He
  · iintro H; iexact H

/-- **The entries map's lookup** (`lc.entries[key]`, nil or a map): the key's entry's
`*leaseKey`, or nil. -/
theorem wp_entries_lookup (st : LeaseCacheSt) (dq : DFrac) (key : GoString)
    (hwf : LeaseCacheWf st) :
    {{ emapOwn (GF := GF) st dq }}
      (App (App (Val (map.lookup1 go.string (go.GoType.PointerType leaseKey.ty))) (Val #st.emap))
        (Val #key))
    {{ RET #(((st.entries !! key).map LeaseEntry.li).getD null); emapOwn st dq }} := by
  iintro %Φ Hm HΦ
  by_cases hnil : st.emap = map.nil
  · have hemp := hwf.empty_if_nil hnil
    rw [hnil]
    wp_pures
    rw [hemp, GMap.lookup_empty]
    simp only [Option.map_none, Option.getD_none]
    rw [← zero_val_loc]
    iapply HΦ $$ Hm
  · unfold emapOwn
    simp only [hnil, ↓reduceIte]
    wp_apply wp_map_lookup1 $$ [$Hm] as Hm
    unfold LeaseCacheSt.lis
    simp only [GMap.lookup_fmap, zero_val_loc]
    iapply HΦ $$ Hm

end defs

end leasing
end EtcdGrove
end Perennial
