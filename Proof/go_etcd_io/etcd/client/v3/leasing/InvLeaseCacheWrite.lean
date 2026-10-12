/-
Lemmas for the lease cache's writers (`Lock`, `LockRange`, `Evict`, `EvictRange`,
`clearOldRevokes`): how the state's well-formedness, facts and resources follow the transitions.
Lean-first (no Rocq counterpart); see `InvLeaseCache.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeaseCache

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

/-! ## Pure lemmas -/

section pure
variable [ext : FfiSyntax]

/-- Two states have entries under the same keys with the same `*leaseKey`s. -/
def SameLis (st st' : LeaseCacheSt) : Prop :=
  ∀ k, (st'.entries !! k).map LeaseEntry.li = (st.entries !! k).map LeaseEntry.li

theorem sameLis_lis {st st' : LeaseCacheSt} (h : SameLis st st') : st'.lis = st.lis := by
  apply GMap.ext
  intro k
  have := h k
  simp only [LeaseCacheSt.lis] at *
  exact this

theorem sameLis_lookup {st st' : LeaseCacheSt} (h : SameLis st st') {k : GoString}
    {e' : LeaseEntry} (hk : st'.entries !! k = some e') :
    ∃ e, st.entries !! k = some e ∧ e.li = e'.li := by
  have := h k
  rw [hk] at this
  cases h2 : st.entries !! k with
  | none => rw [h2] at this; simp at this
  | some e => rw [h2] at this; simp at this; exact ⟨e, rfl, this.symm⟩

theorem sameLis_lookup' {st st' : LeaseCacheSt} (h : SameLis st st') {k : GoString}
    {e : LeaseEntry} (hk : st.entries !! k = some e) :
    ∃ e', st'.entries !! k = some e' ∧ e'.li = e.li := by
  have := h k
  rw [hk] at this
  cases h2 : st'.entries !! k with
  | none => rw [h2] at this; simp at this
  | some e' => rw [h2] at this; simp at this; exact ⟨e', rfl, this⟩

/-- Well-formedness depends on the entries' `*leaseKey`s only. -/
theorem wf_sameLis {st st' : LeaseCacheSt} (hwf : LeaseCacheWf st) (h : SameLis st st')
    (he : st'.emap = st.emap) (hf : st'.frozen = st.frozen) (hi : st'.installed = st.installed) :
    LeaseCacheWf st' where
  li_inj k1 k2 e1 e2 h1 h2 heq := by
    obtain ⟨f1, hf1, hl1⟩ := sameLis_lookup h h1
    obtain ⟨f2, hf2, hl2⟩ := sameLis_lookup h h2
    exact hwf.li_inj k1 k2 f1 f2 hf1 hf2 (by rw [hl1, hl2, heq])
  li_not_frozen k e hk f hfm := by
    obtain ⟨f0, hf0, hl0⟩ := sameLis_lookup h hk
    rw [hf] at hfm
    rw [← hl0]; exact hwf.li_not_frozen k f0 hf0 f hfm
  installed k li hmem := by
    rw [hi] at hmem
    rcases hwf.installed k li hmem with ⟨e, he0, hli⟩ | ⟨e, hfm, hli⟩
    · obtain ⟨e', he', hl'⟩ := sameLis_lookup' h he0
      exact Or.inl ⟨e', he', by rw [hl', hli]⟩
    · exact Or.inr ⟨e, by rw [hf]; exact hfm, hli⟩
  entries_installed k e hk := by
    obtain ⟨f0, hf0, hl0⟩ := sameLis_lookup h hk
    rw [hi, ← hl0]; exact hwf.entries_installed k f0 hf0
  li_ne k e hk := by
    obtain ⟨f0, hf0, hl0⟩ := sameLis_lookup h hk
    rw [← hl0]; exact hwf.li_ne k f0 hf0
  empty_if_nil hnil := by
    have hemp := hwf.empty_if_nil (by rw [← he]; exact hnil)
    apply GMap.ext
    intro k
    have := h k
    rw [hemp] at this
    simp only [GMap.lookup_empty, Option.map_none] at this
    cases h2 : st'.entries !! k with
    | none => rfl
    | some _ => rw [h2] at this; simp at this

/-- The entries' facts depend on their revision, acquired record and lease only. -/
def SameFacts (st st' : LeaseCacheSt) : Prop :=
  (∀ k e', st'.entries !! k = some e' → ∃ e, st.entries !! k = some e ∧ e'.rev = e.rev ∧
    e'.acq = e.acq ∧ e'.lease = e.lease) ∧
  (∀ f ∈ st'.frozen, f ∈ st.frozen ∨ st.entries !! f.1 = some f.2)

theorem sameLis_insert (st : LeaseCacheSt) (k : GoString) (e e' : LeaseEntry)
    (hk : st.entries !! k = some e) (hli : e'.li = e.li) :
    SameLis st { st with entries := GMap.insert k e' st.entries } := by
  intro k'
  by_cases hkk : k = k'
  · subst hkk; simp [hk, hli]
  · simp [hkk]

theorem sameFacts_insert (st : LeaseCacheSt) (k : GoString) (e e' : LeaseEntry)
    (hk : st.entries !! k = some e) (hr : e'.rev = e.rev) (ha : e'.acq = e.acq)
    (hl : e'.lease = e.lease) :
    SameFacts st { st with entries := GMap.insert k e' st.entries } := by
  refine ⟨?_, fun f hf => Or.inl hf⟩
  intro k' e2 hk'
  by_cases hkk : k = k'
  · subst hkk
    simp only [GMap.lookup_insert] at hk'
    cases hk'
    exact ⟨e, hk, hr, ha, hl⟩
  · simp only [GMap.lookup_insert_ne _ _ hkk] at hk'
    exact ⟨e2, hk', rfl, rfl, rfl⟩

theorem waitcOnly_setWaitc (st : LeaseCacheSt) (k : GoString) (ch : GoChan) :
    WaitcOnly st (st.setWaitc k ch) := by
  unfold LeaseCacheSt.setWaitc
  cases hk : st.entries !! k with
  | none => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
  | some e =>
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun k' => ?_⟩
    simp only
    by_cases hkk : k = k'
    · subst hkk; simp [hk]
    · simp [hkk]

theorem waitcOnly_trans {a b c : LeaseCacheSt} (h1 : WaitcOnly a b) (h2 : WaitcOnly b c) :
    WaitcOnly a c := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := h1
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := h2
  exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6,
    b7.trans a7, fun k => (b8 k).trans (a8 k)⟩

theorem waitcOnly_refl (a : LeaseCacheSt) : WaitcOnly a a :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

/-- The entries `ents` differ from `st`'s in their waiter channels only. -/
def WaitcOnlyEnts (st : LeaseCacheSt) (ents : GMap GoString LeaseEntry) : Prop :=
  ∀ k, (ents !! k).map (fun e => { e with waitc := null }) =
    (st.entries !! k).map (fun e => { e with waitc := null })

theorem waitcOnly_ents {st : LeaseCacheSt} {ents : GMap GoString LeaseEntry}
    (h : WaitcOnlyEnts st ents) : WaitcOnly st { st with entries := ents } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, h⟩

theorem waitcOnlyEnts_lookup {st : LeaseCacheSt} {ents : GMap GoString LeaseEntry}
    (h : WaitcOnlyEnts st ents) {k : GoString} {e' : LeaseEntry} (hk : ents !! k = some e') :
    ∃ e, st.entries !! k = some e ∧ e'.li = e.li ∧ e'.rev = e.rev ∧ e'.acq = e.acq ∧
      e'.lease = e.lease := by
  have := h k
  rw [hk] at this
  cases h2 : st.entries !! k with
  | none => rw [h2] at this; simp at this
  | some e =>
    rw [h2] at this
    simp only [Option.map_some, Option.some.injEq, LeaseEntry.mk.injEq] at this
    exact ⟨e, rfl, this.1, this.2.1, this.2.2.2.2.2.2.2.2.2.2.2, this.2.2.2.2.2.2.2.2.2.2.1⟩

theorem sameLis_of_waitc {st : LeaseCacheSt} {ents : GMap GoString LeaseEntry}
    (h : WaitcOnlyEnts st ents) : SameLis st { st with entries := ents } := by
  intro k
  have := congrArg (Option.map LeaseEntry.li) (h k)
  simp only [Option.map_map] at this
  exact this

theorem sameFacts_of_waitc {st : LeaseCacheSt} {ents : GMap GoString LeaseEntry}
    (h : WaitcOnlyEnts st ents) : SameFacts st { st with entries := ents } := by
  refine ⟨fun k e' hk => ?_, fun f hf => Or.inl hf⟩
  obtain ⟨e, he, -, h1, h2, h3⟩ := waitcOnlyEnts_lookup h hk
  exact ⟨e, he, h1, h2, h3⟩

theorem waitcOnlyEnts_refl (st : LeaseCacheSt) : WaitcOnlyEnts st st.entries := fun _ => rfl

theorem waitcOnlyEnts_insert {st : LeaseCacheSt} {ents : GMap GoString LeaseEntry}
    (h : WaitcOnlyEnts st ents) (k : GoString) (e : LeaseEntry) (hk : ents !! k = some e)
    (ch : GoChan) : WaitcOnlyEnts st (GMap.insert k { e with waitc := ch } ents) := by
  intro k'
  by_cases hkk : k = k'
  · subst hkk; rw [← h k, hk]; simp
  · simp only [GMap.lookup_insert_ne _ _ hkk]; exact h k'

theorem ldel {V : Type} (m : GMap GoString V) (k k' : GoString) (v : V) :
    (GMap.delete k m) !! k' = some v ↔ k ≠ k' ∧ m !! k' = some v := by
  by_cases h : k = k'
  · subst h; simp
  · simp [h]

/-- `st` with `key`'s entry `e` removed and frozen, and revocation times `rv`. -/
def lcFreeze (st : LeaseCacheSt) (key : GoString) (e : LeaseEntry)
    (rv : GMap GoString time.Time) : LeaseCacheSt :=
  { st with entries := GMap.delete key st.entries, frozen := (key, e) :: st.frozen, revokes := rv }

theorem evict_eq (st : LeaseCacheSt) (key : GoString) (e : LeaseEntry) (t : time.Time)
    (hk : st.entries !! key = some e) :
    st.evict key t = lcFreeze st key e (GMap.insert key t st.revokes) := by
  simp [LeaseCacheSt.evict, LeaseCacheSt.removeEntry, lcFreeze, hk]

theorem evict_none (st : LeaseCacheSt) (key : GoString) (t : time.Time)
    (hk : st.entries !! key = none) : st.evict key t = st := by
  simp [LeaseCacheSt.evict, hk]

theorem wf_freeze {st : LeaseCacheSt} (hwf : LeaseCacheWf st) {key : GoString} {e : LeaseEntry}
    (hk : st.entries !! key = some e) (rv : GMap GoString time.Time) :
    LeaseCacheWf (lcFreeze st key e rv) where
  li_inj k1 k2 e1 e2 h1 h2 heq := by
    simp only [lcFreeze] at h1 h2; rw [ldel] at h1 h2
    exact hwf.li_inj k1 k2 e1 e2 h1.2 h2.2 heq
  li_not_frozen k e1 h1 f hf := by
    simp only [lcFreeze, List.mem_cons] at h1 hf; rw [ldel] at h1
    rcases hf with rfl | hf
    · intro heq
      exact h1.1 (hwf.li_inj key k e e1 hk h1.2 heq)
    · exact hwf.li_not_frozen k e1 h1.2 f hf
  installed k li hmem := by
    simp only [lcFreeze] at hmem ⊢
    rcases hwf.installed k li hmem with ⟨e1, he1, hli⟩ | ⟨e1, hfm, hli⟩
    · by_cases hkk : key = k
      · subst hkk
        rw [hk] at he1; cases he1
        exact Or.inr ⟨e, List.mem_cons_self .., hli⟩
      · exact Or.inl ⟨e1, by rw [GMap.lookup_delete_ne _ hkk]; exact he1, hli⟩
    · exact Or.inr ⟨e1, List.mem_cons_of_mem _ hfm, hli⟩
  entries_installed k e1 h1 := by
    simp only [lcFreeze] at h1 ⊢; rw [ldel] at h1
    exact hwf.entries_installed k e1 h1.2
  li_ne k e1 h1 := by
    simp only [lcFreeze] at h1; rw [ldel] at h1
    exact hwf.li_ne k e1 h1.2
  empty_if_nil hnil := by
    have := hwf.empty_if_nil hnil
    rw [this] at hk; simp at hk

theorem sameFacts_freeze (st : LeaseCacheSt) (key : GoString) (e : LeaseEntry)
    (hk : st.entries !! key = some e) (rv : GMap GoString time.Time) :
    SameFacts st (lcFreeze st key e rv) := by
  refine ⟨fun k e' h => ?_, fun f hf => ?_⟩
  · simp only [lcFreeze] at h; rw [ldel] at h
    exact ⟨e', h.2, rfl, rfl, rfl⟩
  · simp only [lcFreeze, List.mem_cons] at hf
    rcases hf with rfl | hf
    · exact Or.inr hk
    · exact Or.inl hf

theorem freeze_lis (st : LeaseCacheSt) (key : GoString) (e : LeaseEntry)
    (rv : GMap GoString time.Time) : (lcFreeze st key e rv).lis = GMap.delete key st.lis := by
  simp [lcFreeze, LeaseCacheSt.lis, GMap.fmap_delete]

theorem evictRange_none (st : LeaseCacheSt) (key e : GoString) (t : time.Time)
    (h : ¬ ∃ k ent, st.entries !! k = some ent ∧ leaseInRange k key e = true) :
    st.evictRange key e t = st := by
  unfold LeaseCacheSt.evictRange
  rw [if_neg h]

theorem evictRange_present (st : LeaseCacheSt) (key e : GoString) (t : time.Time)
    (h : ∃ k ent, st.entries !! k = some ent ∧ leaseInRange k key e = true) (en : LeaseEntry)
    (hk : st.entries !! key = some en) :
    st.evictRange key e t = lcFreeze st key en (GMap.insert key t st.revokes) := by
  unfold LeaseCacheSt.evictRange
  rw [if_pos h]
  simp [LeaseCacheSt.removeEntry, lcFreeze, hk]

theorem evictRange_absent (st : LeaseCacheSt) (key e : GoString) (t : time.Time)
    (h : ∃ k ent, st.entries !! k = some ent ∧ leaseInRange k key e = true)
    (hk : st.entries !! key = none) :
    st.evictRange key e t = { st with revokes := GMap.insert key t st.revokes } := by
  unfold LeaseCacheSt.evictRange
  rw [if_pos h]
  simp [LeaseCacheSt.removeEntry, hk]

/-- The state after `key`'s eviction at `t` (its entry frozen if any, its revocation time `t`). -/
def evictKeySt (st : LeaseCacheSt) (key : GoString) (t : time.Time) : LeaseCacheSt :=
  match st.entries !! key with
  | some en => lcFreeze st key en (GMap.insert key t st.revokes)
  | none => { st with revokes := GMap.insert key t st.revokes }

theorem evictRange_found (st : LeaseCacheSt) (key e : GoString) (t : time.Time)
    (h : ∃ k ent, st.entries !! k = some ent ∧ leaseInRange k key e = true) :
    st.evictRange key e t = evictKeySt st key t := by
  unfold evictKeySt
  cases hk : st.entries !! key with
  | none => exact evictRange_absent st key e t h hk
  | some en => exact evictRange_present st key e t h en hk

theorem wf_evictKeySt {st : LeaseCacheSt} (hwf : LeaseCacheWf st) (key : GoString)
    (t : time.Time) : LeaseCacheWf (evictKeySt st key t) := by
  unfold evictKeySt
  cases hk : st.entries !! key with
  | none =>
    simp only
    exact ⟨hwf.li_inj, hwf.li_not_frozen, hwf.installed, hwf.entries_installed, hwf.li_ne,
      hwf.empty_if_nil⟩
  | some en => exact wf_freeze hwf hk _

theorem sameFacts_evictKeySt (st : LeaseCacheSt) (key : GoString) (t : time.Time) :
    SameFacts st (evictKeySt st key t) := by
  unfold evictKeySt
  cases hk : st.entries !! key with
  | none => exact ⟨fun k e' h => ⟨e', h, rfl, rfl, rfl⟩, fun f hf => Or.inl hf⟩
  | some en => exact sameFacts_freeze st key en hk _

theorem evictKeySt_lis (st : LeaseCacheSt) (key : GoString) (t : time.Time) :
    (evictKeySt st key t).lis = GMap.delete key st.lis := by
  unfold evictKeySt
  cases hk : st.entries !! key with
  | none =>
    simp only
    rw [GMap.delete_notin]; · rfl
    simp [LeaseCacheSt.lis, hk]
  | some en => exact freeze_lis st key en _

end pure

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem entryFacts_same (pfx k : GoString) (e e' : LeaseEntry) (hr : e'.rev = e.rev)
    (ha : e'.acq = e.acq) (hl : e'.lease = e.lease) :
    entryFacts (GF := GF) pfx k e ⊢ entryFacts pfx k e' := by
  unfold entryFacts; rw [hr, ha, hl]

theorem lcFacts_same (pfx : GoString) (st st' : LeaseCacheSt) (h : SameFacts st st') :
    lcFacts (GF := GF) pfx st ⊢ lcFacts pfx st' := by
  unfold lcFacts
  iintro ⟨#H1, #H2⟩
  isplitl
  · iapply (BigSepM.bigSepM_forall (Φ := fun k e => entryFacts (GF := GF) pfx k e)).2
    iintro %k %e' %hk'
    obtain ⟨e, hk, hr, ha, hl⟩ := h.1 k e' hk'
    iapply entryFacts_same pfx k e e' hr ha hl
    iapply (BigSepM.bigSepM_lookup hk) $$ H1
  · iapply (BigSepL.bigSepL_forall_eqv (Φ := fun _ (f : GoString × LeaseEntry) => entryFacts (GF := GF) pfx f.1 f.2)).2
    iintro %i %f %hf
    rcases h.2 f (List.mem_of_getElem? hf) with hm | hm
    · obtain ⟨j, hj⟩ := List.getElem?_of_mem hm
      iapply (BigSepL.bigSepL_lookup hj) $$ H2
    · iapply (BigSepM.bigSepM_lookup hm) $$ H1

/-- A pending broadcast channel's receive right. -/
theorem pending_unknown (ch : GoChan) (γ : ChanNames) (Q : IProp GF) :
    ownBroadcastChan ch γ Q .Pending ⊢ ownBroadcastChan ch γ Q .Pending ∗
      ownBroadcastChan ch γ Q .Unknown := by
  iintro H
  icases ownBroadcastChan_open _ _ _ _ $$ H with ⟨%γch, #Hint, Htok⟩
  isplitl [Htok]
  · iapply ownBroadcastChan_close _ _ _ _ γch; iframe; iframe #
  · iapply ownBroadcastChan_close _ _ _ .Unknown γch; iframe #

/-- **One entry's resources**, and the way back for a new entry with the same `*leaseKey`. -/
theorem lcOwn_entry_acc (lc : Loc) (st : LeaseCacheSt) (dq : DFrac) (k : GoString)
    (e : LeaseEntry) (hk : st.entries !! k = some e) :
    lcOwn (GF := GF) lc st dq ⊢ entryOwn e dq ∗
      (∀ e', ⌜e'.li = e.li⌝ -∗ entryOwn e' dq -∗
        lcOwn lc { st with entries := GMap.insert k e' st.entries } dq) := by
  unfold lcOwn
  iintro ⟨H1, H2, H3, H4, H5, #H6, Hents, #H8⟩
  icases (BigSepM.bigSepM_insert_acc hk) $$ Hents with ⟨He, Hents⟩
  iframe He
  iintro %e' %hli He'
  have hl := sameLis_lis (sameLis_insert st k e e' hk hli)
  unfold emapOwn
  simp only [hl]
  iframe
  iframe #
  iapply Hents $$ He'

/-- The entries field and the map, and the way back. -/
theorem lcOwn_emap_acc (lc : Loc) (st : LeaseCacheSt) (dq : DFrac) :
    lcOwn (GF := GF) lc st dq ⊢
      structFieldRef leaseCache go!"entries" lc ↦{dq} st.emap ∗ emapOwn st dq ∗
      (structFieldRef leaseCache go!"entries" lc ↦{dq} st.emap -∗ emapOwn st dq -∗
        lcOwn lc st dq) := by
  unfold lcOwn
  iintro ⟨H1, H2, H3, H4, H5, #H6, H7, #H8⟩
  iframe H1 H2
  iintro H1 H2
  iframe
  iframe #

/-- **Looking up `key` in the entries map** (nil or not): the `*leaseKey` of its entry, or nil. -/
theorem wp_emap_lookup (st : LeaseCacheSt) (key : GoString) (dq : DFrac)
    (hwf : LeaseCacheWf st) :
    {{ emapOwn (GF := GF) st dq }}
      (App (App (Val (map.lookup1 go.string (go.GoType.PointerType leaseKey.ty))) (Val #st.emap))
        (Val #key))
    {{ RET #(((st.entries !! key).map LeaseEntry.li).getD (zero_val Loc)); emapOwn st dq }} := by
  iintro %Φ Hm HΦ
  by_cases hnil : st.emap = map.nil
  · have hemp := hwf.empty_if_nil hnil
    rw [hnil, hemp]
    wp_pures
    simp only [GMap.lookup_empty, Option.map_none, Option.getD_none]
    iapply HΦ $$ Hm
  · unfold emapOwn
    simp only [hnil, ↓reduceIte]
    wp_apply wp_map_lookup1 $$ [$Hm] as Hm
    simp only [LeaseCacheSt.lis, GMap.lookup_fmap]
    iapply HΦ $$ Hm

/-- **The entries' resources apart**, and the way back for new entries with the same
`*leaseKey`s (the map and the other fields unchanged). -/
theorem lcOwn_entries_acc (lc : Loc) (st : LeaseCacheSt) (dq : DFrac) :
    lcOwn (GF := GF) lc st dq ⊢ ([∗map] _k ↦ e ∈ st.entries, entryOwn e dq) ∗
      (∀ ents : GMap GoString LeaseEntry, ⌜SameLis st { st with entries := ents }⌝ -∗
        ([∗map] _k ↦ e ∈ ents, entryOwn e dq) -∗ lcOwn lc { st with entries := ents } dq) := by
  unfold lcOwn
  iintro ⟨H1, H2, H3, H4, H5, #H6, Hents, #H8⟩
  iframe Hents
  iintro %ents %hsl Hents
  have hl := sameLis_lis hsl
  unfold emapOwn
  simp only [hl]
  iframe
  iframe #

/-- **The entries field, the map and the entries' resources apart**, and the way back for new
entries with the same `*leaseKey`s. -/
theorem lcOwn_ents_emap_acc (lc : Loc) (st : LeaseCacheSt) (dq : DFrac) :
    lcOwn (GF := GF) lc st dq ⊢ structFieldRef leaseCache go!"entries" lc ↦{dq} st.emap ∗
      emapOwn st dq ∗ ([∗map] _k ↦ e ∈ st.entries, entryOwn e dq) ∗
      (∀ ents : GMap GoString LeaseEntry, ⌜SameLis st { st with entries := ents }⌝ -∗
        structFieldRef leaseCache go!"entries" lc ↦{dq} st.emap -∗ emapOwn st dq -∗
        ([∗map] _k ↦ e ∈ ents, entryOwn e dq) -∗ lcOwn lc { st with entries := ents } dq) := by
  unfold lcOwn
  iintro ⟨H1, H2, H3, H4, H5, #H6, Hents, #H8⟩
  iframe H1 H2 Hents
  iintro %ents %hsl H1 H2 Hents
  have hl := sameLis_lis hsl
  unfold emapOwn at *
  simp only [hl]
  iframe
  iframe #

/-- **Freezing an entry**: the cache's resources for `st`, with the entries map and the
revocation map changed accordingly, give those of `st.freeze key e rv` (the entry's resources
become read-only). -/
theorem lcOwn_freeze (lc : Loc) (st : LeaseCacheSt) (key : GoString) (e : LeaseEntry)
    (hk : st.entries !! key = some e) :
    lcOwn (GF := GF) lc st (DFrac.own 1) ⊢
      structFieldRef leaseCache go!"entries" lc ↦ st.emap ∗ emapOwn st (DFrac.own 1) ∗
      structFieldRef leaseCache go!"revokes" lc ↦ st.rmap ∗ st.rmap ↦$ st.revokes ∗
      (∀ rv, emapOwn (lcFreeze st key e rv) (DFrac.own 1) -∗ st.rmap ↦$ rv -∗
        structFieldRef leaseCache go!"entries" lc ↦ st.emap -∗
        structFieldRef leaseCache go!"revokes" lc ↦ st.rmap ==∗
        lcOwn lc (lcFreeze st key e rv) (DFrac.own 1)) := by
  unfold lcOwn
  iintro ⟨H1, H2, H3, H4, H5, #H6, Hents, #H8⟩
  iframe H1 H2 H3 H4
  iintro %rv H2 H4 H1 H3
  icases (BigSepM.bigSepM_delete hk).1 $$ Hents with ⟨He, Hents⟩
  imod (entryOwn_dfractional (GF := GF) e).dfractional_persist (DFrac.own 1) $$ He with #He
  imodintro
  simp only [lcFreeze]
  iframe
  iframe #

/-- One entry's resources, and the way back (unchanged). -/
theorem lcOwn_entry_acc' (lc : Loc) (st : LeaseCacheSt) (dq : DFrac) (k : GoString)
    (e : LeaseEntry) (hk : st.entries !! k = some e) :
    lcOwn (GF := GF) lc st dq ⊢ entryOwn e dq ∗ (entryOwn e dq -∗ lcOwn lc st dq) := by
  unfold lcOwn
  iintro ⟨H1, H2, H3, H4, H5, #H6, Hents, #H8⟩
  icases (BigSepM.bigSepM_lookup_acc hk).1 $$ Hents with ⟨He, Hents⟩
  iframe He
  iintro He
  iframe
  iframe #
  iapply Hents $$ He

/-- The entries field and map and the revocation field and map apart, and the way back for any
revocation times. -/
theorem lcOwn_emap_revokes_acc (lc : Loc) (st : LeaseCacheSt) :
    lcOwn (GF := GF) lc st (DFrac.own 1) ⊢
      structFieldRef leaseCache go!"entries" lc ↦ st.emap ∗ emapOwn st (DFrac.own 1) ∗
      structFieldRef leaseCache go!"revokes" lc ↦ st.rmap ∗ st.rmap ↦$ st.revokes ∗
      (∀ rv, structFieldRef leaseCache go!"entries" lc ↦ st.emap -∗ emapOwn st (DFrac.own 1) -∗
        structFieldRef leaseCache go!"revokes" lc ↦ st.rmap -∗ st.rmap ↦$ rv -∗
        lcOwn lc { st with revokes := rv } (DFrac.own 1)) := by
  unfold lcOwn
  iintro ⟨H1, H2, H3, H4, H5, #H6, Hents, #H8⟩
  iframe H1 H2 H3 H4
  iintro %rv H1 H2 H3 H4
  unfold emapOwn at *
  dsimp only
  iframe
  iframe #

/-- **For `EvictRange`**: the entries field and (non-nil) map and the revocation field and map
apart, and the way back either unchanged, or after `key`'s eviction at some `t`. -/
theorem lcOwn_evictKey_acc (lc : Loc) (st : LeaseCacheSt) (key : GoString)
    (hnil : st.emap ≠ map.nil) :
    lcOwn (GF := GF) lc st (DFrac.own 1) ⊢
      structFieldRef leaseCache go!"entries" lc ↦ st.emap ∗ st.emap ↦$ st.lis ∗
      structFieldRef leaseCache go!"revokes" lc ↦ st.rmap ∗ st.rmap ↦$ st.revokes ∗
      ((structFieldRef leaseCache go!"entries" lc ↦ st.emap -∗ st.emap ↦$ st.lis -∗
          structFieldRef leaseCache go!"revokes" lc ↦ st.rmap -∗ st.rmap ↦$ st.revokes -∗
          lcOwn lc st (DFrac.own 1)) ∧
       (∀ t, structFieldRef leaseCache go!"entries" lc ↦ st.emap -∗
          st.emap ↦$ GMap.delete key st.lis -∗
          structFieldRef leaseCache go!"revokes" lc ↦ st.rmap -∗
          st.rmap ↦$ GMap.insert key t st.revokes ==∗
          lcOwn lc (evictKeySt st key t) (DFrac.own 1))) := by
  unfold lcOwn
  iintro ⟨H1, H2, H3, H4, H5, #H6, Hents, #H8⟩
  unfold emapOwn
  simp only [hnil, ↓reduceIte]
  iframe H1 H2 H3 H4
  isplit
  · iintro H1 H2 H3 H4
    iframe
    iframe #
  · iintro %t H1 H2 H3 H4
    unfold evictKeySt
    cases hk : st.entries !! key with
    | none =>
      simp only
      rw [GMap.delete_notin _ _ (by simp [LeaseCacheSt.lis, hk])]
      imodintro
      simp only [hnil, ↓reduceIte, LeaseCacheSt.lis]
      iframe
      iframe #
    | some en =>
      simp only
      icases (BigSepM.bigSepM_delete hk).1 $$ Hents with ⟨He, Hents⟩
      imod (entryOwn_dfractional (GF := GF) en).dfractional_persist (DFrac.own 1) $$ He with #He
      imodintro
      simp only [show (lcFreeze st key en (GMap.insert key t st.revokes)).emap = st.emap
        from rfl, hnil, ↓reduceIte]
      rw [freeze_lis]
      simp only [lcFreeze]
      iframe
      iframe #

end defs

end leasing
end EtcdGrove
end Perennial
