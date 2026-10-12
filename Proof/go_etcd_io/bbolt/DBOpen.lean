/-
`Open` of a well-formed file: the database's state once it is open (`openState`: no reader, no
writer, the freelist's free ids those of the current meta's freelist page), and its facts
(`dbOK_open`) from the file's (`fileWF`).

`fileWF bs ps`: the file's pages are of `ps` bytes, and for its two metas (whichever bytes the
file holds, one valid) the current tree (of the meta `db.meta()` picks) is strict, its pages
disjoint and inside the file, none free or a meta page; the freelist is synced (the meta names a
freelist page, inside the file, whose ids are distinct, below the high-water mark and below
`2^62`); the txid has not reached `2^64 - 1`. bbolt writes such files (with `NoFreelistSync`
off): the proof of `Commit` is to show it keeps this.
-/
module

public import Proof.go_etcd_io.bbolt.DBRollback
public import Spec.go_etcd_io.bbolt.DB__loadFreelist
public import Spec.go_etcd_io.bbolt.DB__mmap

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section open_defs
variable [ext : FfiSyntax]

/-- The current meta `m`'s facts in the file `bs` of pages of `ps` bytes. -/
def fileCurOK (bs : List w8) (ps : Nat) (m : internal.common.Meta) : Prop :=
  let hwm := uint.nat m.pgid'
  let root := uint.nat m.root'.root'
  let cur := treePages (filePages bs ps hwm) root
  let fid := uint.nat m.freelist'
  let fpg := pageAt bs ps fid
  treeStrict cur hwm root ∧ pagesDisjoint cur ∧
  (∀ id pg, cur !! id = some pg → id + pageSpan bs ps id ≤ min (bs.length / ps) hwm) ∧
  (∀ s, coversSlot cur s → 2 ≤ s ∧ W64 s ∉ flIds fpg) ∧
  m.freelist' ≠ W64 18446744073709551615 ∧ 2 ≤ fid ∧ fid + pageSpan bs ps fid ≤ bs.length / ps ∧
  flPageOK fpg ∧ (∀ x ∈ flIds fpg, uint.Z x < uint.Z m.pgid' ∧ uint.Z x < 2 ^ 62) ∧
  uint.Z m.txid' + 1 < 2 ^ 64

/-- A well-formed database file (see the module doc). -/
def fileWF (bs : List w8) (ps : Nat) : Prop :=
  80 ≤ ps ∧ ps < 2 ^ 32 ∧ 2 * ps ≤ bs.length ∧ bs.length < 2 ^ 47 ∧
  ∀ v0 v1, ((slotAt bs ps 0).drop 16).take 64 = metaBytes v0 →
    ((slotAt bs ps 1).drop 16).take 64 = metaBytes v1 → (metaValid v0 ∨ metaValid v1) →
    fileCurOK bs ps (if metaPick v0 v1 then v1 else v0)

end open_defs

section open_state
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

/-- The database just opened: the file `bs` mapped at `data` (`sz` bytes), its free ids
`free`, no transaction open. -/
def openState (file : Loc) (fd : w64) (bs : List w8) (data : Loc) (sz ps : Nat)
    (free : List w64) (path : GoString) : DBState :=
  { file := file, fd := fd, bs := bs, data := data, sz := sz, ps := ps,
    fl := { FLState.empty with free := free }, readers := ∅, rem := fun _ => halfQ, frem := 1,
    rwtx := null, wr := none, path := path }

theorem dbOK_open (file : Loc) (fd : w64) (bs : List w8) (data : Loc) (sz ps : Nat)
    (free : List w64) (path : GoString) (v0 v1 : internal.common.Meta)
    (hwf : fileWF bs ps) (hm : metasOK bs ps v0 v1) (hsz : bs.length ≤ sz)
    (hszb : sz ≤ 281474976710655) (hdata : data.locCar ≠ 0)
    (hfree : free.Perm (flIds (pageAt bs ps
      (uint.nat (if metaPick v0 v1 then v1 else v0).freelist')))) :
    dbOK (openState file fd bs data sz ps free path) v0 v1 := by
  obtain ⟨hps, hps2, h2, hlen, hcur⟩ := hwf
  obtain ⟨hm0, hm1, hv⟩ := hm
  have hc := hcur v0 v1 hm0 hm1 hv
  obtain ⟨cwf, cdisj, cin, cfree, cfl, cfid2, cfid, cfpg, cids, ctx⟩ := hc
  have hns : (openState file fd bs data sz ps free path).nslots = bs.length / ps := by
    unfold DBState.nslots openState; simp only; rw [Nat.min_eq_right hsz]
  have hfree' : ∀ x, x ∈ free ↔ x ∈ flIds (pageAt bs ps
      (uint.nat (if metaPick v0 v1 then v1 else v0).freelist')) := fun x => hfree.mem_iff
  refine ⟨hps, hps2, ?_, ⟨hszb, by show bs.length < 2 ^ 62; omega⟩, hdata, hm0, hm1, hv, ⟨cwf, cdisj, ?_, ?_, ?_, ?_, ?_⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hns]; exact (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  · intro id pg hid; rw [hns]; exact cin id pg hid
  · intro id pg hid a ha; simp [openState, FLState.empty] at ha
  · intro s hs
    obtain ⟨c2, cnot⟩ := cfree s hs
    refine ⟨c2, fun hx => cnot ((hfree' _).1 hx), fun t pd a ht _ => ?_⟩
    simp [openState, FLState.empty] at ht
  · refine ⟨fun x hx => ((cids x ((hfree' x).1 hx)).1), fun t pd p ht => ?_, fun t pd p ht => ?_,
      fun w hw => ?_, ctx, fun x hx => (cids x ((hfree' x).1 hx)).2, fun t pd p ht => ?_⟩
    · simp [openState, FLState.empty] at ht
    · simp [openState, FLState.empty] at ht
    · simp [openState] at hw
    · simp [openState, FLState.empty] at ht
  · exact ⟨fun k r hk => by simp [openState] at hk, fun w hw => by simp [openState] at hw⟩
  · intro k r hk; simp [openState] at hk
  · intro k r hk; simp [openState] at hk
  · intro s _
    show fracSum halfQ (wQ none _ (readersQ ∅ _)) halfQ
    unfold readersQ; rw [GMap.mapFold_empty]; rfl
  · show fracSum 1 (wQ none _ (readersQ ∅ _)) 1
    unfold readersQ; rw [GMap.mapFold_empty]; rfl
  · show ([] : List w64).Perm _
    show ([] : List w64).Perm ((∅ : GMap Nat Reader).toList.map _)
    simp
  · show (∅ : GMap Nat Reader).size < _
    rw [GMap.map_size_empty, sync.rwmutex.actualMaxReaders_unseal]; decide
  · exact ⟨⟨fun _ => rfl, fun _ => rfl⟩, fun w hw => by simp [openState] at hw⟩

open Iris.ProofMode in
/-- A new mapping of the file: the database's half of the whole slots, and the tail. -/
theorem open_slots (d : Loc) (bs : List w8) (sz ps : Nat) :
    mapRange (GF := GF) (some (d, sz)) bs 0 sz ⊢
      slotsView d bs ps (fun _ => halfQ) (List.range (min sz bs.length / ps)) ∗
        mapTail d bs sz ps := by
  have hfit : (min sz bs.length / ps) * ps ≤ bs.length := by
    have := Nat.div_mul_le_self (min sz bs.length) ps; omega
  iintro Hm
  icases (mapRange_slots (GF := GF) d bs sz ps).1 $$ Hm with ⟨Hs, Ht⟩
  ihave Hs := (slots_const (GF := GF) d bs ps halfQ _ hfit).2 $$ Hs
  iframe

/-- The slots after a page `fid` is lent out at a quarter. -/
def flRem (bs : List w8) (ps fid : Nat) (s : Nat) : Qp :=
  if fid ≤ s ∧ s < fid + pageSpan bs ps fid then halfQ.half else halfQ

open Iris.ProofMode in
/-- Page `fid` (the freelist page) of the slots, lent out at a quarter. -/
theorem open_flpage (d : Loc) (bs : List w8) (ps n fid : Nat) (hps : 16 ≤ ps)
    (hfit : n * ps ≤ bs.length) (hin : fid + pageSpan bs ps fid ≤ n) :
    slotsView (GF := GF) d bs ps (fun _ => halfQ) (List.range n) ⊣⊢
      slotsView d bs ps (flRem bs ps fid) (List.range n) ∗
        bytesPointsto (d +ₗ ((fid * ps : Nat) : Int)) (DFrac.own halfQ.half) (pageAt bs ps fid) := by
  have hov := pageOverflow_pageAt bs ps fid hps
  have hcov : ∀ s, coversSlot {[fid := pageAt bs ps fid]} s ↔ (fid ≤ s ∧ s < fid + pageSpan bs ps fid) := by
    intro s
    unfold coversSlot pageSpan
    constructor
    · rintro ⟨id, pg, hid, h1, h2⟩
      rw [GMap.lookup_singleton_Some] at hid
      obtain ⟨rfl, rfl⟩ := hid
      rw [hov] at h2; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fid, pageAt bs ps fid, by rw [GMap.lookup_singleton], h1, by rw [hov]; exact h2⟩
  refine (slots_carve (GF := GF) d bs ps (fun _ => halfQ) (flRem bs ps fid) halfQ.half n
    {[fid := pageAt bs ps fid]} hps hfit ?_ ?_ ?_ ?_).trans (sep_congr .rfl ?_)
  · intro id pg hid
    rw [GMap.lookup_singleton_Some] at hid
    obtain ⟨rfl, rfl⟩ := hid
    exact ⟨rfl, hin⟩
  · intro id1 pg1 id2 pg2 h1 h2 hne
    rw [GMap.lookup_singleton_Some] at h1 h2
    exact absurd (h1.1.symm.trans h2.1) hne
  · intro s _ hc
    unfold flRem; rw [if_pos ((hcov s).1 hc)]; exact (Qp.half_add_half _).symm
  · intro s _ hc
    unfold flRem; rw [if_neg (fun h => hc ((hcov s).2 h))]
  · unfold pagesView
    exact (BigSepM.bigSepM_singleton (M := GMap Nat)).trans .rfl

open Iris.ProofMode in
/-- The two metas, out of the slots (the database's half of the meta slots). -/
theorem open_metas (d : Loc) (bs : List w8) (ps n : Nat) (rem : Nat → Qp)
    (v0 v1 : internal.common.Meta) (hps : 80 ≤ ps) (hn : 2 ≤ n) (hfit : n * ps ≤ bs.length)
    (hdc : d.locCar ≠ 0) (hm0 : ((slotAt bs ps 0).drop 16).take 64 = metaBytes v0)
    (hm1 : ((slotAt bs ps 1).drop 16).take 64 = metaBytes v1)
    (hr0 : rem 0 = halfQ) (hr1 : rem 1 = halfQ) :
    slotsView (GF := GF) d bs ps rem (List.range n) ⊢
      (d +ₗ 16) ↦{DFrac.own halfQ} v0 ∗ (d +ₗ ((ps + 16 : Nat) : Int)) ↦{DFrac.own halfQ} v1 ∗
      ((d +ₗ 16) ↦{DFrac.own halfQ} v0 -∗ (d +ₗ ((ps + 16 : Nat) : Int)) ↦{DFrac.own halfQ} v1 -∗
        slotsView d bs ps rem (List.range n)) := by
  have Hr : List.range n = 0 :: 1 :: List.range' 2 (n - 2) := by
    have Hm : ∀ m, List.range (m + 2) = 0 :: 1 :: List.range' 2 m := fun m => by
      rw [List.range_eq_range']; rfl
    rw [← Hm, show n - 2 + 2 = n by omega]
  have hl0 : 80 ≤ (slotAt bs ps 0).length := by
    rw [slot_length _ _ _ (by have := Nat.mul_le_mul_right ps (show 1 ≤ n by omega); omega)]
    exact hps
  have hl1 : 80 ≤ (slotAt bs ps 1).length := by
    rw [slot_length _ _ _ (by have := Nat.mul_le_mul_right ps (show 2 ≤ n by omega); omega)]
    exact hps
  have hc1 : (d +ₗ ((1 * ps : Nat) : Int)).locCar ≠ 0 := by simpa [Loc.add] using hdc
  have hc0 : (d +ₗ ((0 * ps : Nat) : Int)).locCar ≠ 0 := by simpa [Loc.add] using hdc
  have ha0 : d +ₗ ((0 * ps : Nat) : Int) +ₗ 16 = d +ₗ 16 := by simp
  have ha1 : d +ₗ ((1 * ps : Nat) : Int) +ₗ 16 = d +ₗ ((ps + 16 : Nat) : Int) := by
    rw [loc_add_assoc]; congr 1; push_cast; omega
  unfold slotsView
  rw [Hr]
  iintro ⟨H0, H1, Hrest⟩
  rw [hr0, hr1]
  icases slot_meta_acc (hG := hG) _ _ _ v0 hc0 hl0 hm0 $$ H0 with ⟨Hm0, Hb0⟩
  icases slot_meta_acc (hG := hG) _ _ _ v1 hc1 hl1 hm1 $$ H1 with ⟨Hm1, Hb1⟩
  rw [ha0, ha1]
  iframe Hm0 Hm1
  iintro Hm0 Hm1
  ihave H0 := Hb0 $$ Hm0
  ihave H1 := Hb1 $$ Hm1
  iframe
  rw [hr0, hr1]
  iframe

end open_state

end bbolt
end EtcdGrove
end Perennial
