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
  m.freelist' ≠ W64 18446744073709551615 ∧ fid + pageSpan bs ps fid ≤ bs.length / ps ∧
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
  obtain ⟨cwf, cdisj, cin, cfree, cfl, cfid, cfpg, cids, ctx⟩ := hc
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

end open_state

end bbolt
end EtcdGrove
end Perennial
