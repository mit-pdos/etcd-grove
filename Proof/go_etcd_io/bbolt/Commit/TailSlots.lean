/-
`Commit`'s written slots between `tx.write()` and `tx.writeMeta()` (U10k of
`notes/bbolt-proof-plan.md`): the dirty pages' slots `SB`, written (`slotsOwn`), split into the
slots the commit publishes `S` (the new tree's slots that were no store slots) and the rest `R`
(the new freelist page's, pages freed again), which go back into the writer's `W` slots
(`cm_slots_split`); after a failed meta write, `S` goes back too (`cm_slots_back`).
-/
module

public import Proof.go_etcd_io.bbolt.Commit.TailAcc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section slots
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]


omit sem in
/-- Written slots (whole pages) are write targets again. -/
theorem slotsOwn_wrSlots (b : Loc) (l : Nat) (p : GoString) (S : List Nat) (bs : Nat → List w8)
    (hlen : ∀ s ∈ S, (bs s).length = 4096) :
    slotsOwn (GF := GF) (some (b, l)) p S bs ⊢ wrSlots b p S bs := by
  unfold slotsOwn wrSlots
  apply BigSepL.bigSepL_mono
  intro k s hs
  have h := hlen s (List.mem_of_getElem? hs)
  iintro ⟨Hb, Ho⟩
  iframe Ho
  ihave Hc := bytes_cellsR (GF := GF) b (bs s) (4096 * s) $$ Hb
  rw [h]
  iexists _; iexact Hc


omit go_gctx sem in
/-- The written slots split by a predicate. -/
theorem slotsOwn_filter (ms : MapSt) (p : GoString) (L : List Nat) (bs : Nat → List w8)
    (P : Nat → Bool) :
    slotsOwn (GF := GF) ms p L bs ⊢
      slotsOwn ms p (L.filter P) bs ∗ slotsOwn ms p (L.filter (fun s => !P s)) bs := by
  unfold slotsOwn
  exact (BigSepL.bigSepL_perm (List.filter_append_perm P L).symm).1.trans BigSepL.bigSepL_append.1

/-- **The written slots split** (see the file header): of the dirty pages' slots `SB`, those
satisfying `P` stay written (`S`), the rest go back into the writer's `W` slots `W'` with their
written bytes. -/
theorem cm_slots_split (B : BNs) (db : Loc) (p : GoString) (sp : Loc) (t0 : Nat) (tx : Loc)
    (ws : WSt) (w : WDb) (b : Loc) (l : Nat) (SB : List Nat) (bs : Nat → List w8)
    (P : Nat → Bool) (hms : w.ms = some (b, l)) (hdisj : ∀ s ∈ w.W, s ∉ SB)
    (hin : ∀ s ∈ SB, 4096 * (s + 1) ≤ l ∧ 4096 * (s + 1) ≤ w.m.size)
    (hlen : ∀ s ∈ SB, (bs s).length = 4096) :
    wdbLive (GF := GF) B db p sp t0 tx ws w ∗ slotsOwn (some (b, l)) p SB bs ⊢
      wdbLive B db p sp t0 tx ws
        (w.reslot w.m (SB.filter (fun s => !P s) ++ w.W)
          (wbUpd (SB.filter (fun s => !P s)) bs w.wb)) ∗
      slotsOwn (some (b, l)) p (SB.filter P) bs := by
  iintro ⟨Hd, HS⟩
  icases slotsOwn_filter (some (b, l)) p SB bs P $$ HS with ⟨HS, HR⟩
  iframe HS
  ihave HR := slotsOwn_wrSlots b l p _ bs
    (fun s hs => hlen s (List.mem_filter.1 hs).1) $$ HR
  icases cm_file_acc B db p sp t0 tx ws w $$ Hd with ⟨Hfile, Hwa, Hfo, Hfd, Hom, Hwc, Hwbs, Hback⟩
  rw [hms]
  icases wSlots_return b l p w.W (SB.filter (fun s => !P s)) w.wb bs w.m.size
    (fun s hs hR => hdisj s hs (List.mem_filter.1 hR).1)
    (fun s hs => hin s (List.mem_filter.1 hs).1) $$ [HR Hwc Hwbs] with ⟨Hwc, Hwbs⟩
  · iframe
  iapply Hback $$ %w.m %_ %_ Hfile Hwa Hfo Hfd Hom [Hwc] Hwbs
  iexact Hwc

/-- **The written slots back** (after a failed meta write): `S` into the writer's `W` slots. -/
theorem cm_slots_back (B : BNs) (db : Loc) (p : GoString) (sp : Loc) (t0 : Nat) (tx : Loc)
    (ws : WSt) (w : WDb) (b : Loc) (l : Nat) (S : List Nat) (bs : Nat → List w8)
    (hms : w.ms = some (b, l)) (hdisj : ∀ s ∈ w.W, s ∉ S)
    (hin : ∀ s ∈ S, 4096 * (s + 1) ≤ l ∧ 4096 * (s + 1) ≤ w.m.size)
    (hlen : ∀ s ∈ S, (bs s).length = 4096) :
    wdbLive (GF := GF) B db p sp t0 tx ws w ∗ slotsOwn (some (b, l)) p S bs ⊢
      wdbLive B db p sp t0 tx ws (w.reslot w.m (S ++ w.W) (wbUpd S bs w.wb)) := by
  iintro ⟨Hd, HS⟩
  ihave HS := slotsOwn_wrSlots b l p S bs hlen $$ HS
  icases cm_file_acc B db p sp t0 tx ws w $$ Hd with ⟨Hfile, Hwa, Hfo, Hfd, Hom, Hwc, Hwbs, Hback⟩
  rw [hms]
  icases wSlots_return b l p w.W S w.wb bs w.m.size hdisj hin $$ [HS Hwc Hwbs] with ⟨Hwc, Hwbs⟩
  · iframe
  iapply Hback $$ %w.m %_ %_ Hfile Hwa Hfo Hfd Hom [Hwc] Hwbs
  iexact Hwc

end slots

end bbolt
end EtcdGrove
end Perennial
