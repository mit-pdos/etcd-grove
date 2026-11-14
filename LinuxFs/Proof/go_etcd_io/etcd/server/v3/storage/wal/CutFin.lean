/- Lean-first (no Rocq counterpart).

# `cut`'s last steps (W2, `notes/wal-fsext-plan.md`, "W2 implementation log", tenth session)

* `walInv_cutSynced`: step 7's update (`walInvBody_cutSynced`, `CutSync.lean`) as an update of the
  invariant, with the generation's `notCrashed` (`walInv_step`; the program takes it at a step,
  `wp_notCrashed_acc`).
* The new handle's pure facts (step 8): the directory's largest `.wal` name after the rename
  (`cutDir_largest`), the out-record after the commit (`walOut_cut`), the encoder's split of a fresh
  tail (`WalHS.split_fresh`), the tail's `TailMeta` after its fdatasync (`tailMeta_synced`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CutSync
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateSteps

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- **The largest `.wal` name after the rename**: `bt`, above the old largest `nm0`. -/
theorem cutDir_largest {c : Ents} {nm0 bt : GoString} (i : Ino)
    (hl : ∀ b n, c !! b = some n → walNameP b = true → b = nm0 ∨ go.GoStringLt b nm0)
    (hlt : go.GoStringLt nm0 bt) :
    ∀ b n, (<[bt := Node.file i]> c) !! b = some n → walNameP b = true →
      b = bt ∨ go.GoStringLt b bt := by
  intro b n hb hw
  by_cases he : bt = b
  · exact Or.inl he.symm
  · rw [GMap.lookup_insert_ne _ _ he] at hb
    rcases hl b n hb hw with h | h
    · subst h; exact Or.inr hlt
    · exact Or.inr (go.goStringLt_trans h hlt)

/-- **The out-record after the cut's commit**: the old tail put back, the new segment out. -/
theorem walOut_cut (i0 i : Ino) (D : List (Ino × NameSet)) (T : List GoString) :
    ((⟨[i0], D, T⟩ : WalOut).delSeg i0).addSeg i = ⟨[i], D, T⟩ := by
  simp [WalOut.delSeg, WalOut.addSeg]

/-- **A fresh tail's split** (every record encoded, the encoder started at the stream's end). -/
theorem WalHS.split_fresh (Mr : WalMarshal) (h : WalHS) (hr : h.rest = 0)
    (ho : h.o0 = (tailStream Mr h.H h.md h.cuts).length) (hout : h.out = []) (hp : h.pend = []) :
    h.Split Mr := by
  unfold WalHS.Split WalHS.encRecs
  rw [hr, Nat.sub_zero, List.take_length, ← tailStream_recs, ho, hout, hp]
  simp

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **The tail's `TailMeta` after its fdatasync**: all its bytes, no mappings. -/
theorem tailMeta_synced (m : OsMeta) (bs : List ByteG) (hl : bs.length = m.size)
    (hmaps : m.maps = ∅) (hB : pageEnd m.size ≤ max m.size m.cz) : TailMeta m.synced bs :=
  ⟨hl, hmaps, TailZ.synced_of hB, rfl, rfl⟩

/-- **Step 7 of `cut`** (`walInvBody_cutSynced`) as an update of the invariant, at a program step
(the generation's `notCrashed`, handed back). -/
theorem walInv_cutSynced (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir : GoString) (j : Ino) (X : List GoString) (hj : NamesH) (x : Nat)
    (e : LogEntry) (c : Ents) (bt : GoString) (i : Ino) (dq : DFrac) (γ : GName) (tg : TailG)
    (n : Nat) (hx : x < n) (hw : e.op.Writes j bt) (hwal : walNameP bt = true)
    (hc : c !! bt = some (.file i)) (hti : tg.2.2.2.2.1 = i) :
    ⊢ walInv (L := L) (W := W) walCodec Mr R jr r -∗ notCrashed (hC := L.goose_crashGS) -∗
      walDirKey (W := W) dir j X -∗ osNames (L := L) j (.except X) dq (hj.log x e c) -∗
      walTailKey (W := W) dir γ -∗ tailVar (W := W) γ tg -∗ walCutFrag (W := W) (some dir) -∗
      osCommitLb (L := L) n ={⊤}=∗
      notCrashed (hC := L.goose_crashGS) ∗ osNames (L := L) j (.except X) dq (hj.log x e c) ∗
        walTailKey (W := W) dir γ ∗ tailVar (W := W) γ tg ∗ walCutFrag (W := W) none := by
  iintro #Hinv Hnc #Hkey Hq Hk Hv Hcf #Hc
  iapply walInv_step walCodec Mr R jr r
    iprop(walDirKey (W := W) dir j X ∗ osCommitLb (L := L) n ∗
      osNames (L := L) j (.except X) dq (hj.log x e c) ∗ walTailKey (W := W) dir γ ∗
      tailVar (W := W) γ tg ∗ walCutFrag (W := W) (some dir))
    iprop(osNames (L := L) j (.except X) dq (hj.log x e c) ∗ walTailKey (W := W) dir γ ∗
      tailVar (W := W) γ tg ∗ walCutFrag (W := W) none)
    ⊤ (fun _ _ => CoPset.mem_full) (fun s => by
      iintro Hb ⟨#Hkey, #Hc, Hq, Hk, Hv, Hcf⟩
      imod walInvBody_cutSynced walCodec Mr R jr r s dir j X hj x e c bt i dq γ tg n hx hw hwal hc hti
        $$ Hb Hkey Hq Hk Hv Hcf Hc with ⟨Hb, Hq, Hk, Hv, Hcf⟩
      imodintro
      iframe) $$ Hinv Hnc [Hq Hk Hv Hcf]
  iframe; iframe #

end iris

end WalFs
end EtcdGrove
end Perennial

end
