/- Lean-first (no Rocq counterpart).

# Putting a segment back by its inode (`notes/wal-fsext-plan.md`, W3/W5 log, tenth session)

A holder of what is out puts a segment back at a later step than it took it (`openAtIndex`'s error arms, a
failed `ReadAll`, `Close`), when the layouts may be others (`Ls`): `walParked_putSeg` needs the very
segment among `segsAll Ls`, but the program's halves (`segResP`) depend only on the segment's inode and
length. So the segment goes back by its inode: onto the segment of `Ls` with that inode, whose length is
the held one's (`walParked_putSegIno`'s `hlen`), or, if no segment of `Ls` has it, the halves are dropped
(the record forgets the inode either way).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Parked

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section parked
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- The program's halves depend only on the inode and the length. -/
theorem segResP_congr (g g' : SegG) (hi : g'.ino = g.ino) (hl : g'.bs.length = g.bs.length) :
    segResP (L := L) g ⊢ segResP (L := L) g' := by
  unfold segResP
  iintro ⟨%m, %bs, Hm, Hb, %h⟩
  iexists m, bs
  rw [hi]
  iframe Hm Hb
  ipureintro; rw [hl]; exact h

/-- An inode no segment has, forgotten from `O`. -/
theorem segsP_forget (S : List SegG) (O : List Ino) (i : Ino) (hS : ∀ x ∈ S, x.ino ≠ i) :
    ([∗list] x ∈ S, if x.ino ∈ O then emp else segResP (L := L) x) ⊢
      [∗list] x ∈ S, if x.ino ∈ O.filter (· ≠ i) then emp else segResP (L := L) x := by
  iapply BigSepL.bigSepL_mono (fun {k x} hk => segP_congr (L := L) x ?_)
  have hx := hS x (List.mem_of_getElem? hk)
  simp [hx]

/-- **A segment put back by its inode** (see the file header): no change in flight on it, the layouts'
inodes distinct, every segment of `Ls` with its inode of its length. -/
theorem walParked_putSegIno (Ls : GMap GoString WalLay) (cl : List Claim) (F : GMap Ino SegFl)
    (o : WalOut) (g : SegG) (hnd : ((segsAll Ls).map (·.ino)).Nodup) (hF : F !! g.ino = none)
    (hlen : ∀ g' ∈ segsAll Ls, g'.ino = g.ino → g'.bs.length = g.bs.length) :
    ⊢ walParked (L := L) (W := W) Ls cl F -∗ walOutFrag (W := W) o -∗ segResP (L := L) g ==∗
      walParked (L := L) (W := W) Ls cl F ∗ walOutFrag (W := W) (o.delSeg g.ino) := by
  by_cases hex : ∃ g' ∈ segsAll Ls, g'.ino = g.ino
  · obtain ⟨g', hg', hi⟩ := hex
    iintro Hp Ho Hg
    ihave Hg := segResP_congr (L := L) g g' hi (hlen g' hg' hi) $$ Hg
    rw [← hi] at hF ⊢
    iapply walParked_putSeg (L := L) (W := W) Ls cl F o g' hg' hnd hF $$ Hp Ho Hg
  · have hS : ∀ x ∈ segsAll Ls, x.ino ≠ g.ino := fun x hx e => hex ⟨x, hx, e⟩
    unfold walParked
    iintro ⟨%b, %o', Hpa, Hoa, %hp, Hs, Hc, Ht, Hw⟩ Ho -
    icases walOut_agree (W := W) o' o $$ Hoa Ho with %ho
    subst ho
    imod walOut_set (W := W) o' o' (o'.delSeg g.ino) $$ Hoa Ho with ⟨Hoa, Ho⟩
    ihave Hs := segsP_forget (L := L) (segsAll Ls) o'.O g.ino hS $$ Hs
    imodintro
    iframe Ho
    iexists b, o'.delSeg g.ino
    dsimp only [WalOut.delSeg]
    iframe Hpa Hoa Hs Hc Ht Hw
    ipureintro
    intro i hi
    have hne : i ≠ g.ino := by rintro rfl; exact hi hF
    simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨hp i hi, hne⟩

end parked

end WalFs
end EtcdGrove
end Perennial

end
