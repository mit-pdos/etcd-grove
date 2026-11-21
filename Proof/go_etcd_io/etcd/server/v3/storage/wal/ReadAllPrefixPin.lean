/- The fallback opens one earlier, closed WAL segment at a time. The existing
reader retains its selected suffix and its registration on the active tail. -/
module
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenPinTake
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ParkedPut

@[expose] public section
noncomputable section
namespace Perennial.EtcdGrove.WalFs
open Iris Iris.BI Iris.ProofMode Fs WalEnc

variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- The selected suffix and a candidate in its strict prefix have distinct
inodes because the layout names every segment exactly once. -/
theorem prefix_ino_not_selected (gs : List SegG) (k i : Nat) (g : SegG)
    (hnd : (gs.map (·.ino)).Nodup) (hi : i < k) (hg : gs[i]? = some g) :
    g.ino ∉ (gs.drop k).map (·.ino) := by
  rw [List.map_drop]
  have hin : g.ino ∈ (gs.map (·.ino)).take k := by
    apply List.mem_of_getElem?
    rw [List.getElem?_take_of_lt hi, List.getElem?_map, hg]; rfl
  conv at hnd => arg 1; rw [← List.take_append_drop k (gs.map (·.ino))]
  intro hout
  exact (List.nodup_append.1 hnd).2.2 _ hin _ hout rfl

/-- Reserve the exact original bytes and metadata while the probe opens and
decodes this segment. Only its inode is added to the reader's outstanding set. -/
theorem readAll_takeProbe (Ls : GMap GoString WalLay) (cl : List Claim) (F : GMap Ino SegFl)
    (o : WalOut) (g : SegG) (hg : g ∈ segsAll Ls) (ho : g.ino ∉ o.O) :
    ⊢ walParked (L := L) (W := W) Ls cl F -∗ laysResF (L := L) F Ls -∗ walOutFrag (W := W) o ==∗
      walParked (L := L) (W := W) Ls cl F ∗ laysResF (L := L) F Ls ∗
      walOutFrag (W := W) (o.addSeg g.ino) ∗ segRes (L := L) g ∗ ⌜F !! g.ino = none⌝ := by
  iintro Hp Hl Ho
  imod walParked_takeSeg (L := L) Ls cl F o g hg ho $$ Hp Ho with ⟨Hp, Ho, Hprog, %hf⟩
  iunfold laysResF at Hl
  icases BigSepL.bigSepL_mem_acc (Φ := fun x => segResF (L := L) F x) hg $$ Hl with ⟨Hgs, Hback⟩
  have he : segResF (L := L) F g = segRes (L := L) g := by simp [segResF, hf]
  ihave Hgs : segRes (L := L) g $$ [Hgs]
  · rw [← he]; iexact Hgs
  icases segRes_exact (L := L) g $$ [Hgs Hprog] with ⟨Hgs, Hprog⟩
  · iframe Hgs Hprog
  imodintro; iframe Hp Ho Hprog
  isplitl [Hgs Hback]
  · unfold laysResF; iapply Hback; rw [he]; iexact Hgs
  · ipureintro; exact hf

/-- The deferred close returns the borrowed segment and restores the outstanding
set the caller had before looking at that file. -/
theorem readAll_putProbe (Ls : GMap GoString WalLay) (cl : List Claim) (F : GMap Ino SegFl)
    (o : WalOut) (g : SegG) (hg : g ∈ segsAll Ls) (ho : g.ino ∉ o.O)
    (hnd : ((segsAll Ls).map (·.ino)).Nodup) (hf : F !! g.ino = none) :
    ⊢ walParked (L := L) (W := W) Ls cl F -∗ walOutFrag (W := W) (o.addSeg g.ino) -∗
      segRes (L := L) g ==∗ walParked (L := L) (W := W) Ls cl F ∗ walOutFrag (W := W) o := by
  iintro Hp Ho Hg
  ihave Hprog := segRes_segResP (L := L) g $$ Hg
  imod walParked_putSeg (L := L) Ls cl F _ g hg hnd hf $$ Hp Ho Hprog with ⟨Hp, Ho⟩
  imodintro; iframe Hp
  have he : (o.addSeg g.ino).delSeg g.ino = o := by
    cases o with
    | mk O D T =>
      simp only [WalOut.addSeg, WalOut.delSeg, List.filter_cons, ne_eq, not_true_eq_false,
        decide_false, Bool.false_eq_true, ↓reduceIte, WalOut.mk.injEq, and_self, and_true]
      apply List.filter_eq_self.2
      intro i hi
      simp only [decide_eq_true_eq]
      exact fun e => ho (e ▸ hi)
  iapply walOutFrag_eq' (W := W) o $$ Ho
  ipureintro; first | exact he | exact he.symm

end Perennial.EtcdGrove.WalFs
