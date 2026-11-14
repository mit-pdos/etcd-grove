/- Lean-first (no Rocq counterpart).

# A segment the program creates is none of the invariant's (W4, the inode-clash gap)

`Create`'s commit at the rename (and `cut`'s) adds a segment the program created to the invariant's
layouts, which must keep the segments' inodes distinct (`WalsOk`'s `Nodup`). The program holds the
new file's `OsMeta` and bytes wholly; the invariant holds, of every segment, half of its `OsMeta`
(idle) or, with a write in flight (whose token holds the `OsMeta` whole), half of the bytes before
the write, byte 0 among them (`SegFl.Ok`: the write is past the header, `0 < fl.off`). So the new
file's inode is none of theirs (`laysResF_ino_ne`), with no fact of the file system's inode
allocator (which its shared mode does not expose: a created inode is `st.fs.nextIno`, a fresh key of
the `OsMeta` map, and no fragment of it reaches a client).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Inv

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- A write in flight leaves byte 0 to the halves before it. -/
theorem segFl_take_cons {fl : SegFl} {g : SegG} (h : fl.Ok g) :
    ∃ y ys, fl.bs.take (cfLo fl.m fl.off) = y :: ys := by
  obtain ⟨hin, hd, hlen, -, -, -, hpos⟩ := h
  have hlo : cfLo fl.m fl.off = fl.off := by unfold cfLo; omega
  rw [hlo]
  have hdl : 0 < fl.data.length := List.length_pos_iff.2 hd
  cases hb : fl.bs with
  | nil => rw [hb] at hlen; simp at hlen; omega
  | cons y ys =>
    obtain ⟨k, hk⟩ : ∃ k, fl.off = k + 1 := ⟨fl.off - 1, by omega⟩
    rw [hk]
    exact ⟨y, ys.take k, rfl⟩

/-- A resize in flight leaves byte 0 to the halves below it (I3b). -/
theorem segFlR_take_cons {fl : SegFl} {tr : Bool} {tg : Nat} {g : SegG} (h : fl.OkR tr tg g) :
    ∃ y ys, fl.bs.take (min fl.m.size tg) = y :: ys := by
  obtain ⟨hlen, -, -, -, hpos⟩ := h
  cases hb : fl.bs with
  | nil => rw [hb] at hlen; simp at hlen; omega
  | cons y ys =>
    obtain ⟨k, hk⟩ : ∃ k, min fl.m.size tg = k + 1 := ⟨min fl.m.size tg - 1, by omega⟩
    rw [hk]
    exact ⟨y, ys.take k, rfl⟩

/-- **The invariant's part of a segment excludes the program's whole file of the same inode** (its
`OsMeta` and byte 0, both whole). -/
theorem segResF_ino_ne (F : GMap Ino SegFl) (g : SegG) (m : OsMeta) (x : ByteG) (xs : List ByteG) :
    ⊢ segResF (L := L) F g -∗ osMeta (L := L) g.ino (DFrac.own 1) m -∗
      osBytes (L := L) g.ino 0 (DFrac.own 1) (x :: xs) -∗ False := by
  iintro Hs Hm Hb
  unfold segResF
  split
  · unfold segRes
    icases Hs with ⟨Hm', -⟩
    unfold osMeta
    icases gElem_valid_2 _ _ _ _ _ _ _ $$ Hm Hm' with %Hv
    exact absurd (DFrac.valid_own_op Hv.1) (by simp)
  · rename_i fl _
    split
    · icases Hs with ⟨-, Hb0, -, %Hok⟩
      obtain ⟨y, ys, hy⟩ := segFl_take_cons Hok
      rw [hy]
      unfold osBytes
      icases (bytesG_cons _ _ _ _ _ _).1 $$ Hb with ⟨Hx, -⟩
      icases (bytesG_cons _ _ _ _ _ _).1 $$ Hb0 with ⟨Hy, -⟩
      icases gElem_valid_2 _ _ _ _ _ _ _ $$ Hx Hy with %Hv
      exact absurd (DFrac.valid_own_op Hv.1) (by simp)
    · rename_i tg _
      icases Hs with ⟨-, Hb0, %Hok⟩
      obtain ⟨y, ys, hy⟩ := segFlR_take_cons Hok
      rw [hy]
      unfold osBytes
      icases (bytesG_cons _ _ _ _ _ _).1 $$ Hb with ⟨Hx, -⟩
      icases (bytesG_cons _ _ _ _ _ _).1 $$ Hb0 with ⟨Hy, -⟩
      icases gElem_valid_2 _ _ _ _ _ _ _ $$ Hx Hy with %Hv
      exact absurd (DFrac.valid_own_op Hv.1) (by simp)

/-- **A file the program holds wholly (its `OsMeta`, byte 0) is no segment of the invariant's
layouts.** -/
theorem laysResF_ino_ne (F : GMap Ino SegFl) (Ls : GMap GoString WalLay) (i : Ino) (m : OsMeta)
    (x : ByteG) (xs : List ByteG) :
    ⊢ laysResF (L := L) F Ls -∗ osMeta (L := L) i (DFrac.own 1) m -∗
      osBytes (L := L) i 0 (DFrac.own 1) (x :: xs) -∗
      ⌜∀ g ∈ segsAll Ls, g.ino ≠ i⌝ ∗ laysResF (L := L) F Ls ∗ osMeta (L := L) i (DFrac.own 1) m ∗
        osBytes (L := L) i 0 (DFrac.own 1) (x :: xs) := by
  iintro Hl Hm Hb
  by_cases hc : ∀ g ∈ segsAll Ls, g.ino ≠ i
  · iframe Hl Hm Hb
    ipureintro; exact hc
  · iexfalso
    obtain ⟨g, hg, hgi⟩ : ∃ g ∈ segsAll Ls, g.ino = i := by
      exact Classical.byContradiction fun hn => hc fun g hg hgi => hn ⟨g, hg, hgi⟩
    unfold laysResF
    icases (BigSepL.bigSepL_mem_acc hg) $$ Hl with ⟨Hs, -⟩
    subst hgi
    iapply segResF_ino_ne F g m x xs $$ Hs Hm Hb

end iris

end WalFs
end EtcdGrove
end Perennial

end
