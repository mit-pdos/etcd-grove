/- Lean-first (no Rocq counterpart).

# The files of `Open`'s handle, out of its decoder (`WAL.Close.specOpening`; the W7-W12 log of
`notes/wal-fsext-plan.md`, eighth session)

`Close` of a handle `openAtIndex` made does not read the decoder: it syncs the tail and closes the
locks' files, and puts the program's halves of the segments back. All of them sit in the decoder's
streams (`walFileS`, through `ownDecoder_streams`); `walReadTie`'s per-file facts name them.

* `walTie_files`: the streams of the tie's files give the program's halves of the segments
  (`segRes`) and, per index, the file and its fd (`walTieFile`).
* `walOpening_lockedTok`: the ghost handle `walOpening` holds the lock token (`walHandleP`), which
  `Close` gives back (the inverse of `walInv_mintOpening`; the handle's ghost names stay behind).
* `walTie_locks`: with the locks' `fileutil.lockedFile` facts, the files are the locks' `walLockH`.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadDefs
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Inv
import all LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Ghost

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Fs WalEnc

section files
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [bufio_sem : _root_.Perennial.bufio.Assumptions]

/-- The `k`th file of the tie, open on the segment `g`: its `*os.File` and fd. -/
def walTieFile (dir : GoString) (flag : w64) (fls : List Loc) (k : Nat) (g : SegG) : IProp GF :=
  iprop(∃ fd : w64, os.ownFile (fls.getD k null) fd (child dir g.name) (DFrac.own 1) ∗
    osFd fd (DFrac.own 1) (openFd g.ino flag))

/-- The `k`th file, any name and fd state (what a lock's `Close` needs). -/
def walFileAt (fls : List Loc) (k : Nat) : IProp GF :=
  iprop(∃ (fd : w64) (nm : GoString) (d : OsFd), os.ownFile (fls.getD k null) fd nm (DFrac.own 1) ∗
    osFd fd (DFrac.own 1) d)

theorem walTieFile_at (dir : GoString) (flag : w64) (fls : List Loc) (k : Nat) (g : SegG) :
    walTieFile (GF := GF) dir flag fls k g ⊢ walFileAt fls k := by
  unfold walTieFile walFileAt
  iintro ⟨%fd, Hf, Hfd⟩
  iexists fd, _, _
  iframe

/-- See the file header. -/
theorem walTie_files (dir : GoString) (flag : w64) :
    ∀ (gs : List SegG) (fs : List (DecFile GF)) (fls : List Loc),
    fs.length = gs.length → fls.length = gs.length →
    (∀ (k : Nat) (F : DecFile GF) (g : SegG), fs[k]? = some F → gs[k]? = some g →
      ∃ (f : Loc) (fd : w64), fls[k]? = some f ∧ F.S = walFileS f fd (child dir g.name) (openFd g.ino flag) g) →
    ([∗list] F ∈ fs, ∃ r, F.S r) ⊢
      ([∗list] g ∈ gs, segRes (L := hG.goose_localGS) g) ∗
      [∗list] k ↦ g ∈ gs, walTieFile dir flag fls k g
  | [], [], _, _, _, _ => by
    iintro -
    isplitl
    · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
    · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
  | g :: gs, F :: fs, f0 :: fls, hl1, hl2, hk => by
    obtain ⟨f, fd, hf, hS⟩ := hk 0 F g rfl rfl
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hf
    subst hf
    have e : ∀ (k : Nat) (g' : SegG), walTieFile (GF := GF) dir flag (f0 :: fls) (k + 1) g' =
        walTieFile dir flag fls k g' := by
      intro k g'; simp [walTieFile]
    have ih := walTie_files dir flag gs fs fls (by simpa using hl1) (by simpa using hl2)
      (fun k F' g' h1 h2 => hk (k + 1) F' g' h1 h2)
    iintro H
    icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ H with ⟨⟨%r, Hs⟩, H⟩
    rw [hS]
    unfold walFileS
    icases Hs with ⟨-, Hf, Hfd, -, Hm, Hb⟩
    icases ih $$ H with ⟨Hsg, Hfs⟩
    isplitl [Hm Hb Hsg]
    · iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
      iframe Hsg
      unfold segRes; iframe
    · iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
      simp only [e]
      iframe Hfs
      unfold walTieFile
      iexists fd
      iframe
  | [], _ :: _, _, hl1, _, _ => by simp at hl1
  | _ :: _, [], _, hl1, _, _ => by simp at hl1
  | _ :: _, _ :: _, [], _, hl2, _ => by simp at hl2

/-- See the file header. -/
theorem walTie_locks :
    ∀ (gs : List SegG) (lfs fls : List Loc), lfs.length = gs.length →
    ([∗list] k ↦ _g ∈ gs, walFileAt (GF := GF) fls k) ∗
      ([∗list] k ↦ lf ∈ lfs, fileutil.lockedFile lf (fls.getD k null)) ⊢
      [∗list] lf ∈ lfs, walLockH lf
  | [], [], _, _ => by
    iintro -
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
  | _ :: gs, lf :: lfs, fls, hl => by
    have ih := walTie_locks gs lfs fls.tail (by simpa using hl)
    iintro ⟨Hf, Hl⟩
    icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ Hf with ⟨Hf0, Hf⟩
    icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ Hl with ⟨#Hl0, Hl⟩
    have e1 : ∀ k, fls.getD (k + 1) null = fls.tail.getD k null := by
      intro k; cases fls <;> simp
    have e2 : ∀ k, walFileAt (GF := GF) fls (k + 1) = walFileAt fls.tail k := by
      intro k; simp only [walFileAt, e1]
    simp only [e1, e2]
    iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
    isplitl [Hf0]
    · unfold walFileAt walLockH
      icases Hf0 with ⟨%fd, %nm, %d, Hf0, Hfd0⟩
      iexists fls.getD 0 null, fd, nm, d
      iframe
      iexact Hl0
    · iapply ih
      iframe
  | [], _ :: _, _, hl => by simp at hl
  | _ :: _, [], _, hl => by simp at hl

/-- See the file header. -/
theorem walOpening_lockedTok (w : Loc) (dir : GoString) (s : w64 × w64) :
    walOpening (W := W) w dir s ⊢ walLockedTok (W := W) := by
  unfold walOpening walHandleP
  iintro ⟨%γ, -, -, -, Hl⟩
  iexact Hl

end files

end WalFs
end EtcdGrove
end Perennial

end
