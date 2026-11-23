/-
The proofs of `examples/osfs/walfs`'s `seglog.go` (one generation), part 2, over the file
extension v2: `lockFile`, `Segment`, `ZeroToEnd`, `readFull`, `Reread` and the driver `Run`, over
the specs of the calls they make (hypotheses) and `SegLogOps.lean`'s.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs.SegLogOps
public import Spec.os.File__Truncate
public import Proof.golang_org.x.sys.unix.FileOps
public import Spec.os.File__Fd
public import Spec.os.File__Close
public import Spec.syscall.Fdatasync

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_walfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs DSBase
  github_com.mit_pdos.etcd_grove.examples.osfs.walfs

section prog
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [go.BasicIntoValInj]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.walfs.Assumptions]
variable [os.Assumptions] [os.file.FieldAssumptions] [golang_org.x.sys.unix.Assumptions]

/-- `lockFile(f)`: an OFD write lock on the whole file, without waiting (`unix.FcntlFlock`'s
`F_OFD_SETLK`), on a writable fd with no OFD lock: on success the fd holds it, with its token; on an
error nothing changed. -/
theorem wp_lockFile (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (d : OsFd) (hfree : d.ofd = none)
    (hw : d.writable = true) :
    {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ osFd (GF := GF) fd (DFrac.own 1) d }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.lockFile)) (Val #f))
    {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗
        ((⌜err = interface.nil⌝ ∗ osFd fd (DFrac.own 1) (d.setLk .ofd (some true)) ∗
            osLock (GF := GF) .ofd d.ino fd) ∨
         (⌜err ≠ interface.nil⌝ ∗ osFd fd (DFrac.own 1) d)) }} := by
  wp_start as ⟨#Hinv, Hf, Hfd⟩
  wp_auto
  wp_apply wp_Fd f fd name dqf $$ Hf as Hf
  ihave Ht := lockTok_none (GF := GF) .ofd fd d (by simp [OsFd.lk, hfree])
  wp_apply golang_org.x.sys.unix.FcntlFlock.wp_lock fd (W64 37) lk_ptr
    { Type' := W16 1, Whence' := W16 0, Start' := W64 0, Len' := W64 0, Pid' := 0,
      «_#5'» := zeroValDef } d (some true) (.inl rfl)
    rfl rfl rfl rfl rfl (fun _ => hw) (fun h => by cases h) (fun _ => hfree)
    $$ [Hinv lk Hfd Ht] as %e ⟨-, Hout⟩
  · iframe; isplitl []; iexact Hinv; iexact Ht
  unfold lockOut
  icases Hout with ⟨%d', Hfd, Ht, %hd⟩
  obtain ⟨-, h2, h3⟩ := hd
  by_cases he : e = 0
  · subst he
    have hd' := h2 rfl; subst hd'
    rw [show errnoErr 0 = interface.nil from if_pos rfl]
    iapply HΦ
    iframe Hf
    ileft
    iframe Hfd
    isplitr
    · ipureintro; rfl
    ihave Ht := (lockTok_some (GF := GF) .ofd fd _ (by cases d; rfl)).1 $$ Ht
    rw [setLk_ino]
    iexact Ht
  · have hd' := h3 (by simp) he; subst hd'
    rw [show errnoErr e = interface.mkOk syscall.Errno.ty #e from if_neg he]
    iapply HΦ
    iframe Hf
    iright
    iframe Hfd
    ipureintro; intro h; cases h

/-- The tokens of a description holding an exclusive OFD lock and no `flock` lock. -/
theorem seg_lockToks (i : Ino) (rd wr : Bool) (fd : w64) :
    osLock (GF := GF) .ofd i fd ⊢ lockToks (GF := GF) fd ⟨i, rd, wr, some true, none⟩ := by
  iintro H
  unfold lockToks
  isplitl [H]
  · iapply (lockTok_some (GF := GF) .ofd fd _ rfl).2; iexact H
  · iapply lockTok_none; simp [OsFd.lk]

/-- The segment's file after `Segment`: no mapping, `segSize` bytes, all of them held. -/
def segFile (i : Ino) : IProp GF :=
  iprop(∃ (m : OsMeta) (bs : List ByteG), ⌜m.maps = ∅ ∧ m.size = 0x10000 ∧ bs.length = 0x10000⌝ ∗
    osMeta (GF := GF) i (DFrac.own 1) m ∗ osBytes (GF := GF) i 0 (DFrac.own 1) bs)

/-- `Segment(dir/seg.log, rec)`, `dir` the root of inode `j`, `seg.log` absent, `rec` the 8 bytes
of data: on success `seg.log` names a new file of a fresh inode `i`, `segSize` long, and the offset
past `rec` is returned. -/
theorem wp_Segment (wp_CreateS : os.OpenFile.specCreateS (GF := GF) (hG := hG))
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (wp_WriteAt : os.File.WriteAt.spec (GF := GF) (hG := hG))
    (wp_Fdatasync : syscall.Fdatasync.spec (GF := GF) (hG := hG))
    (R : Roots) (dir : GoString) (j : Ino) (hrj : (dir, j) ∈ R)
    (h : NamesH) (hn : h.cur !! logB = none) (sl : GoSlice) (dqs : DFrac) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ logRes (GF := GF) R dir j h ∗ sl ↦*{dqs} dataC }}
      (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.Segment))
        (Val #(child dir logB))) (Val #sl))
    {{ (e : w64) (err : GoInterface), RET (PairV #e #err);
        ∃ V' : NamesH, logRes (GF := GF) R dir j V' ∗
        ((⌜err = interface.nil ∧ e = W64 8⌝ ∗ ∃ i, ⌜V'.cur !! logB = some (.file i)⌝ ∗
            segFile i) ∨
         ⌜err ≠ interface.nil⌝) }} := by
  wp_start as ⟨#Hos, #Hsi, Hh, Hsl⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  rw [show (W64 2 ||| W64 64) = W64 66 from by decide]
  wp_apply wp_openLog wp_CreateS R dir j hrj h hn (W32 384) $$ [Hos Hsi Hh] as %f %err Hr
  · iframe; iframe #
  icases Hr with (⟨%fd, %i, %V', %hek, Hf, Ho, Hfd, Hm, Hh⟩ | ⟨%herr, %V', Hh⟩)
  rotate_left
  · cases err with
    | nil => exact absurd rfl herr
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    iexists V'
    iframe Hh
    iright; ipureintro; intro h; cases h
  obtain ⟨rfl, hfd0, hk⟩ := hek
  have hclose : ∀ (e : GoInterface), e ≠ interface.nil →
      ⊢ (∀ e' err', (∃ V2 : NamesH, logRes (GF := GF) R dir j V2 ∗
          ((⌜err' = interface.nil ∧ e' = W64 8⌝ ∗ ∃ i, ⌜V2.cur !! logB = some (.file i)⌝ ∗
            segFile i) ∨ ⌜err' ≠ interface.nil⌝)) -∗ Φ (PairV #e' #err')) -∗
        logRes (GF := GF) R dir j V' -∗ Φ (PairV #(W64 0) #e) := by
    intro e he
    iintro HΦ Hh
    iapply HΦ
    iexists V'
    iframe Hh
    iright; ipureintro; exact he
  (try wp_auto)
  wp_apply wp_lockFile wp_Fd f fd (child dir logB) (DFrac.own 1) ⟨i, true, true, none, none⟩ rfl rfl
    $$ [Hos Hf Hfd] as %err ⟨Hf, Hr⟩
  · iframe; iexact Hos
  icases Hr with (⟨%herr, Hfd, Hk⟩ | ⟨%herr, Hfd⟩)
  rotate_left
  · cases err with
    | nil => exact absurd rfl herr
    | ok ie =>
    (try wp_auto)
    wp_apply wp_Close f fd (child dir logB) ⟨i, true, true, none, none⟩ $$ [Hos Hf Hfd] as %e' -
    · iframe; isplitr; iexact Hos; iapply lockToks_unlocked <;> rfl
    (try wp_auto)
    iapply hclose _ (by intro h; cases h) $$ HΦ Hh
  subst herr
  (try wp_auto)
  wp_apply os.File.Seek.wp_end f fd (child dir logB) (DFrac.own 1) (W64 0) (DFrac.own 1)
    (DFrac.own 1) ⟨i, true, true, some true, none⟩ newMeta hfd0 (by decide) $$ [Hos Hf Ho Hfd Hm]
    as %e0 %err ⟨Hf, Hfd, Hm, Hr⟩
  · iframe; iexact Hos
  icases Hr with (⟨%hr, Ho⟩ | ⟨%herr, Ho⟩)
  rotate_left
  · cases err with
    | nil => exact absurd rfl herr
    | ok ie =>
    (try wp_auto)
    wp_apply wp_Close f fd (child dir logB) ⟨i, true, true, some true, none⟩ $$ [Hos Hf Hfd Hk] as %e' -
    · iframe; isplitr; iexact Hos; iapply seg_lockToks $$ Hk
    (try wp_auto)
    iapply hclose _ (by intro h; cases h) $$ HΦ Hh
  obtain ⟨rfl, rfl⟩ := hr
  (try wp_auto)
  wp_apply wp_Fd f fd (child dir logB) (DFrac.own 1) $$ Hf as Hf
  (try wp_auto)
  ihave Hc0 : mcellsAny (GF := GF) newMeta.maps newMeta.size
      (max newMeta.size ((W64 0).toNat + (W64 65536).toNat)) $$ []
  · unfold mcellsAny; rw [show newMeta.maps = ∅ from rfl]
    iapply BigSepM.bigSepM_empty.2; iempintro
  wp_apply golang_org.x.sys.unix.Fallocate.wp_grow fd (W64 0) (W64 65536) (DFrac.own 1)
      ⟨i, true, true, some true, none⟩ newMeta rfl (by decide) (by decide)
    $$ [Hos Hfd Hm Hc0] as %e1 ⟨Hfd, %n1, Hr⟩
  · iframe; iexact Hos
  icases Hr with (⟨%he1, Hg⟩ | ⟨%he1, -⟩)
  rotate_left
  · rw [show errnoErr e1 = interface.mkOk syscall.Errno.ty #e1 from if_neg he1]
    dsimp only
    (try wp_auto)
    wp_apply wp_Close f fd (child dir logB) ⟨i, true, true, some true, none⟩ $$ [Hos Hf Hfd Hk] as %e' -
    · iframe; isplitr; iexact Hos; iapply seg_lockToks $$ Hk
    (try wp_auto)
    iapply hclose _ (by intro h; cases h) $$ HΦ Hh
  subst he1
  rw [show errnoErr 0 = interface.nil from if_pos rfl]
  dsimp only
  (try wp_auto)
  wp_apply os.File.Seek.wp_start f fd (child dir logB) (DFrac.own 1) (W64 0) (W64 0) hfd0 (by decide)
    (by decide) $$ [Hf Ho] as ⟨Hf, Ho⟩
  · iframe
  (try wp_auto)
  -- the record at 0
  unfold rsDone
  icases Hg with ⟨%zs, %hzs, Hm, Hb, -⟩
  have hT : max newMeta.size ((W64 0).toNat + (W64 65536).toNat) = 65536 := by decide
  try rw [hT]
  have hz : zs = List.replicate 65536 [(0, 0)] := by
    obtain ⟨hl, hzz, -⟩ := hzs
    have hl' : zs.length = 65536 := by rw [hl]; decide
    apply List.ext_getElem? ; intro j
    by_cases hj : j < 65536
    · rw [hzz j 0 rfl (Nat.zero_le _) (by rw [hl']; exact hj), List.getElem?_replicate, if_pos hj]
    · rw [List.getElem?_eq_none (by rw [hl']; omega),
        List.getElem?_eq_none (by rw [List.length_replicate]; omega)]
  subst hz
  simp only [List.map_replicate]
  rw [show newMeta.size = 0 from rfl]
  obtain ⟨xb, hxb⟩ : ∃ xb : ByteG, xb = ((0 : w8), [(0, 0)] ++ [(0, n1)]) := ⟨_, rfl⟩
  rw [← hxb]
  icases (osBytes_take_drop' i 0 8 (DFrac.own 1) (List.replicate 65536 xb)
    (by rw [List.length_replicate]; omega)).1 $$ Hb with ⟨Hb8, Hbr⟩
  rw [List.take_replicate, List.drop_replicate]
  have hmaps0 : (rsPost false newMeta 65536 65536).maps = ∅ := by simp [rsPost]; rfl
  ihave Hmc : mcellsAny (GF := GF) (rsPost false newMeta 65536 65536).maps (W64 0).toNat
      ((W64 0).toNat + dataC.length) $$ []
  · unfold mcellsAny; rw [hmaps0]
    iapply BigSepM.bigSepM_empty.2; iempintro
  wp_apply os.File.Write.wp_spec wp_WriteAt f fd (child dir logB) (DFrac.own 1) sl dataC dqs (W64 0)
      (DFrac.own 1) ⟨i, true, true, some true, none⟩ (rsPost false newMeta 65536 65536) (List.replicate (min 8 65536) xb)
      hfd0 rfl (by decide) (by simp only [rsPost]; decide) (by decide) (by decide)
      (by rw [List.length_replicate]; simp only [rsPost]; decide) (by decide)
    $$ [Hos Hf Ho Hsl Hfd Hm Hb8 Hmc] as %n %err ⟨Hf, Hsl, Hfd, ⟨%j', %ys, %Hres, Hm, Hys, -⟩, Ho⟩
  · iframe; iexact Hos
  cases err with
  | ok ie =>
    (try wp_auto)
    wp_apply wp_Close f fd (child dir logB) ⟨i, true, true, some true, none⟩ $$ [Hos Hf Hfd Hk] as %e' -
    · iframe; isplitr; iexact Hos; iapply seg_lockToks $$ Hk
    (try wp_auto)
    iapply hclose _ (by intro h; cases h) $$ HΦ Hh
  | nil =>
  obtain ⟨hj, hys, ⟨rfl, -, -⟩ | hne⟩ := Hres
  rotate_left
  · exact absurd rfl (by first | exact hne | exact hne.1)
  icases Ho with (⟨-, Ho⟩ | ⟨%hne, -⟩)
  rotate_left
  · exact absurd rfl (by first | exact hne | exact hne.1)
  rw [show W64 0 + W64 (dataC.length : Int) = W64 8 from rfl]
  (try wp_auto)
  -- the blocks
  wp_apply wp_Fd f fd (child dir logB) (DFrac.own 1) $$ Hf as Hf
  (try wp_auto)
  wp_apply golang_org.x.sys.unix.Fallocate.wp_keep fd (W64 0) (W64 65536) (DFrac.own 1)
      ⟨i, true, true, some true, none⟩ rfl (by decide) (by decide) $$ [Hos Hfd] as %e2 Hfd
  · iframe; iexact Hos
  by_cases he2 : e2 = 0
  rotate_left
  · rw [show errnoErr e2 = interface.mkOk syscall.Errno.ty #e2 from if_neg he2]
    dsimp only
    (try wp_auto)
    wp_apply wp_Close f fd (child dir logB) ⟨i, true, true, some true, none⟩ $$ [Hos Hf Hfd Hk] as %e' -
    · iframe; isplitr; iexact Hos; iapply seg_lockToks $$ Hk
    (try wp_auto)
    iapply hclose _ (by intro h; cases h) $$ HΦ Hh
  subst he2
  rw [show errnoErr 0 = interface.nil from if_pos rfl]
  dsimp only
  (try wp_auto)
  -- the sync
  wp_apply wp_Fd f fd (child dir logB) (DFrac.own 1) $$ Hf as Hf
  (try wp_auto)
  have hyl : ys.length = 8 := by
    rw [hys.1]; simp only [rsPost, pwSize, dataC]; decide
  ihave Hb := (osBytes_take_drop' i 0 8 (DFrac.own 1) (ys ++ List.replicate (65536 - 8) xb)
    (by rw [List.length_append, hyl, List.length_replicate]; omega)).2 $$ [Hys Hbr]
  · rw [List.take_left' hyl, List.drop_left' hyl]
    iframe
  have hall : (ys ++ List.replicate (65536 - 8) xb).length =
      (pwPost (rsPost false newMeta 65536 65536) (W64 0).toNat dataC.length dataC.length).size := by
    rw [List.length_append, hyl, List.length_replicate]; simp only [pwPost, rsPost, pwSize, dataC]; decide
  wp_apply wp_Fdatasync fd (DFrac.own 1) ⟨i, true, true, some true, none⟩ _ 0 _ (OsMeta.covers_whole _ hall)
      $$ [Hos Hfd Hm Hb] as %e3 ⟨Hfd, Hr⟩
  · iframe; iexact Hos
  icases Hr with (⟨%he3, Hm, Hb⟩ | ⟨%he3, -, -⟩)
  rotate_left
  · rw [show errnoErr e3 = interface.mkOk syscall.Errno.ty #e3 from if_neg he3.1]
    dsimp only
    (try wp_auto)
    wp_apply wp_Close f fd (child dir logB) ⟨i, true, true, some true, none⟩ $$ [Hos Hf Hfd Hk] as %e' -
    · iframe; isplitr; iexact Hos; iapply seg_lockToks $$ Hk
    (try wp_auto)
    iapply hclose _ (by intro h; cases h) $$ HΦ Hh
  subst he3
  rw [show errnoErr 0 = interface.nil from if_pos rfl]
  dsimp only
  (try wp_auto)
  wp_apply os.File.Seek.wp_cur f fd (child dir logB) (DFrac.own 1) (W64 8) hfd0 (by decide)
    (by decide) $$ [Hf Ho] as ⟨Hf, Ho⟩
  · iframe
  (try wp_auto)
  wp_apply wp_Close f fd (child dir logB) ⟨i, true, true, some true, none⟩ $$ [Hos Hf Hfd Hk] as %e' -
  · iframe; isplitr; iexact Hos; iapply seg_lockToks $$ Hk
  (try wp_auto)
  iapply HΦ
  iexists V'
  iframe Hh
  ileft
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  iexists i
  isplitr
  · ipureintro; exact hk
  unfold segFile
  iexists _, _
  iframe Hm Hb
  ipureintro
  refine ⟨by simp [OsMeta.synced, pwPost, hmaps0], ?_, by rw [List.length_map, hall]; simp only [pwPost, rsPost, pwSize, dataC]; decide⟩
  simp only [OsMeta.synced, pwPost, rsPost, pwSize, dataC]; decide

/-- `ZeroToEnd(f)`, the offset 8, the file of inode `i` (no mapping, `segSize` bytes) whole: on
success its first 8 bytes kept and its size at least 8; the offset stays some offset. -/
theorem wp_ZeroToEnd (wp_Truncate : os.File.Truncate.spec (GF := GF) (hG := hG))
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (f : Loc) (fd : w64) (name : GoString) (dqf dq : DFrac) (i : Ino) (m : OsMeta)
    (bs : List ByteG) (hfd0 : 0 ≤ fd.toInt) (hmaps : m.maps = ∅) (hsz : m.size = 0x10000)
    (hbl : bs.length = 0x10000) :
    {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ os.ownOff (GF := GF) f (W64 8) ∗
        osFd (GF := GF) fd dq ⟨i, true, true, none, none⟩ ∗ osMeta (GF := GF) i (DFrac.own 1) m ∗
        osBytes (GF := GF) i 0 (DFrac.own 1) bs }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.ZeroToEnd)) (Val #f))
    {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ osFd fd dq ⟨i, true, true, none, none⟩ ∗
        (∃ o, os.ownOff f o) ∗
        ((⌜err = interface.nil⌝ ∗ ∃ m', ⌜8 ≤ m'.size ∧ m'.size < 2 ^ 62⌝ ∗
            osMeta i (DFrac.own 1) m' ∗ osBytes i 0 (DFrac.own 1) (bs.take 8)) ∨
         ⌜err ≠ interface.nil⌝) }} := by
  wp_start as ⟨#Hos, Hf, Ho, Hfd, Hm, Hb⟩
  wp_auto
  wp_apply os.File.Seek.wp_cur f fd name dqf (W64 8) hfd0 (by decide) (by decide) $$ [Hf Ho] as ⟨Hf, Ho⟩
  · iframe
  (try wp_auto)
  wp_apply os.File.Seek.wp_end f fd name dqf (W64 8) dq (DFrac.own 1) ⟨i, true, true, none, none⟩ m
    hfd0 (by rw [hsz]; decide) $$ [Hos Hf Ho Hfd Hm] as %lenf %err ⟨Hf, Hfd, Hm, Hr⟩
  · iframe; iexact Hos
  icases Hr with (⟨%hr, Ho⟩ | ⟨%herr, Ho⟩)
  rotate_left
  · cases err with
    | nil => exact absurd rfl herr
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    iframe Hf Hfd
    isplitl [Ho]
    · iexists _; iexact Ho
    iright; ipureintro; intro h; cases h
  obtain ⟨rfl, rfl⟩ := hr
  rw [hsz]
  (try wp_auto)
  icases (osBytes_take_drop' i 0 8 _ bs (by omega)).1 $$ Hb with ⟨Hb8, Hbr⟩
  have hmin : min m.size (W64 8).toNat = 8 := by rw [hsz]; decide
  have hmax8 : max m.size (W64 8).toNat = 0x10000 := by rw [hsz]; decide
  ihave Hc8 : mcellsAny (GF := GF) m.maps (min m.size (W64 8).toNat) (rsHi true m.size (W64 8).toNat) $$ []
  · unfold mcellsAny; rw [hmaps]; iapply BigSepM.bigSepM_empty.2; iempintro
  wp_apply wp_Truncate f fd name dqf (W64 8) dq ⟨i, true, true, none, none⟩ m (bs.drop 8)
      hfd0 rfl (by decide) (by simp [hbl, hsz])
    $$ [Hos Hf Hfd Hm Hbr Hc8] as %err ⟨Hf, Hfd, Hr, -⟩
  · iframe; iframe #; rw [hmin]; iexact Hbr
  icases Hr with (⟨%he, Hd⟩ | ⟨%he, -⟩)
  rotate_left
  · cases err with
    | nil => exact absurd rfl he
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    iframe Hf Hfd
    isplitl [Ho]
    · iexists _; iexact Ho
    iright; ipureintro; intro h; cases h
  subst he
  unfold os.ftDone
  icases Hd with ⟨%zs0, -, Hm, -, -⟩
  (try wp_auto)
  have hg8 : sint.Z (W64 0) < sint.Z (W64 (0x10000 : Int)) := by decide
  try rw [decide_eq_true hg8]
  (try wp_auto)
  wp_apply wp_Fd f fd name dqf $$ Hf as Hf
  (try wp_auto)
  have hsh : (rsPost true m (W64 8).toNat (W64 8).toNat).size = 8 := rfl
  have hmaps2 : (rsPost true m (W64 8).toNat (W64 8).toNat).maps = ∅ := by simp [rsPost, hmaps]
  ihave Hc0 : mcellsAny (GF := GF) (rsPost true m (W64 8).toNat (W64 8).toNat).maps
      (rsPost true m (W64 8).toNat (W64 8).toNat).size
      (max (rsPost true m (W64 8).toNat (W64 8).toNat).size ((W64 0).toNat + (W64 0x10000).toNat)) $$ []
  · unfold mcellsAny; rw [hmaps2]; iapply BigSepM.bigSepM_empty.2; iempintro
  wp_apply golang_org.x.sys.unix.Fallocate.wp_grow fd (W64 0) (W64 0x10000) dq ⟨i, true, true, none, none⟩
      (rsPost true m (W64 8).toNat (W64 8).toNat) rfl (by decide) (by decide)
    $$ [Hos Hfd Hm Hc0] as %e1 ⟨Hfd, %n1, Hr⟩
  · iframe; iexact Hos
  icases Hr with (⟨%he1, Hg⟩ | ⟨%he1, -⟩)
  rotate_left
  · rw [show errnoErr e1 = interface.mkOk syscall.Errno.ty #e1 from if_neg he1]
    dsimp only
    (try wp_auto)
    iapply HΦ
    iframe Hf Hfd
    isplitl [Ho]
    · iexists _; iexact Ho
    iright; ipureintro; intro h; cases h
  subst he1
  rw [show errnoErr 0 = interface.nil from if_pos rfl]
  dsimp only
  (try wp_auto)
  wp_apply os.File.Seek.wp_start f fd name dqf _ (W64 8) hfd0 (by decide) (by decide)
    $$ [Hf Ho] as ⟨Hf, Ho⟩
  · iframe
  (try wp_auto)
  unfold rsDone
  icases Hg with ⟨%zs, -, Hm, -, -⟩
  iapply HΦ
  iframe Hf Hfd
  isplitl [Ho]
  · iexists _; iexact Ho
  ileft
  isplitr
  · ipureintro; rfl
  iexists _
  iframe Hm Hb8
  ipureintro
  simp only [rsPost, rsHi, hsh]
  constructor <;> decide

/-- `readFull(f, buf)` at the offset `o` of a non-empty `buf` (at most `maxRW` bytes) inside the
file, the bytes held at any fractions: `Read`s until it is full; any error is returned. -/
theorem wp_readFull (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sl : GoSlice)
    (vs : List w8) (o : w64) (dq dqm dqb : DFrac) (d : OsFd) (m : OsMeta) (xs : List ByteG)
    (hfd : 0 ≤ fd.toInt) (hrd : d.readable = true) (h0 : 0 ≤ o.toInt) (hn2 : vs.length ≤ 0x40000000)
    (hin : o.toNat + vs.length ≤ m.size) (hxl : xs.length = vs.length)
    (hmax : o.toInt + vs.length < 2 ^ 62) :
    {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ os.ownOff (GF := GF) f o ∗
        sl ↦* vs ∗ osFd (GF := GF) fd dq d ∗ osMeta (GF := GF) d.ino dqm m ∗
        osBytes (GF := GF) d.ino o.toNat dqb xs }}
      (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.readFull)) (Val #f))
        (Val #sl))
    {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ osFd fd dq d ∗
        osMeta d.ino dqm m ∗ osBytes d.ino o.toNat dqb xs ∗ (∃ vs' : List w8, sl ↦* vs') ∗
        (∃ o' : w64, os.ownOff f o') }} := by
  wp_start as ⟨#Hos, Hf, Ho, Hsl, Hfd, Hm, Hb⟩
  icases ownSlice_len sl _ vs $$ Hsl with %Hlen
  icases ownSlice_wf sl _ vs $$ Hsl with %Hwf
  wp_auto
  have hslz : sint.Z sl.len = vs.length := by
    have h1 := Hlen.1; have h2 := Hlen.2; simp only [sint.nat, sint.Z] at h1 h2 ⊢; omega
  ihave IH : iprop(∃ (nv : w64) (us : List w8), "n" ∷ n_ptr ↦ nv ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z nv ∧ sint.Z nv ≤ sint.Z sl.len ∧ us.length = vs.length⌝ ∗
      "Ho" ∷ os.ownOff (GF := GF) f (o + nv) ∗ "Hsl" ∷ sl ↦* us) $$ [n Ho Hsl]
  · iexists W64 0, vs
    rw [show o + W64 0 = o from BitVec.add_zero o]
    iframe
    ipureintro; exact ⟨by decide, Hlen.2, rfl⟩
  wp_for IH
  obtain ⟨hn0, hnl, hus⟩ := Hn
  wp_if_destruct
  · have hk : 0 ≤ sint.Z nv ∧ sint.Z nv ≤ sint.Z sl.len := ⟨hn0, hnl⟩
    rw [if_pos ⟨hn0, hnl, Hwf.2⟩]
    wp_auto
    ihave ⟨Hs1, Hs2⟩ := (ownSlice_split_all nv sl (DFrac.own 1) us hk).1 $$ Hsl
    have hnz : ((sint.nat nv : Nat) : Int) = sint.Z nv := Int.toNat_of_nonneg hn0
    have hnat : sint.nat nv < vs.length := by
      have : sint.Z nv < vs.length := by rw [← hslz]; exact Hif
      omega
    icases (osBytes_take_drop' d.ino o.toNat (sint.nat nv) dqb xs (by omega)).1 $$ Hb with ⟨Hb1, Hb2⟩
    have hon : (o + nv).toNat = o.toNat + sint.nat nv := by
      simp only [sint.nat, sint.Z] at hn0 hnat ⊢; word
    rw [← hon]
    have a1 : 0 ≤ (o + nv).toInt := by word
    have a2 : 0 < (us.drop (sint.nat nv)).length := by rw [List.length_drop, hus]; omega
    have a3 : (us.drop (sint.nat nv)).length ≤ 0x40000000 := by rw [List.length_drop, hus]; omega
    have a4 : (o + nv).toNat + (us.drop (sint.nat nv)).length ≤ m.size := by
      rw [List.length_drop, hus, hon]; omega
    have a5 : (xs.drop (sint.nat nv)).length = (us.drop (sint.nat nv)).length := by
      rw [List.length_drop, List.length_drop, hus, hxl]
    have a6 : (o + nv).toInt + (us.drop (sint.nat nv)).length < 2 ^ 62 := by
      rw [List.length_drop, hus]; simp only [sint.nat, sint.Z] at hn0 hnat; word
    wp_apply os.File.Read.wp_spec f fd name dqf (slice.slice sl w8 nv sl.len) (us.drop (sint.nat nv))
        (o + nv) dq dqm dqb d m (xs.drop (sint.nat nv)) hfd hrd a1 a2 a3 a4 a5 a6
      $$ [Hos Hf Ho Hs2 Hfd Hm Hb2] as %k %err ⟨Hf, Hfd, Hm, Hb2, %us', Hs2, %hul, Hr⟩
    · iframe; iexact Hos
    rw [hon]
    ihave Hb := (osBytes_take_drop' d.ino o.toNat (sint.nat nv) dqb xs (by omega)).2 $$ [Hb1 Hb2]
    · iframe
    ihave Hsl := (ownSlice_split_all nv sl (DFrac.own 1) (us.take (sint.nat nv) ++ us')
      hk).2 $$ [Hs1 Hs2]
    · rw [List.take_left' (by simp; omega), List.drop_left' (by simp; omega)]
      iframe
    icases Hr with (⟨%k', %hr, Ho⟩ | ⟨%hr, Ho⟩)
    · obtain ⟨hk0, hkl, rfl, rfl, -⟩ := hr
      (try wp_auto)
      wp_for_post
      iframe
      iexists nv + W64 k', _
      iframe
      isplitr
      · ipureintro
        simp only [List.length_drop] at hkl
        refine ⟨?_, ?_, ?_⟩
        · simp only [sint.nat, sint.Z] at hn0 hnat hkl hslz ⊢; word
        · simp only [sint.nat, sint.Z] at hn0 hnat hkl hslz ⊢; word
        · simp only [List.length_append, List.length_take, hul, List.length_drop]; omega
      rw [show o + (nv + W64 k') = o + nv + W64 k' from (BitVec.add_assoc _ _ _).symm]
      iexact Ho
    · obtain ⟨rfl, hne⟩ := hr
      cases err with
      | nil => exact absurd rfl (by first | exact hne | exact hne.1)
      | ok ie =>
      (try wp_auto)
      wp_for_post
      iapply HΦ
      iframe
  · (try wp_auto)
    iapply HΦ
    iframe

/-- `Reread(dir/seg.log, 8)`, `dir` the root of inode `j`, `seg.log` the file of inode `i` (a
fraction of a claim on it), of size at least 8, its first 8 bytes held at any fractions: it does not
panic. -/
theorem wp_Reread (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (R : Roots) (dir : GoString) (j : Ino) (hrj : (dir, j) ∈ R) (dqn : DFrac) (qc : Qp)
    (h : NamesH) (i : Ino) (hk : h.cur !! logB = some (.file i)) (dqm dqb : DFrac)
    (m : OsMeta) (bs : List ByteG) (hsz : 8 ≤ m.size) (hbl : bs.length = 8) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osCallPerm (callKey R dir) qc ∗ osNames j lN dqn h ∗
        osMeta (GF := GF) i dqm m ∗ osBytes (GF := GF) i 0 dqb bs }}
      (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.Reread))
        (Val #(child dir logB))) (Val #(W64 8)))
    {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err); True }} := by
  wp_start as ⟨#Hos, #Hsi, Hperm, Hn, Hm, Hb⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  imod osPathS_root R dir j (DFrac.own 1) hrj CoPset.subseteq_top $$ Hsi with Hp
  wp_apply os.OpenFile.wp_fileS dir logB (W64 0) (W32 0) R j i lN (DFrac.own 1) dqn h qc
      (by rw [show W64 0 ||| W64 0x80000 = flRO from by decide]; exact flRO_ok) (by decide)
      logB_ok lN_log hk $$ [Hos Hsi Hp Hn Hperm] as %f %err ⟨-, -, -, Hr⟩
  · iframe; iframe #
  icases Hr with (⟨%fd, %herr, Hf, Ho, Hfd⟩ | ⟨%herr, -⟩)
  rotate_left
  · cases err with
    | nil => exact absurd rfl herr.1
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    itrivial
  obtain ⟨rfl, hfdr⟩ := herr
  rw [show openFd i (W64 0 ||| W64 524288) = ⟨i, true, false, none, none⟩ by
    simp [openFd, O_WRONLY, O_RDONLY]]
  (try wp_auto)
  wp_apply (wp_slice_make2 (V := w8) (W64 8)) as %buf ⟨Hbuf, -⟩
  · ipureintro; decide
  (try wp_auto)
  wp_apply wp_readFull f fd (child dir logB) (DFrac.own 1) buf
      (List.replicate (sint.nat (W64 8)) (zero_val w8)) (W64 0) (DFrac.own 1) dqm dqb
      ⟨i, true, false, none, none⟩ m bs hfdr rfl (by decide) (by decide)
      (by rw [List.length_replicate]; exact hsz) (by rw [List.length_replicate, hbl]; rfl)
      (by decide) $$ [Hos Hf Ho Hbuf Hfd Hm Hb] as %err ⟨Hf, Hfd, Hm, Hb, -, -⟩
  · iframe; iexact Hos
  cases err with
  | ok ie =>
    (try wp_auto)
    wp_apply wp_Close f fd (child dir logB) ⟨i, true, false, none, none⟩ $$ [Hos Hf Hfd] as %e' -
    · iframe; isplitr; iexact Hos; iapply lockToks_unlocked <;> rfl
    (try wp_auto)
    iapply HΦ
    itrivial
  | nil =>
    (try wp_auto)
    wp_apply wp_Close f fd (child dir logB) ⟨i, true, false, none, none⟩ $$ [Hos Hf Hfd] as %e' -
    · iframe; isplitr; iexact Hos; iapply lockToks_unlocked <;> rfl
    (try wp_auto)
    iapply HΦ
    itrivial

/-- `Run(dir)`, `dir` the root of inode `j`, with the whole claim on `seg.log` (and, if it names a
directory, that directory's whole claim): it does not panic (nor is it stuck). -/
theorem wp_Run (wp_CreateS : os.OpenFile.specCreateS (GF := GF) (hG := hG))
    (wp_Truncate : os.File.Truncate.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (wp_WriteAt : os.File.WriteAt.spec (GF := GF) (hG := hG))
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_Fdatasync : syscall.Fdatasync.spec (GF := GF) (hG := hG))
    (R : Roots) (dir : GoString) (j : Ino) (hrj : (dir, j) ∈ R) (h0 : NamesH) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ logRes (GF := GF) R dir j h0 ∗ DS.subRes (GF := GF) logB h0 }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.Run)) (Val #dir))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hos, #Hsi, Hh, Hsub⟩
  wp_auto
  unfold logRes
  icases Hh with ⟨Hperm, Hn⟩
  imod osPathS_root R dir j (DFrac.own 1) hrj CoPset.subseteq_top $$ Hsi with Hp
  wp_apply wp_readNamesS dir R j (DFrac.own 1) 1 lN (DFrac.own 1) h0 $$ [Hp Hperm Hn]
    as %sl %ok ⟨-, Hperm, Hn, Hr⟩
  · iframe; iframe #
  icases Hr with (%hok | ⟨%names, %hn, Hsl⟩)
  · subst hok
    (try wp_auto)
    iapply HΦ
    itrivial
  obtain ⟨rfl, -, hmem, -⟩ := hn
  (try wp_auto)
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  try rw [show dir ++ go!"/seg.log" = child dir logB from rfl]
  ihave IH : iprop(∃ (i : w64) (nv : GoString) (h : NamesH),
      "i" ∷ i_ptr ↦ i ∗ "n" ∷ n_ptr ↦ nv ∗
      "Hperm" ∷ osCallPerm (GF := GF) (callKey R dir) 1 ∗
      "Hn" ∷ osNames (GF := GF) j lN (DFrac.own 1) h ∗ "Hsub" ∷ DS.subRes (GF := GF) logB h ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ names.length ∧
        (logB ∈ names.take (sint.nat i) → h.cur !! logB = none) ∧
        (logB ∉ names.take (sint.nat i) → h = h0)⌝) $$ [i n Hperm Hn Hsub]
  · iexists W64 0, _, h0
    iframe
    ipureintro
    refine ⟨by decide, ?_, ?_, fun _ => rfl⟩
    · rw [show sint.nat (W64 0) = 0 from rfl]; simp
    · rw [show sint.nat (W64 0) = 0 from rfl]; simp
  wp_for IH
  obtain ⟨hi0, hil, hgin, hgout⟩ := Hi
  wp_if_destruct
  · have Hlt : sint.nat i < names.length := by word
    have Hbnd : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len := ⟨hi0, Hif⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    obtain ⟨b, hb⟩ : ∃ b, names[sint.nat i]? = some b := ⟨_, List.getElem?_eq_getElem Hlt⟩
    wp_apply wp_load_slice_index sl (sint.Z i) names (DFrac.own 1) b hi0 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact hb
    have htake : names.take (sint.nat (i + W64 1)) = names.take (sint.nat i) ++ [b] := by
      rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word]
      rw [List.take_add_one, hb]; rfl
    (try wp_auto)
    by_cases hbl : b = logB
    · subst hbl
      rw [decide_eq_true (show logB = go!"seg.log" from rfl)]
      wp_auto
      imod osPathS_root R dir j (DFrac.own 1) hrj CoPset.subseteq_top $$ Hsi with Hp
      wp_apply DS.wp_rmAny R dir logB j (DFrac.own 1) h logB_ok $$ [Hp Hperm Hn Hsub]
        as %err ⟨-, Hperm, %h', Hn, Hsub, %hg'⟩
      · iframe; iframe #
      cases err with
      | ok ie =>
        (try wp_auto)
        wp_for_post
        iapply HΦ
        itrivial
      | nil =>
      (try wp_auto)
      wp_for_post
      iframe
      iexists i + W64 1, logB, h'
      iframe
      ipureintro
      have hg2 : h'.cur !! logB = none := by
        rcases hg' with ⟨-, hne⟩ | hn
        · exact absurd rfl hne
        · exact hn
      refine ⟨by word, by word, fun _ => hg2, fun h => absurd (by rw [htake]; simp) h⟩
    rw [decide_eq_false (show ¬ b = go!"seg.log" from hbl)]
    wp_auto
    wp_for_post
    iframe
    iexists i + W64 1, b, h
    iframe
    ipureintro
    refine ⟨by word, by word, ?_, ?_⟩
    · rw [htake]; intro h; simp [Ne.symm hbl] at h; exact hgin h
    · rw [htake]; intro h; simp [Ne.symm hbl] at h; exact hgout h
  · -- the loop is done
    have hie : sint.nat i = names.length := by word
    rw [hie, List.take_length] at hgin hgout
    have hn : h.cur !! logB = none := by
      by_cases hm : logB ∈ names
      · exact hgin hm
      · rw [hgout hm]
        cases hc : h0.cur !! logB with
        | none => rfl
        | some x => exact absurd ((hmem logB lN_log).1 (by rw [hc]; rfl)) hm
    iclear Hsub
    (try wp_auto)
    wp_apply wp_newData as %sl2 Hsl2
    (try wp_auto)
    ihave Hh : logRes (GF := GF) R dir j h $$ [Hperm Hn]
    · unfold logRes; iframe
    wp_apply wp_Segment wp_CreateS wp_Fd wp_Close wp_WriteAt wp_Fdatasync R dir j hrj h hn sl2 (DFrac.own 1)
      $$ [Hh Hsl2] as %e %err ⟨%V', Hh, Hr⟩
    · iframe; iframe #
    icases Hr with (⟨%hr, %k, %hk1, Hsf⟩ | %herr)
    rotate_left
    · cases err with
      | nil => exact absurd rfl herr
      | ok ie =>
      (try wp_auto)
      iapply HΦ
      itrivial
    obtain ⟨rfl, rfl⟩ := hr
    (try wp_auto)
    rw [show (W64 2 ||| W64 64) = W64 66 from by decide]
    unfold segFile
    icases Hsf with ⟨%m, %bs, %hm, Hm, Hb⟩
    obtain ⟨hmaps, hsz, hbl⟩ := hm
    unfold logRes
    icases Hh with ⟨Hperm, Hn⟩
    imod osPathS_root R dir j (DFrac.own 1) hrj CoPset.subseteq_top $$ Hsi with Hp
    wp_apply os.OpenFile.wp_fileS dir logB (W64 66) (W32 384) R j k lN (DFrac.own 1) (DFrac.own 1) V' 1
        createL_flag.1 createL_flag.2.2 logB_ok lN_log hk1 $$ [Hp Hn Hperm]
      as %f %err ⟨-, Hn, Hperm, Hr⟩
    · iframe; iframe #
    icases Hr with (⟨%fd, %herr, Hf, Ho, Hfd⟩ | ⟨%herr, -⟩)
    rotate_left
    · cases err with
      | nil => exact absurd rfl herr.1
      | ok ie =>
      (try wp_auto)
      iapply HΦ
      itrivial
    obtain ⟨rfl, hfd0⟩ := herr
    rw [createL_openFd]
    (try wp_auto)
    wp_apply os.File.Seek.wp_start f fd (child dir logB) (DFrac.own 1) (W64 0) (W64 8) hfd0
      (by decide) (by decide) $$ [Hf Ho] as ⟨Hf, Ho⟩
    · iframe
    (try wp_auto)
    wp_apply wp_ZeroToEnd wp_Truncate wp_Fd f fd (child dir logB) (DFrac.own 1) (DFrac.own 1) k m bs hfd0 hmaps
      hsz hbl $$ [Hos Hf Ho Hfd Hm Hb] as %err ⟨Hf, Hfd, -, Hr⟩
    · iframe; iexact Hos
    icases Hr with (⟨%herr, %m', %hm', Hm, Hb⟩ | %herr)
    rotate_left
    · cases err with
      | nil => exact absurd rfl herr
      | ok ie =>
      (try wp_auto)
      wp_apply wp_Close f fd (child dir logB) ⟨k, true, true, none, none⟩ $$ [Hos Hf Hfd] as %e' -
      · iframe; isplitr; iexact Hos; iapply lockToks_unlocked <;> rfl
      (try wp_auto)
      iapply HΦ
      itrivial
    subst herr
    (try wp_auto)
    wp_apply wp_Close f fd (child dir logB) ⟨k, true, true, none, none⟩ $$ [Hos Hf Hfd] as %e' -
    · iframe; isplitr; iexact Hos; iapply lockToks_unlocked <;> rfl
    (try wp_auto)
    wp_apply wp_Reread wp_Close R dir j hrj (DFrac.own 1) 1 V' k hk1 (DFrac.own 1) (DFrac.own 1) m'
      (bs.take 8) hm'.1 (by rw [List.length_take, hbl]; rfl) $$ [Hperm Hn Hm Hb] as %sl3 %err3 -
    · iframe; iframe #
    (try wp_auto)
    iapply HΦ
    itrivial

end prog

end osfs_walfs
end EtcdGrove
end Perennial

end
