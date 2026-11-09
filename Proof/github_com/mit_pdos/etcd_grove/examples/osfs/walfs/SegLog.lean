/-
The proofs of `examples/osfs/walfs`'s `seglog.go` (one generation), part 2, over the file
extension v2: `lockFile`, `Segment`, `ZeroToEnd`, `readFull`, `Reread` and the driver `Run`, over
the specs of the calls they make (hypotheses) and `SegLogOps.lean`'s.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs.SegLogOps
public import Proof.os.TruncateShrink
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

/-- `lockFile(f)`: an OFD write lock, any error (the lock state is not modelled). -/
theorem wp_lockFile (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (f : Loc) (fd : w64) (name : GoString) (dqf dq : DFrac) (d : OsFd) :
    {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ osFd (GF := GF) fd dq d }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.lockFile)) (Val #f))
    {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ osFd fd dq d }} := by
  wp_start as ⟨#Hinv, Hf, Hfd⟩
  wp_auto
  wp_apply wp_Fd f fd name dqf $$ Hf as Hf
  wp_apply golang_org.x.sys.unix.FcntlFlock.wp_lock fd (W64 37) lk_ptr dq d (.inr (.inr (.inl rfl)))
    $$ [Hinv Hfd] as %e Hfd
  · iframe; iexact Hinv
  iapply HΦ
  iframe

/-- The segment's file after `Segment`: no mapping, `segSize` bytes, all of them held. -/
def segFile (i : Ino) : IProp GF :=
  iprop(∃ (m : OsMeta) (bs : List (w8 × Bool)), ⌜m.maps = ∅ ∧ m.size = 0x10000 ∧ bs.length = 0x10000⌝ ∗
    osMeta (GF := GF) i (DFrac.own 1) m ∗ osBytes (GF := GF) i 0 (DFrac.own 1) bs)

/-- `Segment(dir/seg.log, rec)`, `dir` the root of inode `j`, `seg.log` absent, `rec` the 8 bytes
of data: on success `seg.log` names a new file of a fresh inode `i`, `segSize` long, and the offset
past `rec` is returned. -/
theorem wp_Segment (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (wp_WriteAt : os.File.WriteAt.spec (GF := GF) (hG := hG))
    (wp_Fdatasync : syscall.Fdatasync.spec (GF := GF) (hG := hG))
    (R : Roots) (hR : RootsOk R) (dir : GoString) (j : Ino) (hrj : (dir, j) ∈ R)
    (V : Hist) (hn : V.now.entry j logB = none) (sl : GoSlice) (dqs : DFrac) :
    {{ osInv (GF := GF) ∗ logInv (GF := GF) R ∗ osTree (GF := GF) (DFrac.own (1 : Qp).half) R V ∗
        sl ↦*{dqs} dataC }}
      (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.Segment))
        (Val #(child dir logB))) (Val #sl))
    {{ (e : w64) (err : GoInterface), RET (PairV #e #err);
        ∃ V', osTree (DFrac.own (1 : Qp).half) R V' ∗
        ((⌜err = interface.nil ∧ e = W64 8⌝ ∗ ∃ i, ⌜V'.now.entry j logB = some (.file i)⌝ ∗
            segFile i) ∨
         ⌜err ≠ interface.nil⌝) }} := by
  wp_start as ⟨#Hos, #Hinv, Hh, Hsl⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  rw [show (W64 2 ||| W64 64) = W64 66 from by decide]
  wp_apply wp_openLog R hR dir j hrj V hn (W32 384) $$ [Hos Hinv Hh] as %f %err Hr
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
      ⊢ (∀ e' err', (∃ V2, osTree (GF := GF) (DFrac.own (1 : Qp).half) R V2 ∗
          ((⌜err' = interface.nil ∧ e' = W64 8⌝ ∗ ∃ i, ⌜V2.now.entry j logB = some (.file i)⌝ ∗
            segFile i) ∨ ⌜err' ≠ interface.nil⌝)) -∗ Φ (PairV #e' #err')) -∗
        osTree (GF := GF) (DFrac.own (1 : Qp).half) R V' -∗ Φ (PairV #(W64 0) #e) := by
    intro e he
    iintro HΦ Hh
    iapply HΦ
    iexists V'
    iframe Hh
    iright; ipureintro; exact he
  (try wp_auto)
  wp_apply wp_lockFile wp_Fd f fd (child dir logB) (DFrac.own 1) (DFrac.own 1) ⟨i, true, true⟩
    $$ [Hos Hf Hfd] as %err ⟨Hf, Hfd⟩
  · iframe; iexact Hos
  cases err with
  | ok ie =>
    (try wp_auto)
    wp_apply wp_Close f fd (child dir logB) ⟨i, true, true⟩ $$ [Hos Hf Hfd] as %e' -
    · iframe; iexact Hos
    (try wp_auto)
    iapply hclose _ (by intro h; cases h) $$ HΦ Hh
  | nil =>
  (try wp_auto)
  wp_apply os.File.Seek.wp_end f fd (child dir logB) (DFrac.own 1) (W64 0) (DFrac.own 1)
    (DFrac.own 1) ⟨i, true, true⟩ newMeta (by decide) $$ [Hos Hf Ho Hfd Hm]
    as %e0 %err ⟨Hf, Hfd, Hm, Hr⟩
  · iframe; iexact Hos
  icases Hr with (⟨%hr, Ho⟩ | ⟨%herr, Ho⟩)
  rotate_left
  · cases err with
    | nil => exact absurd rfl herr
    | ok ie =>
    (try wp_auto)
    wp_apply wp_Close f fd (child dir logB) ⟨i, true, true⟩ $$ [Hos Hf Hfd] as %e' -
    · iframe; iexact Hos
    (try wp_auto)
    iapply hclose _ (by intro h; cases h) $$ HΦ Hh
  obtain ⟨rfl, rfl⟩ := hr
  (try wp_auto)
  wp_apply wp_Fd f fd (child dir logB) (DFrac.own 1) $$ Hf as Hf
  (try wp_auto)
  ihave Hc0 : mcellsAny (GF := GF) newMeta.maps newMeta.size 0 $$ []
  · iapply mcellsAny_nil; rfl
  wp_apply golang_org.x.sys.unix.Fallocate.wp_grow fd (W64 0) (W64 65536) (DFrac.own 1)
      ⟨i, true, true⟩ newMeta 0 rfl (by decide) (by decide) (fun b len h => by simp [newMeta, initMeta] at h)
    $$ [Hos Hfd Hm Hc0] as %e1 ⟨Hfd, Hr⟩
  · iframe; iexact Hos
  icases Hr with (⟨%he1, Hg⟩ | %he1)
  rotate_left
  · rw [show errnoErr e1 = interface.mkOk syscall.Errno.ty #e1 from if_neg he1]
    dsimp only
    (try wp_auto)
    wp_apply wp_Close f fd (child dir logB) ⟨i, true, true⟩ $$ [Hos Hf Hfd] as %e' -
    · iframe; iexact Hos
    (try wp_auto)
    iapply hclose _ (by intro h; cases h) $$ HΦ Hh
  subst he1
  rw [show errnoErr 0 = interface.nil from if_pos rfl]
  dsimp only
  (try wp_auto)
  wp_apply os.File.Seek.wp_start f fd (child dir logB) (DFrac.own 1) (W64 0) (W64 0) (by decide)
    (by decide) $$ [Hf Ho] as ⟨Hf, Ho⟩
  · iframe
  (try wp_auto)
  -- the record at 0
  unfold osGrown
  icases Hg with ⟨%zs, %hzs, Hm, Hb, -, -⟩
  have hz : zs = List.replicate 65536 0 := by
    rw [hzs.2]; rfl
  subst hz
  simp only [List.length_nil, Nat.zero_add, Nat.zero_max, List.map_replicate]
  rw [show (initMeta newFile).size = 0 from rfl]
  icases (osBytes_take_drop' i 0 8 (DFrac.own 1) (List.replicate 65536 (0, false))
    (by rw [List.length_replicate]; omega)).1 $$ Hb with ⟨Hb8, Hbr⟩
  rw [List.take_replicate, List.drop_replicate]
  ihave Hmc : mcellsAny (GF := GF) (newMeta.grown 65536).maps (W64 0).toNat
      ((W64 0).toNat + dataC.length) $$ []
  · unfold mcellsAny; rw [show (newMeta.grown 65536).maps = ∅ from rfl]
    iapply BigSepM.bigSepM_empty.2; iempintro
  wp_apply os.File.Write.wp_spec wp_WriteAt f fd (child dir logB) (DFrac.own 1) sl dataC dqs (W64 0)
      (DFrac.own 1) ⟨i, true, true⟩ 1 (newMeta.grown 65536) (List.replicate (min 8 65536) (0, false))
      rfl (by decide) (by decide) (by decide) (by decide) (by decide) (fun _ => rfl) (.inl rfl) (by decide)
    $$ [Hos Hf Ho Hsl Hfd Hm Hb8 Hmc] as %n %err ⟨Hf, Hsl, Hfd, ⟨%j', %ys, %h, %v, %Hres, Hm, Hys, -⟩, Ho⟩
  · iframe; iexact Hos
  cases err with
  | ok ie =>
    (try wp_auto)
    wp_apply wp_Close f fd (child dir logB) ⟨i, true, true⟩ $$ [Hos Hf Hfd] as %e' -
    · iframe; iexact Hos
    (try wp_auto)
    iapply hclose _ (by intro h; cases h) $$ HΦ Hh
  | nil =>
  obtain ⟨hj, -, hys, -, ⟨rfl, -, -⟩ | hne⟩ := Hres
  rotate_left
  · exact absurd rfl hne
  icases Ho with (⟨-, Ho⟩ | ⟨%hne, -⟩)
  rotate_left
  · exact absurd rfl hne
  rw [show W64 0 + W64 (dataC.length : Int) = W64 8 from rfl]
  (try wp_auto)
  -- the blocks
  wp_apply wp_Fd f fd (child dir logB) (DFrac.own 1) $$ Hf as Hf
  (try wp_auto)
  wp_apply golang_org.x.sys.unix.Fallocate.wp_keep fd (W64 0) (W64 65536) (DFrac.own 1)
      ⟨i, true, true⟩ rfl (by decide) (by decide) $$ [Hos Hfd] as %e2 Hfd
  · iframe; iexact Hos
  by_cases he2 : e2 = 0
  rotate_left
  · rw [show errnoErr e2 = interface.mkOk syscall.Errno.ty #e2 from if_neg he2]
    dsimp only
    (try wp_auto)
    wp_apply wp_Close f fd (child dir logB) ⟨i, true, true⟩ $$ [Hos Hf Hfd] as %e' -
    · iframe; iexact Hos
    (try wp_auto)
    iapply hclose _ (by intro h; cases h) $$ HΦ Hh
  subst he2
  rw [show errnoErr 0 = interface.nil from if_pos rfl]
  dsimp only
  (try wp_auto)
  -- the sync
  wp_apply wp_Fd f fd (child dir logB) (DFrac.own 1) $$ Hf as Hf
  (try wp_auto)
  ihave Hb0 : osBytes (GF := GF) i 0 (DFrac.own 1) [] $$ []
  · unfold osBytes; iapply (bytesG_nil _ _ _ _).2; iempintro
  wp_apply wp_Fdatasync fd (DFrac.own 1) ⟨i, true, true⟩ _ 0 [] $$ [Hos Hfd Hm Hb0]
    as %e3 ⟨Hfd, Hr⟩
  · iframe; iexact Hos
  icases Hr with (⟨%he3, Hm, -⟩ | ⟨%he3, -, -⟩)
  rotate_left
  · rw [show errnoErr e3 = interface.mkOk syscall.Errno.ty #e3 from if_neg he3.1]
    dsimp only
    (try wp_auto)
    wp_apply wp_Close f fd (child dir logB) ⟨i, true, true⟩ $$ [Hos Hf Hfd] as %e' -
    · iframe; iexact Hos
    (try wp_auto)
    iapply hclose _ (by intro h; cases h) $$ HΦ Hh
  subst he3
  rw [show errnoErr 0 = interface.nil from if_pos rfl]
  dsimp only
  (try wp_auto)
  wp_apply os.File.Seek.wp_cur f fd (child dir logB) (DFrac.own 1) (W64 8) (by decide) (by decide)
    $$ [Hf Ho] as ⟨Hf, Ho⟩
  · iframe
  (try wp_auto)
  wp_apply wp_Close f fd (child dir logB) ⟨i, true, true⟩ $$ [Hos Hf Hfd] as %e' -
  · iframe; iexact Hos
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
  have hyl : ys.length = 8 := by
    have := congrArg List.length hys
    simp only [List.length_map] at this; rw [this]; simp [pwBytes, pwSize, dataC]; rfl
  ihave Hb := (osBytes_take_drop' i 0 8 (DFrac.own 1) (ys ++ List.replicate (65536 - 8) (0, false))
    (by rw [List.length_append, hyl, List.length_replicate]; omega)).2 $$ [Hys Hbr]
  · rw [List.take_left' hyl, List.drop_left' hyl]
    iframe
  iexists _, _
  iframe Hm Hb
  ipureintro
  refine ⟨rfl, by simp [OsMeta.synced, pwSize, dataC], by rw [List.length_append, hyl, List.length_replicate]⟩

/-- `ZeroToEnd(f)`, the offset 8, the file of inode `i` (no mapping, `segSize` bytes) whole: on
success its first 8 bytes kept and its size at least 8; the offset stays some offset. -/
theorem wp_ZeroToEnd (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (f : Loc) (fd : w64) (name : GoString) (dqf dq : DFrac) (i : Ino) (m : OsMeta)
    (bs : List (w8 × Bool)) (hfd0 : 0 ≤ fd.toInt) (hmaps : m.maps = ∅) (hsz : m.size = 0x10000)
    (hbl : bs.length = 0x10000) :
    {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ os.ownOff (GF := GF) f (W64 8) ∗
        osFd (GF := GF) fd dq ⟨i, true, true⟩ ∗ osMeta (GF := GF) i (DFrac.own 1) m ∗
        osBytes (GF := GF) i 0 (DFrac.own 1) bs }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.ZeroToEnd)) (Val #f))
    {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ osFd fd dq ⟨i, true, true⟩ ∗
        (∃ o, os.ownOff f o) ∗
        ((⌜err = interface.nil⌝ ∗ ∃ m', ⌜8 ≤ m'.size ∧ m'.size < 2 ^ 62⌝ ∗
            osMeta i (DFrac.own 1) m' ∗ osBytes i 0 (DFrac.own 1) (bs.take 8)) ∨
         ⌜err ≠ interface.nil⌝) }} := by
  wp_start as ⟨#Hos, Hf, Ho, Hfd, Hm, Hb⟩
  wp_auto
  wp_apply os.File.Seek.wp_cur f fd name dqf (W64 8) (by decide) (by decide) $$ [Hf Ho] as ⟨Hf, Ho⟩
  · iframe
  (try wp_auto)
  wp_apply os.File.Seek.wp_end f fd name dqf (W64 8) dq (DFrac.own 1) ⟨i, true, true⟩ m
    (by rw [hsz]; decide) $$ [Hos Hf Ho Hfd Hm] as %lenf %err ⟨Hf, Hfd, Hm, Hr⟩
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
  wp_apply os.File.Truncate.wp_shrink f fd name dqf (W64 8) dq ⟨i, true, true⟩ m (bs.drop 8)
      hfd0 rfl (by decide) (by rw [hsz]; decide) hmaps (by simp [hbl, hsz])
    $$ [Hos Hf Hfd Hm Hbr] as %err ⟨Hf, Hfd, Hr⟩
  · iframe; iexact Hos
  icases Hr with (⟨%he, Hm⟩ | %he)
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
  (try wp_auto)
  have hg8 : sint.Z (W64 0) < sint.Z (W64 (0x10000 : Int)) := by decide
  try rw [decide_eq_true hg8]
  (try wp_auto)
  wp_apply wp_Fd f fd name dqf $$ Hf as Hf
  (try wp_auto)
  have hsh : (m.shrunk (W64 8).toNat).size = 8 := rfl
  ihave Hc0 : mcellsAny (GF := GF) (m.shrunk (W64 8).toNat).maps (m.shrunk (W64 8).toNat).size 8 $$ []
  · iapply mcellsAny_nil; exact hsh
  wp_apply golang_org.x.sys.unix.Fallocate.wp_grow fd (W64 0) (W64 0x10000) dq ⟨i, true, true⟩
      (m.shrunk (W64 8).toNat) 8 rfl (by decide) (by decide)
      (fun b len h => by rw [OsMeta.shrunk_maps, hmaps] at h; simp at h)
    $$ [Hos Hfd Hm Hc0] as %e1 ⟨Hfd, Hr⟩
  · iframe; iexact Hos
  icases Hr with (⟨%he1, Hg⟩ | %he1)
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
  wp_apply os.File.Seek.wp_start f fd name dqf _ (W64 8) (by decide) (by decide) $$ [Hf Ho] as ⟨Hf, Ho⟩
  · iframe
  (try wp_auto)
  unfold osGrown
  icases Hg with ⟨%zs, -, Hm, -, -, -⟩
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
  simp only [OsMeta.grown, hsh]
  constructor <;> decide

/-- `readFull(f, buf)` at the offset `o` of a non-empty `buf` (at most `maxRW` bytes) inside the
file, the bytes held at any fractions: `Read`s until it is full; any error is returned. -/
theorem wp_readFull (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sl : GoSlice)
    (vs : List w8) (o : w64) (dq dqm dqb : DFrac) (d : OsFd) (m : OsMeta) (xs : List (w8 × Bool))
    (hrd : d.readable = true) (h0 : 0 ≤ o.toInt) (hn2 : vs.length ≤ 0x40000000)
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
        (o + nv) dq dqm dqb d m (xs.drop (sint.nat nv)) hrd a1 a2 a3 a4 a5 a6
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
      | nil => exact absurd rfl hne
      | ok ie =>
      (try wp_auto)
      wp_for_post
      iapply HΦ
      iframe
  · (try wp_auto)
    iapply HΦ
    iframe

/-- `Reread(dir/seg.log, 8)`, `dir` the root of inode `j`, `seg.log` the file of inode `i`, of
size at least 8, its first 8 bytes held at any fractions: it does not panic. -/
theorem wp_Reread (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (R : Roots) (hR : RootsOk R) (dir : GoString) (j : Ino) (hrj : (dir, j) ∈ R) (q : Qp)
    (V : Hist) (i : Ino) (hk : V.now.entry j logB = some (.file i)) (dqm dqb : DFrac)
    (m : OsMeta) (bs : List (w8 × Bool)) (hsz : 8 ≤ m.size) (hbl : bs.length = 8) :
    {{ osInv (GF := GF) ∗ osTree (GF := GF) (DFrac.own q) R V ∗ osMeta (GF := GF) i dqm m ∗
        osBytes (GF := GF) i 0 dqb bs }}
      (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.Reread))
        (Val #(child dir logB))) (Val #(W64 8)))
    {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err); True }} := by
  wp_start as ⟨#Hos, Hh, Hm, Hb⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  have hl : lookupH R V (child dir logB) = some (.file i) := by
    rw [lookupH_child_root hR hrj V logB_ok]; exact hk
  wp_apply wp_openExisting (child dir logB) (W64 0) flRO_ok (by decide) q R V i hl (W32 0)
    $$ [Hos Hh] as %f %err ⟨-, Hr⟩
  · iframe; iexact Hos
  icases Hr with (⟨%fd, %herr, Hf, Ho, Hfd⟩ | %herr)
  rotate_left
  · cases err with
    | nil => exact absurd rfl herr
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    itrivial
  obtain ⟨rfl, -⟩ := herr
  rw [show openFd i (W64 0 ||| W64 524288) = ⟨i, true, false⟩ by
    simp [openFd, O_WRONLY, O_RDONLY]]
  (try wp_auto)
  wp_apply (wp_slice_make2 (V := w8) (W64 8)) as %buf ⟨Hbuf, -⟩
  · ipureintro; decide
  (try wp_auto)
  wp_apply wp_readFull f fd (child dir logB) (DFrac.own 1) buf
      (List.replicate (sint.nat (W64 8)) (zero_val w8)) (W64 0) (DFrac.own 1) dqm dqb
      ⟨i, true, false⟩ m bs rfl (by decide) (by decide)
      (by rw [List.length_replicate]; exact hsz) (by rw [List.length_replicate, hbl]; rfl)
      (by decide) $$ [Hos Hf Ho Hbuf Hfd Hm Hb] as %err ⟨Hf, Hfd, Hm, Hb, -, -⟩
  · iframe; iexact Hos
  cases err with
  | ok ie =>
    (try wp_auto)
    wp_apply wp_Close f fd (child dir logB) ⟨i, true, false⟩ $$ [Hos Hf Hfd] as %e' -
    · iframe; iexact Hos
    (try wp_auto)
    iapply HΦ
    itrivial
  | nil =>
    (try wp_auto)
    wp_apply wp_Close f fd (child dir logB) ⟨i, true, false⟩ $$ [Hos Hf Hfd] as %e' -
    · iframe; iexact Hos
    (try wp_auto)
    iapply HΦ
    itrivial

/-- `Run(dir)`, `dir` the root of inode `j`, from half of the history: it does not panic (nor is
it stuck). -/
theorem wp_Run (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (wp_WriteAt : os.File.WriteAt.spec (GF := GF) (hG := hG))
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_Fdatasync : syscall.Fdatasync.spec (GF := GF) (hG := hG))
    (R : Roots) (hR : RootsOk R) (dir : GoString) (j : Ino) (hrj : (dir, j) ∈ R) (V0 : Hist) :
    {{ osInv (GF := GF) ∗ logInv (GF := GF) R ∗
        osTree (GF := GF) (DFrac.own (1 : Qp).half) R V0 }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.Run)) (Val #dir))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hos, #Hinv, Hh⟩
  wp_auto
  wp_apply wp_readNamesT dir _ R V0 j (lookupH_root hR hrj V0) $$ [Hos Hh] as %sl %ok ⟨Hh, Hr⟩
  · iframe; iexact Hos
  icases Hr with (%hok | ⟨%names, %hn, Hsl⟩)
  · subst hok
    (try wp_auto)
    iapply HΦ
    itrivial
  obtain ⟨rfl, hnodup, hmem⟩ := hn
  (try wp_auto)
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  try rw [show dir ++ go!"/seg.log" = child dir logB from rfl]
  ihave IH : iprop(∃ (i : w64) (nv : GoString) (V : Hist),
      "i" ∷ i_ptr ↦ i ∗ "n" ∷ n_ptr ↦ nv ∗
      "Hh" ∷ osTree (GF := GF) (DFrac.own (1 : Qp).half) R V ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ names.length ∧
        (logB ∈ names.take (sint.nat i) → V.now.entry j logB = none) ∧
        (logB ∉ names.take (sint.nat i) → V = V0)⌝) $$ [i n Hh]
  · iexists W64 0, _, V0
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
      wp_apply wp_removeLog R hR dir j hrj V $$ [Hos Hinv Hh] as %err ⟨%V', Hh, %hg'⟩
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
      iexists i + W64 1, logB, V'
      iframe
      ipureintro
      refine ⟨by word, by word, fun _ => hg' rfl, fun h => absurd (by rw [htake]; simp) h⟩
    rw [decide_eq_false (show ¬ b = go!"seg.log" from hbl)]
    wp_auto
    wp_for_post
    iframe
    iexists i + W64 1, b, V
    iframe
    ipureintro
    refine ⟨by word, by word, ?_, ?_⟩
    · rw [htake]; intro h; simp [Ne.symm hbl] at h; exact hgin h
    · rw [htake]; intro h; simp [Ne.symm hbl] at h; exact hgout h
  · -- the loop is done
    have hie : sint.nat i = names.length := by word
    rw [hie, List.take_length] at hgin hgout
    have hn : V.now.entry j logB = none := by
      by_cases hm : logB ∈ names
      · exact hgin hm
      · rw [hgout hm]
        cases h : V0.now.entry j logB with
        | none => rfl
        | some x => exact absurd ((hmem logB).2 (by rw [h]; rfl)) hm
    (try wp_auto)
    wp_apply wp_newData as %sl2 Hsl2
    (try wp_auto)
    wp_apply wp_Segment wp_Fd wp_Close wp_WriteAt wp_Fdatasync R hR dir j hrj V hn sl2 (DFrac.own 1)
      $$ [Hos Hinv Hh Hsl2] as %e %err ⟨%V', Hh, Hr⟩
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
    have hl : lookupH R V' (child dir logB) = some (.file k) := by
      rw [lookupH_child_root hR hrj V' logB_ok]; exact hk1
    have hfl : OpenFlagsOk (W64 66 ||| W64 524288).toNat := by
      rw [show (W64 66 ||| W64 524288) = flCreat from by decide]; exact flCreat_ok
    wp_apply wp_openExisting (child dir logB) (W64 66) hfl (by decide) _ R V' k hl (W32 384)
      $$ [Hos Hh] as %f %err ⟨Hh, Hr⟩
    · iframe; iexact Hos
    icases Hr with (⟨%fd, %herr, Hf, Ho, Hfd⟩ | %herr)
    rotate_left
    · cases err with
      | nil => exact absurd rfl herr
      | ok ie =>
      (try wp_auto)
      iapply HΦ
      itrivial
    obtain ⟨rfl, hfd0⟩ := herr
    rw [show (W64 66 ||| W64 524288) = W64 0x80042 from by decide, openFd_rw]
    (try wp_auto)
    wp_apply os.File.Seek.wp_start f fd (child dir logB) (DFrac.own 1) (W64 0) (W64 8) (by decide)
      (by decide) $$ [Hf Ho] as ⟨Hf, Ho⟩
    · iframe
    (try wp_auto)
    wp_apply wp_ZeroToEnd wp_Fd f fd (child dir logB) (DFrac.own 1) (DFrac.own 1) k m bs hfd0 hmaps
      hsz hbl $$ [Hos Hf Ho Hfd Hm Hb] as %err ⟨Hf, Hfd, -, Hr⟩
    · iframe; iexact Hos
    icases Hr with (⟨%herr, %m', %hm', Hm, Hb⟩ | %herr)
    rotate_left
    · cases err with
      | nil => exact absurd rfl herr
      | ok ie =>
      (try wp_auto)
      wp_apply wp_Close f fd (child dir logB) ⟨k, true, true⟩ $$ [Hos Hf Hfd] as %e' -
      · iframe; iexact Hos
      (try wp_auto)
      iapply HΦ
      itrivial
    subst herr
    (try wp_auto)
    wp_apply wp_Close f fd (child dir logB) ⟨k, true, true⟩ $$ [Hos Hf Hfd] as %e' -
    · iframe; iexact Hos
    (try wp_auto)
    wp_apply wp_Reread wp_Close R hR dir j hrj _ V' k hk1 (DFrac.own 1) (DFrac.own 1) m' (bs.take 8)
      hm'.1 (by rw [List.length_take, hbl]; rfl) $$ [Hos Hh Hm Hb] as %sl3 %err3 -
    · iframe; iexact Hos
    (try wp_auto)
    iapply HΦ
    itrivial

end prog

end osfs_walfs
end EtcdGrove
end Perennial

end
