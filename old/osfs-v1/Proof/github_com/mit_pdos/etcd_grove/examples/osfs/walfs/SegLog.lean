/-
The proofs of `examples/osfs/walfs`'s `seglog.go` (one generation), part 2: `lockFile`,
`Segment`, `ZeroToEnd`, `readFull`, `Reread` and the driver `Run`, over the specs of the calls
they make (hypotheses, as the walfs proof's `Boot.lean` takes them) and `SegLogOps.lean`'s.
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
  github_com.mit_pdos.etcd_grove.examples.osfs.walfs

section prog
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
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

theorem osBytes_take_drop' (p : GoString) (off n : Nat) (dq : DFrac) (bs : List (w8 × Bool))
    (hn : n ≤ bs.length) :
    osBytes (GF := GF) p off dq bs ⊣⊢
      osBytes (GF := GF) p off dq (bs.take n) ∗ osBytes (GF := GF) p (off + n) dq (bs.drop n) := by
  have A := bytesG_append (gooseOsGS (L := hG.goose_localGS)) p dq off (bs.take n) (bs.drop n)
  rw [List.take_append_drop, List.length_take, show min n bs.length = n by omega] at A
  exact A

/-- The segment's file after `Segment`: no mapping, `segSize` bytes, all of them held. -/
def segFile (k : GoString) : IProp GF :=
  iprop(∃ (m : OsMeta) (bs : List (w8 × Bool)), ⌜m.maps = ∅ ∧ m.size = 0x10000 ∧ bs.length = 0x10000⌝ ∗
    osMeta (GF := GF) k (DFrac.own 1) (some m) ∗ osBytes (GF := GF) k 0 (DFrac.own 1) bs)

/-- `Segment(d/seg.log, rec)`, `seg.log` absent, `rec` the 8 bytes of data: on success a new file
of a fresh key `k` named `seg.log`, `segSize` long, the offset past `rec` returned. -/
theorem wp_Segment (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (wp_WriteAt : os.File.WriteAt.spec (GF := GF) (hG := hG))
    (wp_Fdatasync : syscall.Fdatasync.spec (GF := GF) (hG := hG))
    (d : GoString) (g : DirG) (hn : g.now !! logB = none) (sl : GoSlice) (dqs : DFrac) :
    {{ osInv (GF := GF) ∗ logInv (GF := GF) d ∗ osDir (GF := GF) d (DFrac.own (1 : Qp).half) g ∗
        osNsBusy (GF := GF) false ∗ sl ↦*{dqs} dataC }}
      (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.Segment))
        (Val #(child d logB))) (Val #sl))
    {{ (e : w64) (err : GoInterface), RET (PairV #e #err); osNsBusy false ∗
        ((⌜err = interface.nil ∧ e = W64 8⌝ ∗ ∃ k,
            osDir d (DFrac.own (1 : Qp).half) (g.push (.put logB (.file k))) ∗ segFile k) ∨
         ⌜err ≠ interface.nil⌝) }} := by
  wp_start as ⟨#Hos, #Hinv, Hd, Hz, Hsl⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  rw [show (W64 2 ||| W64 64) = W64 66 from by decide]
  wp_apply wp_openLog d g hn (W32 384) $$ [Hos Hinv Hd Hz] as %f %err ⟨Hz, Hr⟩
  · iframe; iframe #
  icases Hr with (⟨%fd, %k, %hek, Hf, Ho, Hfd, Hm, Hd⟩ | %herr)
  rotate_left
  · cases err with
    | nil => exact absurd rfl herr
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    iframe Hz
    iright; ipureintro; intro h; cases h
  obtain ⟨rfl, hk⟩ := hek
  (try wp_auto)
  wp_apply wp_lockFile wp_Fd f fd (child d logB) (DFrac.own 1) (DFrac.own 1) ⟨k, true, true⟩
    $$ [Hos Hf Hfd] as %err ⟨Hf, Hfd⟩
  · iframe; iexact Hos
  cases err with
  | ok ie =>
    (try wp_auto)
    wp_apply wp_Close f fd (child d logB) ⟨k, true, true⟩ $$ [Hos Hf Hfd] as %e' -
    · iframe; iexact Hos
    (try wp_auto)
    iapply HΦ
    iframe Hz
    iright; ipureintro; intro h; cases h
  | nil =>
  (try wp_auto)
  wp_apply os.File.Seek.wp_end f fd (child d logB) (DFrac.own 1) (W64 0) (DFrac.own 1) (DFrac.own 1)
    ⟨k, true, true⟩ newMeta (by decide) $$ [Hos Hf Ho Hfd Hm] as %e0 %err ⟨Hf, Hfd, Hm, Hr⟩
  · iframe; iexact Hos
  icases Hr with (⟨%hr, Ho⟩ | ⟨%herr, Ho⟩)
  rotate_left
  · cases err with
    | nil => exact absurd rfl herr
    | ok ie =>
    (try wp_auto)
    wp_apply wp_Close f fd (child d logB) ⟨k, true, true⟩ $$ [Hos Hf Hfd] as %e' -
    · iframe; iexact Hos
    (try wp_auto)
    iapply HΦ
    iframe Hz
    iright; ipureintro; intro h; cases h
  obtain ⟨rfl, rfl⟩ := hr
  (try wp_auto)
  wp_apply wp_Fd f fd (child d logB) (DFrac.own 1) $$ Hf as Hf
  (try wp_auto)
  ihave Hc0 : mcellsAny (GF := GF) newMeta.maps newMeta.size 0 $$ []
  · iapply mcellsAny_nil; rfl
  wp_apply golang_org.x.sys.unix.Fallocate.wp_grow fd (W64 0) (W64 65536) (DFrac.own 1)
      ⟨k, true, true⟩ newMeta 0 rfl (by decide) (by decide) (fun b len h => by simp [newMeta] at h)
    $$ [Hos Hfd Hm Hc0] as %e1 ⟨Hfd, Hr⟩
  · iframe; iexact Hos
  icases Hr with (⟨%he1, Hg⟩ | %he1)
  rotate_left
  · rw [show errnoErr e1 = interface.mkOk syscall.Errno.ty #e1 from if_neg he1]
    dsimp only
    (try wp_auto)
    wp_apply wp_Close f fd (child d logB) ⟨k, true, true⟩ $$ [Hos Hf Hfd] as %e' -
    · iframe; iexact Hos
    (try wp_auto)
    iapply HΦ
    iframe Hz
    iright; ipureintro; intro h; cases h
  subst he1
  rw [show errnoErr 0 = interface.nil from if_pos rfl]
  dsimp only
  (try wp_auto)
  wp_apply os.File.Seek.wp_start f fd (child d logB) (DFrac.own 1) (W64 0) (W64 0) (by decide)
    (by decide) $$ [Hf Ho] as ⟨Hf, Ho⟩
  · iframe
  (try wp_auto)
  -- the record at 0
  unfold osGrown
  rw [show max 0 (0 + 65536) = 65536 from rfl, show newMeta.size = 0 from rfl]
  icases Hg with ⟨Hm, Hb, -, -⟩
  icases (osBytes_take_drop' k 0 8 _ _ (by rw [List.length_replicate]; omega)).1 $$ Hb with ⟨Hb8, Hbr⟩
  rw [List.take_replicate, List.drop_replicate]
  ihave Hmc : mcellsAny (GF := GF) (newMeta.grown 65536).maps (min (W64 0).toNat (newMeta.grown 65536).size)
      ((W64 0).toNat + dataC.length) $$ []
  · unfold mcellsAny; rw [show (newMeta.grown 65536).maps = ∅ from rfl]
    iapply BigSepM.bigSepM_empty.2; iempintro
  wp_apply os.File.Write.wp_spec wp_WriteAt f fd (child d logB) (DFrac.own 1) sl dataC dqs (W64 0)
      (DFrac.own 1) ⟨k, true, true⟩ 1 (newMeta.grown 65536) (List.replicate (min 8 (65536 - 0)) (0, false))
      rfl (by decide) (by decide) (by decide) (by decide) (fun _ => rfl) (by decide)
    $$ [Hos Hf Ho Hsl Hfd Hm Hb8 Hmc] as %n %err ⟨Hf, Hsl, Hfd, ⟨%j, %ys, %h, %Hres, Hm, Hys, -⟩, Ho⟩
  · iframe; iexact Hos
  have hclose : ∀ (e : GoInterface), e ≠ interface.nil →
      ⊢ (∀ e' err', osNsBusy (GF := GF) false ∗ ((⌜err' = interface.nil ∧ e' = W64 8⌝ ∗ ∃ k,
          osDir d (DFrac.own (1 : Qp).half) (g.push (.put logB (.file k))) ∗ segFile k) ∨
          ⌜err' ≠ interface.nil⌝) -∗ Φ (PairV #e' #err')) -∗ osNsBusy (GF := GF) false -∗
        Φ (PairV #(W64 0) #e) := by
    intro e he
    iintro HΦ Hz
    iapply HΦ
    iframe Hz
    iright; ipureintro; exact he
  cases err with
  | ok ie =>
    (try wp_auto)
    wp_apply wp_Close f fd (child d logB) ⟨k, true, true⟩ $$ [Hos Hf Hfd] as %e' -
    · iframe; iexact Hos
    (try wp_auto)
    iapply hclose _ (by intro h; cases h) $$ HΦ Hz
  | nil =>
  obtain ⟨hj, hys, -, ⟨rfl, -, -⟩ | ⟨-, hne⟩⟩ := Hres
  rotate_left
  · exact absurd rfl hne
  icases Ho with (⟨-, Ho⟩ | ⟨%hne, -⟩)
  rotate_left
  · exact absurd rfl hne
  rw [show pwSize 65536 0 dataC.length = 65536 from rfl,
    show W64 0 + W64 (dataC.length : Int) = W64 8 from rfl]
  generalize hm2 : (⟨65536, 0, h, false, true, ∅, [], 0⟩ : OsMeta) = m2
  have hm2maps : m2.maps = ∅ := by rw [← hm2]
  have hm2sz : m2.size = 65536 := by rw [← hm2]
  clear hm2
  (try wp_auto)
  -- the blocks
  wp_apply wp_Fd f fd (child d logB) (DFrac.own 1) $$ Hf as Hf
  (try wp_auto)
  wp_apply golang_org.x.sys.unix.Fallocate.wp_keep fd (W64 0) (W64 65536) (DFrac.own 1)
      ⟨k, true, true⟩ rfl (by decide) (by decide) $$ [Hos Hfd] as %e2 Hfd
  · iframe; iexact Hos
  by_cases he2 : e2 = 0
  rotate_left
  · rw [show errnoErr e2 = interface.mkOk syscall.Errno.ty #e2 from if_neg he2]
    dsimp only
    (try wp_auto)
    wp_apply wp_Close f fd (child d logB) ⟨k, true, true⟩ $$ [Hos Hf Hfd] as %e' -
    · iframe; iexact Hos
    (try wp_auto)
    iapply hclose _ (by intro h; cases h) $$ HΦ Hz
  subst he2
  rw [show errnoErr 0 = interface.nil from if_pos rfl]
  dsimp only
  (try wp_auto)
  -- the sync
  wp_apply wp_Fd f fd (child d logB) (DFrac.own 1) $$ Hf as Hf
  (try wp_auto)
  ihave Hb0 : osBytes (GF := GF) k 0 (DFrac.own 1) [] $$ []
  · unfold osBytes; iapply (bytesG_nil _ _ _ _).2; iempintro
  wp_apply wp_Fdatasync fd (DFrac.own 1) ⟨k, true, true⟩ _ 0 [] $$ [Hos Hfd Hm Hb0] as %e3 ⟨Hfd, Hr⟩
  · iframe; iexact Hos
  icases Hr with (⟨%he3, Hm, -⟩ | ⟨%he3, -, -⟩)
  rotate_left
  · rw [show errnoErr e3 = interface.mkOk syscall.Errno.ty #e3 from if_neg he3.1]
    dsimp only
    (try wp_auto)
    wp_apply wp_Close f fd (child d logB) ⟨k, true, true⟩ $$ [Hos Hf Hfd] as %e' -
    · iframe; iexact Hos
    (try wp_auto)
    iapply hclose _ (by intro h; cases h) $$ HΦ Hz
  subst he3
  rw [show errnoErr 0 = interface.nil from if_pos rfl]
  dsimp only
  (try wp_auto)
  wp_apply os.File.Seek.wp_cur f fd (child d logB) (DFrac.own 1) (W64 8) (by decide) (by decide)
    $$ [Hf Ho] as ⟨Hf, Ho⟩
  · iframe
  (try wp_auto)
  wp_apply wp_Close f fd (child d logB) ⟨k, true, true⟩ $$ [Hos Hf Hfd] as %e' -
  · iframe; iexact Hos
  (try wp_auto)
  iapply HΦ
  iframe Hz
  ileft
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  iexists k
  iframe Hd
  unfold segFile
  have hyl : ys.length = 8 := by
    have := congrArg List.length hys
    simp only [List.length_map] at this; rw [this]; simp [pwBytes, pwSize, dataC]; rfl
  ihave Hb := (osBytes_take_drop' k 0 8 (DFrac.own 1) (ys ++ List.replicate (65536 - 0 - 8) (0, false))
    (by rw [List.length_append, hyl, List.length_replicate]; omega)).2 $$ [Hys Hbr]
  · rw [List.take_left' hyl, List.drop_left' hyl]
    iframe
  iexists _, _
  iframe Hm Hb
  ipureintro
  refine ⟨hm2maps, by simp [OsMeta.synced, hm2sz], by rw [List.length_append, hyl, List.length_replicate]⟩

/-- `ZeroToEnd(f)`, the offset 8, the file of `k` (no mapping, `segSize` bytes) whole: on success
its first 8 bytes kept and its size at least 8; the offset stays some offset. -/
theorem wp_ZeroToEnd (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (f : Loc) (fd : w64) (name : GoString) (dqf dq : DFrac) (k : GoString) (m : OsMeta)
    (bs : List (w8 × Bool)) (hfd0 : 0 ≤ fd.toInt) (hmaps : m.maps = ∅) (hsz : m.size = 0x10000)
    (hbl : bs.length = 0x10000) :
    {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ os.ownOff (GF := GF) f (W64 8) ∗
        osFd (GF := GF) fd dq ⟨k, true, true⟩ ∗ osMeta (GF := GF) k (DFrac.own 1) (some m) ∗
        osBytes (GF := GF) k 0 (DFrac.own 1) bs }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.ZeroToEnd)) (Val #f))
    {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ osFd fd dq ⟨k, true, true⟩ ∗
        (∃ o, os.ownOff f o) ∗
        ((⌜err = interface.nil⌝ ∗ ∃ m', ⌜8 ≤ m'.size ∧ m'.size < 2 ^ 62⌝ ∗
            osMeta k (DFrac.own 1) (some m') ∗ osBytes k 0 (DFrac.own 1) (bs.take 8)) ∨
         ⌜err ≠ interface.nil⌝) }} := by
  wp_start as ⟨#Hos, Hf, Ho, Hfd, Hm, Hb⟩
  wp_auto
  wp_apply os.File.Seek.wp_cur f fd name dqf (W64 8) (by decide) (by decide) $$ [Hf Ho] as ⟨Hf, Ho⟩
  · iframe
  (try wp_auto)
  wp_apply os.File.Seek.wp_end f fd name dqf (W64 8) dq (DFrac.own 1) ⟨k, true, true⟩ m
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
  icases (osBytes_take_drop' k 0 8 _ bs (by omega)).1 $$ Hb with ⟨Hb8, Hbr⟩
  wp_apply os.File.Truncate.wp_shrink f fd name dqf (W64 8) dq ⟨k, true, true⟩ m (bs.drop 8)
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
  wp_apply golang_org.x.sys.unix.Fallocate.wp_grow fd (W64 0) (W64 0x10000) dq ⟨k, true, true⟩
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
  icases Hg with ⟨Hm, -, -, -⟩
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
file, the bytes held at any fractions: one `Read` fills it; any error is returned. -/
theorem wp_readFull (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sl : GoSlice)
    (vs : List w8) (o : w64) (dq dqm dqb : DFrac) (d : OsFd) (m : OsMeta) (xs : List (w8 × Bool))
    (hrd : d.readable = true) (h0 : 0 ≤ o.toInt) (hn : 0 < vs.length) (hn2 : vs.length ≤ 0x40000000)
    (hin : o.toNat + vs.length ≤ m.size) (hxl : xs.length = vs.length)
    (hmax : o.toInt + vs.length < 2 ^ 62) :
    {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ os.ownOff (GF := GF) f o ∗
        sl ↦* vs ∗ osFd (GF := GF) fd dq d ∗ osMeta (GF := GF) d.path dqm (some m) ∗
        osBytes (GF := GF) d.path o.toNat dqb xs }}
      (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.readFull)) (Val #f))
        (Val #sl))
    {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ osFd fd dq d ∗
        osMeta d.path dqm (some m) ∗ osBytes d.path o.toNat dqb xs ∗ (∃ vs' : List w8, sl ↦* vs') ∗
        (∃ o' : w64, os.ownOff f o') }} := by
  wp_start as ⟨#Hos, Hf, Ho, Hsl, Hfd, Hm, Hb⟩
  icases ownSlice_len sl _ vs $$ Hsl with %Hlen
  wp_auto
  have hslz : sint.Z sl.len = vs.length := by
    have h1 := Hlen.1; have h2 := Hlen.2; simp only [sint.nat, sint.Z] at h1 h2 ⊢; omega
  ihave IH : iprop(∃ nv : w64, "n" ∷ n_ptr ↦ nv ∗
      "Hst" ∷ ((⌜nv = W64 0⌝ ∗ os.ownOff (GF := GF) f o ∗ sl ↦* vs) ∨
        (⌜nv = sl.len⌝ ∗ (∃ o' : w64, os.ownOff (GF := GF) f o') ∗ ∃ vs' : List w8, sl ↦* vs'))) $$ [n Ho Hsl]
  · iexists W64 0; iframe; ileft; iframe; ipureintro; rfl
  wp_for IH
  wp_if_destruct
  · icases Hst with (⟨%hn0, Ho, Hsl⟩ | ⟨%hnl, -, -⟩)
    rotate_left
    · subst hnl; exact absurd Hif (Int.lt_irrefl _)
    subst hn0
    icases ownSlice_wf sl _ vs $$ Hsl with %Hwf
    rw [if_pos ⟨by decide, by rw [show sint.Z (W64 0) = 0 from rfl]; exact Hwf.1, Hwf.2⟩,
      ← slice_slice_trivial]
    wp_auto
    wp_apply os.File.Read.wp_spec f fd name dqf sl vs o dq dqm dqb d m xs hrd h0 hn hn2 hin hxl hmax
      $$ [Hos Hf Ho Hsl Hfd Hm Hb] as %n %err ⟨Hf, Hfd, Hm, Hb, %vs', Hsl, %hvl, Hr⟩
    · iframe; iexact Hos
    icases Hr with (⟨%hr, Ho⟩ | ⟨%hr, Ho⟩)
    · obtain ⟨rfl, rfl, -⟩ := hr
      (try wp_auto)
      wp_for_post
      iframe
      iexists _
      iframe
      iright
      isplitr
      · ipureintro
        have hsl : sl.len = W64 vs.length := by
          have h1 := Hlen.1; have h2 := Hlen.2; simp only [sint.nat, sint.Z] at h1 h2; word
        rw [hsl]; exact BitVec.zero_add _
      isplitl [Ho]
      · iexists _; iexact Ho
      iexists _; iexact Hsl
    · obtain ⟨rfl, hne⟩ := hr
      cases err with
      | nil => exact absurd rfl hne
      | ok ie =>
      (try wp_auto)
      wp_for_post
      iapply HΦ
      iframe
  · icases Hst with (⟨%hn0, Ho, Hsl⟩ | ⟨%hnl, Ho, Hsl⟩)
    · subst hn0
      exfalso; apply Hif
      rw [hslz, show sint.Z (W64 0) = 0 from rfl]; omega
    (try wp_auto)
    iapply HΦ
    iframe

/-- `Reread(d/seg.log, 8)`, `seg.log` the file of `k`, of size at least 8 (below `2^62`), its
first 8 bytes held at any fractions: it does not panic. -/
theorem wp_Reread (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (d k : GoString) (dq : DFrac) (g : DirG) (hk : g.now !! logB = some (.file k)) (dqm dqb : DFrac)
    (m : OsMeta) (bs : List (w8 × Bool)) (hsz : 8 ≤ m.size) (hsz2 : m.size < 2 ^ 62)
    (hbl : bs.length = 8) :
    {{ osInv (GF := GF) ∗ osDir (GF := GF) d dq g ∗ osMeta (GF := GF) k dqm (some m) ∗
        osBytes (GF := GF) k 0 dqb bs }}
      (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.Reread))
        (Val #(child d logB))) (Val #(W64 8)))
    {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err); True }} := by
  wp_start as ⟨#Hos, Hd, Hm, Hb⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply wp_openRO d logB k logB_ok (W32 0) dq g hk dqm (some m) $$ [Hos Hd Hm]
    as %f %err ⟨-, Hd, Hm, Hr⟩
  · iframe; iexact Hos
  icases Hr with (⟨%fd, %herr, Hf, Ho, Hfd⟩ | %herr)
  rotate_left
  · cases err with
    | nil => exact absurd rfl herr
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    itrivial
  subst herr
  (try wp_auto)
  wp_apply (wp_slice_make2 (V := w8) (W64 8)) as %buf ⟨Hbuf, -⟩
  · ipureintro; decide
  (try wp_auto)
  wp_apply wp_readFull f fd (child d logB) (DFrac.own 1) buf
      (List.replicate (sint.nat (W64 8)) (zero_val w8)) (W64 0) (DFrac.own 1) dqm dqb
      ⟨k, true, false⟩ m bs rfl (by decide) (by decide) (by decide)
      (by rw [List.length_replicate]; exact hsz) (by rw [List.length_replicate, hbl]; rfl)
      (by decide) $$ [Hos Hf Ho Hbuf Hfd Hm Hb] as %err ⟨Hf, Hfd, Hm, Hb, -, -⟩
  · iframe; iexact Hos
  cases err with
  | ok ie =>
    (try wp_auto)
    wp_apply wp_Close f fd (child d logB) ⟨k, true, false⟩ $$ [Hos Hf Hfd] as %e' -
    · iframe; iexact Hos
    (try wp_auto)
    iapply HΦ
    itrivial
  | nil =>
    (try wp_auto)
    wp_apply wp_Close f fd (child d logB) ⟨k, true, false⟩ $$ [Hos Hf Hfd] as %e' -
    · iframe; iexact Hos
    (try wp_auto)
    iapply HΦ
    itrivial

/-- `Run(d)`, from `d`'s ghost entry `g0` with nothing in flight and no directory at `seg.log`:
it does not panic (nor is it stuck). -/
theorem wp_Run (wp_ReadAt : os.File.ReadAt.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG))
    (wp_WriteAt : os.File.WriteAt.spec (GF := GF) (hG := hG))
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_Fdatasync : syscall.Fdatasync.spec (GF := GF) (hG := hG))
    (d : GoString) (g0 : DirG) (hp0 : g0.pend = []) (hnd : NoDirL g0) :
    {{ osInv (GF := GF) ∗ logInv (GF := GF) d ∗
        osDir (GF := GF) d (DFrac.own (1 : Qp).half) g0 ∗ osNsBusy (GF := GF) false }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.osfs.walfs.Run)) (Val #d))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hos, #Hinv, Hd, Hz⟩
  wp_auto
  wp_apply wp_readNames d (1 : Qp).half g0 $$ [Hos Hd] as %sl %ok ⟨Hd, Hr⟩
  · iframe; iexact Hos
  icases Hr with (%hok | ⟨%names, %hn, Hsl⟩)
  · subst hok
    (try wp_auto)
    iapply HΦ
    itrivial
  obtain ⟨rfl, hnodup, hmem⟩ := hn
  (try wp_auto)
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  try rw [show d ++ go!"/seg.log" = child d logB from rfl]
  ihave IH : iprop(∃ (i : w64) (nv : GoString) (g : DirG),
      "i" ∷ i_ptr ↦ i ∗ "n" ∷ n_ptr ↦ nv ∗
      "Hd" ∷ osDir (GF := GF) d (DFrac.own (1 : Qp).half) g ∗ "Hz" ∷ osNsBusy (GF := GF) false ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ names.length ∧
        g = (if logB ∈ names.take (sint.nat i) then g0.push (.del logB) else g0)⌝) $$ [i n Hd Hz]
  · iexists W64 0, _, g0
    iframe
    ipureintro
    refine ⟨by decide, ?_, ?_⟩ <;> rw [show sint.nat (W64 0) = 0 from rfl] <;> simp
  wp_for IH
  obtain ⟨hi0, hil, hg⟩ := Hi
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
    have hbt0 : b ∉ names.take (sint.nat i) := not_mem_take_of_nodup hnodup hb
    by_cases hbl : b = logB
    · subst hbl
      rw [decide_eq_true (show logB = go!"seg.log" from rfl)]
      wp_auto
      have hg0 : g = g0 := by rw [hg, if_neg hbt0]
      subst hg0
      obtain ⟨x, hx⟩ : ∃ x, g.now !! logB = some x := by
        have := (hmem logB).1 (List.mem_of_getElem? hb)
        cases h : g.now !! logB with
        | none => rw [h] at this; cases this
        | some x => exact ⟨x, rfl⟩
      obtain ⟨k, rfl⟩ : ∃ k, x = .file k := by
        cases x with
        | file k => exact ⟨k, rfl⟩
        | dir => exact absurd hx (hnd g.now g.crashTo_now)
      wp_apply wp_removeLog d k g hx $$ [Hos Hinv Hd Hz] as %err ⟨Hz, %g', Hd, %hg'⟩
      · iframe; iframe #
      cases err with
      | ok ie =>
        (try wp_auto)
        wp_for_post
        iapply HΦ
        itrivial
      | nil =>
      obtain rfl := hg' rfl
      (try wp_auto)
      wp_for_post
      iframe
      iexists i + W64 1, logB, g.push (.del logB)
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [htake]; simp
    rw [decide_eq_false (show ¬ b = go!"seg.log" from hbl)]
    wp_auto
    wp_for_post
    iframe
    iexists i + W64 1, b, g
    iframe
    ipureintro
    refine ⟨by word, by word, ?_⟩
    rw [htake, hg]; simp [Ne.symm hbl]
  · -- the loop is done
    have hie : sint.nat i = names.length := by word
    rw [hie, List.take_length] at hg
    have hn : g.now !! logB = none := by
      rw [hg]; split
      · rw [DirG.push_now]; exact GMap.lookup_delete_eq _ _
      · rename_i ht
        cases h : g0.now !! logB with
        | none => rfl
        | some x => exact absurd ((hmem logB).2 (by rw [h]; rfl)) ht
    (try wp_auto)
    wp_apply wp_newData as %sl2 Hsl2
    (try wp_auto)
    wp_apply wp_Segment wp_Fd wp_Close wp_WriteAt wp_Fdatasync d g hn sl2 (DFrac.own 1)
      $$ [Hos Hinv Hd Hz Hsl2] as %e %err ⟨Hz, Hr⟩
    · iframe; iframe #
    icases Hr with (⟨%hr, %k, Hd, Hsf⟩ | %herr)
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
    have hk1 : (g.push (.put logB (.file k))).now !! logB = some (.file k) := by
      rw [DirG.push_now]; exact GMap.lookup_insert_eq _ _ _
    unfold segFile
    icases Hsf with ⟨%m, %bs, %hm, Hm, Hb⟩
    obtain ⟨hmaps, hsz, hbl⟩ := hm
    wp_apply wp_openLogExisting d k _ _ hk1 (DFrac.own 1) (some m) (W32 384) $$ [Hos Hd Hm Hz]
      as %f %err ⟨-, Hd, Hm, Hz, Hr⟩
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
    (try wp_auto)
    wp_apply os.File.Seek.wp_start f fd (child d logB) (DFrac.own 1) (W64 0) (W64 8) (by decide)
      (by decide) $$ [Hf Ho] as ⟨Hf, Ho⟩
    · iframe
    (try wp_auto)
    wp_apply wp_ZeroToEnd wp_Fd f fd (child d logB) (DFrac.own 1) (DFrac.own 1) k m bs hfd0 hmaps hsz hbl
      $$ [Hos Hf Ho Hfd Hm Hb] as %err ⟨Hf, Hfd, -, Hr⟩
    · iframe; iexact Hos
    icases Hr with (⟨%herr, %m', %hm', Hm, Hb⟩ | %herr)
    rotate_left
    · cases err with
      | nil => exact absurd rfl herr
      | ok ie =>
      (try wp_auto)
      wp_apply wp_Close f fd (child d logB) ⟨k, true, true⟩ $$ [Hos Hf Hfd] as %e' -
      · iframe; iexact Hos
      (try wp_auto)
      iapply HΦ
      itrivial
    subst herr
    (try wp_auto)
    wp_apply wp_Close f fd (child d logB) ⟨k, true, true⟩ $$ [Hos Hf Hfd] as %e' -
    · iframe; iexact Hos
    (try wp_auto)
    wp_apply wp_Reread wp_Close d k _ _ hk1 (DFrac.own 1) (DFrac.own 1) m' (bs.take 8) hm'.1 hm'.2
      (by rw [List.length_take, hbl]; rfl) $$ [Hos Hd Hm Hb] as %sl3 %err3 -
    · iframe; iexact Hos
    (try wp_auto)
    iapply HΦ
    itrivial

end prog

end osfs_walfs
end EtcdGrove
end Perennial
