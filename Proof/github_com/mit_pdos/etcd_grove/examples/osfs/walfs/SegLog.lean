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

end prog

end osfs_walfs
end EtcdGrove
end Perennial
