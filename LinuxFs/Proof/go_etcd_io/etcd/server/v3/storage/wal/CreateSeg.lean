/- Lean-first (no Rocq counterpart).
# `Create`'s first segment: `createNewWALFile(nm.tmp/0…0.wal, false)` (W4 of `notes/wal-fsext-plan.md`)

* `walOpenFlag_create`: `walOpenFlag false` with `O_CLOEXEC` is a valid write-only create open (no
  `O_TRUNC`).
* `wp_createSeg`: `createNewWALFile(dir/b, false)` (the `*fileutil.LockedFile` instance) of a name absent
  in the whole claim held, over `os.OpenFile.specCreateSnc` with the trivial update (`osAUnc_triv`): the
  open's outcome `o` (`crOut`, `crMeta`: on a create the claim logged with `b` holding the new inode, whose
  `OsMeta` is `newMeta`), and on success the locked file, open write-only on that inode (`crIno`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.PipeLemmas
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.createNewWALFile

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Fs

/-- `walOpenFlag false` with `O_CLOEXEC` is a valid write-only create open, not truncating. -/
theorem walOpenFlag_create :
    OpenFlagsOk (wal.walOpenFlag false ||| W64 0x80000).toNat ∧
      (wal.walOpenFlag false ||| W64 0x80000).toNat / O_CREAT % 2 = 1 ∧
      (wal.walOpenFlag false ||| W64 0x80000).toNat / O_TRUNC % 2 = 0 := by
  unfold OpenFlagsOk O_CREAT O_TRUNC O_CLOEXEC wal.walOpenFlag
  decide

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions]

/-- **`createNewWALFile(dir/b, false)` of a name absent from the whole claim held** (see the file
header). -/
theorem wp_createSeg [os.file.FieldAssumptions]
    (wp_create : go_etcd_io.etcd.server.v3.storage.wal.createNewWALFile.specLocked (GF := GF)
      (hG := hG))
    (wp_open : os.OpenFile.specCreateSnc (GF := GF) (hG := hG))
    (R : Roots) (dir : GoString) (dq : DFrac) (j : Ino) (b : GoString) (h : NamesH) (qc : Qp)
    (hb : NameOk b) (hcur : h.cur !! b = none) :
    {{ osInv (GF := GF) ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗
        osSharedInv R ∗ osPathS R dir dq j ∗ osCallPerm qc ∗ osNames j (.only [b]) (DFrac.own 1) h }}
      (App (App (Val #(functions go_etcd_io.etcd.server.v3.storage.wal.createNewWALFile
          [go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.LockedFile.ty]))
          (Val #(child dir b))) (Val #false))
    {{ (lf : Loc) (err : GoInterface), RET (PairV #lf #err);
        osPathS R dir dq j ∗ osCallPerm qc ∗ ∃ o, crOut j b h (DFrac.own 1) o ∗ crMeta o ∗
        ((⌜err = interface.nil⌝ ∗ ∃ (f : Loc) (fd : w64) (i : Ino),
            ⌜0 ≤ fd.toInt ∧ crIno b h o i⌝ ∗
            fileutil.lockedFile lf f ∗ os.ownFile f fd (child dir b) (DFrac.own 1) ∗
            os.ownOff f (W64 0) ∗
            osFd fd (DFrac.own 1) (openFd i (wal.walOpenFlag false ||| W64 0x80000))) ∨
         ⌜err ≠ interface.nil⌝) }} := by
  iintro %Φ ⟨#Hos, #Hpkg, #Hsi, Hp, Hperm, Hn⟩ HΦ
  obtain ⟨hfl, hcr, htr⟩ := walOpenFlag_create
  let A : Option (Nat × Nat × Ino) → Bool → IProp GF := fun o _ =>
    iprop(osPathS R dir dq j ∗ osCallPerm qc ∗ crOut j b h (DFrac.own 1) o ∗ crMeta o)
  have hnd : ∀ J, h.cur !! b ≠ some (.dir J) := by
    intro J hJ; rw [hcur] at hJ; cases hJ
  have hT : fileutil.OpenTriple
      iprop(osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R dir dq j ∗ osCallPerm qc ∗
        osNames j (.only [b]) (DFrac.own 1) h)
      (child dir b) (wal.walOpenFlag false) (W32 384) A (crIno b h) := by
    unfold fileutil.OpenTriple
    iintro %Ψ ⟨#Hos, #Hsi, Hp, Hperm, Hn⟩ HΨ
    icases (osNames_join j _ _ _ h (Qp.half_add_half 1)).2 $$ Hn with ⟨Hn, Hr⟩
    ihave Hau := osAUnc_triv (A := Option (Nat × Nat × Ino))
      (osNames (GF := GF) j (.only [b]) (DFrac.own (1 : Qp).half) h)
      (crOut j b h (DFrac.own (1 : Qp).half)) $$ Hr
    iapply wp_open dir b (wal.walOpenFlag false) (W32 384) R j dq h (1 : Qp).half (1 : Qp).half
      qc (crOut j b h (DFrac.own (1 : Qp).half)) hfl hcr htr hb hnd
      (Qp.half_add_half 1) $$ [$Hos $Hsi $Hp $Hperm $Hn $Hau]
    inext
    iintro %f %err ⟨Hp, Hperm, %o, Ho1, Ho2, Hm, Hr⟩
    iapply HΨ
    unfold fileutil.openPost
    iexists o
    ihave Ho := crOut_join j b h o $$ [$Ho1 $Ho2]
    icases Hr with (⟨%fd, %i, %hres, Hf, Hoff, Hfd⟩ | ⟨%herr, Hok⟩)
    · obtain ⟨rfl, hfd, hi⟩ := hres
      ileft
      isplitr
      · ipureintro; rfl
      isplitl [Hp Hperm Ho Hm]
      · simp only [A]
        iframe
      iexists fd, i
      iframe
      ipureintro; exact ⟨hfd, hi⟩
    · iright
      isplitr
      · ipureintro; exact herr
      iframe Hok
      simp only [A]
      iframe
  wp_apply wp_create (child dir b) false _ _ A (crIno b h) hT $$ [$Hos $Hpkg $Hsi $Hp $Hperm $Hn]
    as %lf %err Hpost
  unfold fileutil.lockPost
  icases Hpost with ⟨%o, (⟨%he, HA, %f, %fd, %i, %hc, Hlf, Hf, Hoff, Hfd⟩ | ⟨%he, %ok, HA⟩)⟩
  · simp only [A]
    icases HA with ⟨Hp, Hperm, Ho, Hm⟩
    iapply HΦ
    iframe Hp Hperm
    iexists o
    iframe Ho Hm
    ileft
    isplitr
    · ipureintro; exact he
    iexists f, fd, i
    iframe
    ipureintro; exact hc
  · simp only [A]
    icases HA with ⟨Hp, Hperm, Ho, Hm⟩
    iapply HΦ
    iframe Hp Hperm
    iexists o
    iframe Ho Hm
    iright
    ipureintro; exact he.1

end proof

end WalFs
end EtcdGrove
end Perennial
