module
public import Spec.go_etcd_io.bbolt.mmap
public import Spec.os.File__Fd
public import Spec.golang_org.x.sys.unix.Mmap
public import Spec.golang_org.x.sys.unix.Madvise
public import Perennial.Proof.fmt
public import Proof.go_etcd_io.bbolt.internal.common.Bytes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem mmap.wp_proof (hFd : os.File.Fd.spec (GF := GF) (hG := hG))
    (hMmap : unix.Mmap.spec (GF := GF) (hG := hG))
    (hMadvise : unix.Madvise.spec (GF := GF) (hG := hG)) :
    mmap.spec (GF := GF) (hG := hG) := by
  intro dbl d fd bs sz Hsz
  have Hfl : (W64 1 ||| d.MmapFlags') &&& W64 1 = W64 1 := or_one_and_one _
  wp_start as ⟨Hdb, #Hf, Hfb, Hmap⟩
  wp_auto
  wp_apply hFd $$ [Hf]
  · iexact Hf
  iintro -
  try wp_auto
  wp_apply hMmap fd bs sz (W64 1 ||| d.MmapFlags') Hsz Hfl $$ [Hfb Hmap]
    as %b %err ⟨Hfb, Hres⟩
  · iframe
  icases Hres with (⟨%Herr, Hmap⟩ | ⟨%Hok, Hmap, Hrange⟩)
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei =>
      try wp_auto
      ispecialize HΦ $$ %(GoInterface.ok ei)
      iapply HΦ
      iframe
      ileft
      iframe
      ipureintro; exact Herr
  · obtain ⟨rfl, Hbl, Hbc, Hbp⟩ := Hok
    try wp_auto
    wp_apply hMadvise b (W64 1) as %err2 %Herr2
    try wp_auto
    rcases Herr2 with rfl | ⟨e, rfl⟩
    · try wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by subst Hbl; word⟩)]
      unfold sliceIndexRef
      rw [show sint.Z (W64 0) = 0 by rfl, arrayIndexRef_zero]
      try wp_auto
      ispecialize HΦ $$ %GoInterface.nil
      iapply HΦ
      iframe
      iright
      iexists b
      iframe
      ipureintro; exact ⟨rfl, Hbl, Hbc, Hbp⟩
    · try wp_auto
      wp_if_destruct
      · -- ENOSYS: as without an error
        try wp_auto
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by subst Hbl; word⟩)]
        unfold sliceIndexRef
        rw [show sint.Z (W64 0) = 0 by rfl, arrayIndexRef_zero]
        try wp_auto
        ispecialize HΦ $$ %GoInterface.nil
        iapply HΦ
        iframe
        iright
        iexists b
        iframe
        ipureintro; exact ⟨rfl, Hbl, Hbc, Hbp⟩
      · -- another error: fmt.Errorf, the mapping lost
        try wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl ⟨Hsl, -⟩
        wp_apply fmt.wp_Errorf $$ [$Hsl] as %e2 _
        try wp_auto
        ispecialize HΦ $$ %(GoInterface.ok e2)
        iapply HΦ
        iframe
        ileft
        iframe
        isplitr
        · ipureintro; intro h; cases h
        · iright; iexists b.ptr; iframe

end proof

end bbolt
end EtcdGrove
end Perennial
