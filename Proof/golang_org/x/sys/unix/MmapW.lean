/-
The proof of `Spec/golang_org/x/sys/unix/MmapW.lean`: by cases on `FsNoErr`, `specNoErr` or `spec`.
-/
module

public import Spec.golang_org.x.sys.unix.MmapW
public import Spec.golang_org.x.sys.unix.MmapNoErr

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [golang_org.x.sys.unix.Assumptions]

theorem golang_org.x.sys.unix.Mmap.wp_proofW
    (hM : golang_org.x.sys.unix.Mmap.spec (GF := GF) (hG := hG))
    (hNE : golang_org.x.sys.unix.Mmap.specNoErr (GF := GF) (hG := hG)) :
    golang_org.x.sys.unix.Mmap.specW (GF := GF) (hG := hG) := by
  intro fd off len prot fl dq d m hrd hoff hlen hprot hfl
  iintro %Φ Hpre HΦ
  by_cases hne : FsNoErr
  · obtain ⟨Sio, hSio, hs1, hs2, hsp⟩ := hne
    haveI := hs2
    iapply hNE Sio hSio fd off len prot fl dq d m hrd hoff hlen hprot hfl $$ Hpre
    inext
    iintro %base ⟨Hfd, Hm, Hc⟩
    iapply HΦ
    iframe Hfd
    ileft
    iexists base
    iframe Hm Hc
    ipureintro; exact ⟨rfl, rfl⟩
  · iapply hM fd off len prot fl dq d m hrd hoff hlen hprot hfl $$ Hpre
    inext
    iintro %sl %e ⟨Hfd, Hr⟩
    iapply HΦ
    iframe Hfd
    icases Hr with (H | ⟨%he, Hm⟩)
    · ileft; iexact H
    · iright; iframe Hm; ipureintro; exact ⟨he.1, he.2, hne⟩

end proof

end EtcdGrove
end Perennial
