/-
The proof of `Spec/golang_org/x/sys/unix/MadviseW.lean`: by cases on `FsNoErr`, `specNoErr` or `spec`
(the `OsMeta` framed).
-/
module

public import Spec.golang_org.x.sys.unix.MadviseW
public import Spec.golang_org.x.sys.unix.MadviseNoErr

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

theorem golang_org.x.sys.unix.Madvise.wp_proofW
    (hM : golang_org.x.sys.unix.Madvise.spec (GF := GF) (hG := hG))
    (hNE : golang_org.x.sys.unix.Madvise.specNoErr (GF := GF) (hG := hG)) :
    golang_org.x.sys.unix.Madvise.specW (GF := GF) (hG := hG) := by
  intro base len cap advice p dq m n hadv hb hlen hmap
  iintro %Φ ⟨#Hos, Hm⟩ HΦ
  by_cases hne : FsNoErr
  · obtain ⟨Sio, hSio, hs1, hs2, hsp⟩ := hne
    haveI := hs2
    iapply hNE Sio hSio base len cap advice p dq m n hadv hb hlen hmap $$ [Hm]
    · iframe; iframe #
    inext
    iintro Hm
    iapply HΦ
    iframe Hm
    ipureintro; exact Or.inl rfl
  · iapply hM ⟨base, len, cap⟩ advice hadv (by simp only; omega) $$ [Hos]
    · iexact Hos
    inext
    iintro %e -
    iapply HΦ
    iframe Hm
    ipureintro; exact Or.inr hne

end proof

end EtcdGrove
end Perennial
