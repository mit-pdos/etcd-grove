/-
A done context's `Err()` is `context.Canceled` or `context.DeadlineExceeded`: from Go's contract of
`Context.Err` (`context.ErrAny`, the trust boundary; until 2026-10-18 this was itself the axiom).
-/
module

public import Spec.context.ErrDone
public import Spec.context.ErrAny

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

theorem context.ErrDone.wp_proof (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG)) :
    context.ErrDone.spec (GF := GF) (hG := hG) := by
  intro c cd
  iintro %Φ ⟨#Hp, #Hc, Hcl⟩ HΦ
  iapply (wp_ErrAny c cd .Done) $$ [Hcl] [HΦ]
  · iframe #; iexact Hcl
  inext
  iintro %err ⟨%Hne, Hid⟩
  iapply HΦ
  icases Hid with (%Hn | ⟨%Ht, Hv⟩)
  · exact absurd Hn Hne
  iframe Hv
  ipureintro; exact Ht

end proof

end EtcdGrove
end Perennial
