/-
Lean-first (no Rocq counterpart).

The proof of `vrOf`: the value's bytes copied to a string, the composite literal.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.vrOf

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.linkvtxn

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

theorem vrOf.wp_proof : vrOf.spec (GF := GF) (hG := hG) := by
  intro sl b dq mod ver
  wp_start as Hs
  wp_auto
  wp_apply wp_bytes_to_string sl b dq $$ [Hs] as Hs
  · iexact Hs
  iapply HΦ
  iexact Hs

end proof

end linkvtxn
end EtcdGrove
end Perennial
