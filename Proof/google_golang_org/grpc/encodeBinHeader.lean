/-
The proof of `Spec/google_golang_org/grpc/encodeBinHeader.lean`: base64's fact, `RawStdEncoding`'s
part (`rawStdEncInit`).
-/
module

public import Spec.google_golang_org.grpc.encodeBinHeader

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.grpc.Assumptions]

theorem grpc.encodeBinHeader.wp_proof : grpc.encodeBinHeader.spec (GF := GF) (hG := hG) := by
  intro sl dq d
  wp_start as Hsl
  ihave #Hb : isPkgInit (PROP := IProp GF) pkg_id.encoding.base64 $$ []
  · iPkgInit
  ihave ⟨%e, #He, #Henc⟩ := encoding.base64.rawStdEncInit_access $$ Hb
  wp_auto
  wp_apply Henc $$ [Hsl] as Hsl
  · iexact Hsl
  iapply HΦ $$ Hsl

end proof

end EtcdGrove
end Perennial
