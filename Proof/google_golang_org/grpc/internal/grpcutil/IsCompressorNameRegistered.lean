/-
The proof of `Spec/google_golang_org/grpc/internal/grpcutil/IsCompressorNameRegistered.lean`: the
loop runs over the nil slice.
-/
module

public import Spec.google_golang_org.grpc.internal.grpcutil.IsCompressorNameRegistered

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
variable [package_sem : google_golang_org.grpc.internal.grpcutil.Assumptions]

theorem grpcutil.IsCompressorNameRegistered.wp_proof :
    grpcutil.IsCompressorNameRegistered.spec (GF := GF) (hG := hG) := by
  intro name
  wp_start as #Hpkg
  ihave #Hr : (go_etcd_io.etcd.cache.v3.grpcutilInit (GF := GF) : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  wp_auto
  ihave IH : iprop("i" ∷ i_ptr ↦ W64 0 ∗ "res" ∷ «$res0_ptr» ↦ zero_val Bool) $$ [i «$res0»]
  · simp only [named]; iframe
  wp_for IH
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
