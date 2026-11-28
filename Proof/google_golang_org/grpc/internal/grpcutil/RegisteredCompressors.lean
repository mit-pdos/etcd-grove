/-
The proof of `Spec/google_golang_org/grpc/internal/grpcutil/RegisteredCompressors.lean`: `strings.Join`
of the nil slice (Perennial's `strings.Join.spec`).
-/
module

public import Spec.google_golang_org.grpc.internal.grpcutil.RegisteredCompressors
public import Perennial.Spec.strings.Join

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

theorem grpcutil.RegisteredCompressors.wp_proof
    (wp_Join : _root_.Perennial.strings.Join.spec (GF := GF) (hG := hG)) :
    grpcutil.RegisteredCompressors.spec (GF := GF) (hG := hG) := by
  wp_start as #Hpkg
  ihave #Hr : (go_etcd_io.etcd.cache.v3.grpcutilInit (GF := GF) : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  ihave #Hs : isPkgInit (PROP := IProp GF) pkg_id.strings $$ []
  · iPkgInit
  wp_auto
  ihave Hnil := ownSlice_nil (V := GoString) (GF := GF) (DFrac.own 1)
  wp_apply (wp_Join slice.nil [] (DFrac.own 1) go!",") $$ [Hs Hnil] as -
  · isplitl [Hnil]
    · iexact Hnil
    ipureintro
    simp
  simp only [List.intercalate_nil]
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
