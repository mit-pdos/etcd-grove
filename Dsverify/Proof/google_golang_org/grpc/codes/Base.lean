/-
The package fact of grpc/codes: `True` (notes/dsv-quepaxa.md). (dsv-retire-2, 2026-11-25: translated as
the main tree's, its `strToCode` and `init` with their bodies, importing grpc's `internal`, whose instance
is `../internal/Base.lean`.)
-/
module

public import Dsverify.GeneratedProof.google_golang_org.grpc.codes
public import Net.Proof.net.Base
public import Dsverify.Proof.google_golang_org.grpc.internal.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace google_golang_org.grpc.codes

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.codes :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.grpc.codes :=
  build_get_is_pkg_init_wf

end def_

end google_golang_org.grpc.codes
end Perennial
