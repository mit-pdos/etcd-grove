/-
The package fact of `github_com.gogo.protobuf.proto`: `True` (names only here (no model: notes/dsv-rabia.md), no variables).
-/
module

public import Dsverify.GeneratedProof.github_com.gogo.protobuf.proto
public import Net.Proof.net.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.gogo.protobuf.proto

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.gogo.protobuf.proto :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.gogo.protobuf.proto :=
  build_get_is_pkg_init_wf

end def_

end github_com.gogo.protobuf.proto
end Perennial
