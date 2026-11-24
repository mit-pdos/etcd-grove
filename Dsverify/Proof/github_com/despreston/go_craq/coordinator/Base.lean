/-
The package fact of go-craq's `coordinator` (the craq kit, notes/dsv-craq.md): its `errors.New` variables (`errors.newVar`).
-/
module

public import Dsverify.GeneratedProof.github_com.despreston.go_craq.coordinator
public import Perennial.Proof.errors.Base
public import Dsverify.Proof.github_com.despreston.go_craq.transport.Base
public import Perennial.Proof.log
public import Perennial.Proof.sync
public import Perennial.Proof.time

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.despreston.go_craq.coordinator

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.despreston.go_craq.coordinator :=
  define_is_pkg_init iprop(errors.newVar ErrEmptyChain go!"no nodes in the chain" ∗
    errors.newVar errLastNode go!"cannot remove the last node of the chain" ∗
    errors.newVar errDisconnected go!"no metadata can be sent to the node" ∗
    errors.newVar ErrVersions go!"no version left")
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.despreston.go_craq.coordinator :=
  build_get_is_pkg_init_wf

end def_

end github_com.despreston.go_craq.coordinator
end Perennial
