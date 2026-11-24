/-
The package fact of go-craq's `node` (the craq kit, notes/dsv-craq.md): its `errors.New` variables (`errors.newVar`).
-/
module

public import Dsverify.GeneratedProof.github_com.despreston.go_craq.node
public import Perennial.Proof.errors.Base
public import Dsverify.Proof.github_com.despreston.go_craq.store.Base
public import Dsverify.Proof.github_com.despreston.go_craq.transport.Base
public import Perennial.Proof.log
public import Perennial.Proof.sync

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.despreston.go_craq.node

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.despreston.go_craq.node :=
  define_is_pkg_init iprop(errors.newVar errNoSuccessor go!"no successor" ∗
    errors.newVar errNoTail go!"no connection to the tail" ∗
    errors.newVar errNotTail go!"not the tail" ∗
    errors.newVar errTailVersion go!"failed to get the latest version from the tail")
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.despreston.go_craq.node :=
  build_get_is_pkg_init_wf

end def_

end github_com.despreston.go_craq.node
end Perennial
