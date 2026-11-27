/-
The package fact of the hraft fork's `examples/snapstore` (the hraft kit, notes/dsv-hraft.md): its `errors.New` variables (`errors.newVar`).
-/
module

public import Dsverify.GeneratedProof.github_com.hashicorp.raft.examples.snapstore
public import Perennial.Proof.errors.Base
public import Perennial.Proof.io.Base
public import Perennial.Proof.strconv.Base
public import Perennial.Proof.sync.Base
public import Dsverify.Proof.github_com.hashicorp.raft.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.hashicorp.raft.examples.snapstore

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.hashicorp.raft.examples.snapstore :=
  define_is_pkg_init iprop(errors.newVar ErrNoSnapshot go!"snapstore: no such snapshot" ∗
    errors.newVar ErrClosed go!"snapstore: sink closed")
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.hashicorp.raft.examples.snapstore :=
  build_get_is_pkg_init_wf

end def_

end github_com.hashicorp.raft.examples.snapstore
end Perennial
