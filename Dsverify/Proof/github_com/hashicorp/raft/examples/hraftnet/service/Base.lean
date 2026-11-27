/-
The package fact of the hraft kit's `examples/hraftnet/service` (notes/dsv-hraft.md): `True` (no package variables).
-/
module

public import Dsverify.GeneratedProof.github_com.hashicorp.raft.examples.hraftnet.service
public import Perennial.Proof.io.Base
public import Perennial.Proof.strconv.Base
public import Perennial.Proof.sync.Base
public import Perennial.Proof.time.Base
public import Dsverify.Proof.github_com.hashicorp.raft.Base
public import Dsverify.Proof.github_com.hashicorp.raft.examples.snapstore.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.hashicorp.raft.examples.hraftnet.service

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.service :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.service :=
  build_get_is_pkg_init_wf

end def_

end github_com.hashicorp.raft.examples.hraftnet.service
end Perennial
