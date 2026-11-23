/-
The package fact of go-craq's `examples.craqnet` (the craq kit, notes/dsv-craq.md): `True` (no package variables).
-/
module

public import Dsverify.GeneratedProof.github_com.despreston.go_craq.examples.craqnet
public import Net.Proof.net.Base
public import Dsverify.Proof.github_com.despreston.go_craq.coordinator.Base
public import Dsverify.Proof.github_com.despreston.go_craq.node.Base
public import Dsverify.Proof.github_com.despreston.go_craq.store.kv.Base
public import Dsverify.Proof.github_com.despreston.go_craq.transport.netrpc.Base
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Base
public import Perennial.Proof.errors.Base
public import Perennial.Proof.log
public import Perennial.Proof.sync
public import Perennial.Proof.time
public import Dsverify.Proof.net.rpc.Base
public import Dsverify.Proof.net.http.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.despreston.go_craq.examples.craqnet

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.despreston.go_craq.examples.craqnet :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.despreston.go_craq.examples.craqnet :=
  build_get_is_pkg_init_wf

end def_

end github_com.despreston.go_craq.examples.craqnet
end Perennial
