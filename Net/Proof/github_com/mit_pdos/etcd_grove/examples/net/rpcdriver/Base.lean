/-
Shared definitions of the proof of `examples/net/rpcdriver` (net/rpc's driver,
notes/library-drivers.md): its package fact, `True` (its variables, `reached` and `failMsgs`, are
read by the client's proof from what the initializer stores, not from the fact).
-/
module

public import Net.GeneratedProof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.service.Base
public import Net.Proof.net.Base
public import Net.Proof.net.rpc.PkgInit
public import Net.Proof.net.http.PkgInit
public import Perennial.Proof.errors.Base
public import Perennial.Proof.sync.Base
public import Perennial.Proof.github_com.goose_lang.primitive.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.mit_pdos.etcd_grove.examples.net.rpcdriver

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver :=
  build_get_is_pkg_init_wf

end def_

end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver
end Perennial
