/-
Shared definitions of the proof of `examples/net/httpdriver` (net/http's driver,
notes/library-drivers.md): its package fact, `True` (its variable, `reached`, is read by the proofs
from what the initializer stores, not from the fact).
-/
module

public import Net.GeneratedProof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver
public import Net.Proof.net.Base
public import Net.Proof.net.http.PkgInit
public import Proof.bufio.PkgInit
public import Perennial.Proof.io.Base
public import Perennial.Proof.strconv.Base
public import Perennial.Proof.sync.Base
public import Perennial.Proof.github_com.goose_lang.primitive.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.mit_pdos.etcd_grove.examples.net.httpdriver

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.httpdriver :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.httpdriver :=
  build_get_is_pkg_init_wf

end def_

end github_com.mit_pdos.etcd_grove.examples.net.httpdriver
end Perennial
