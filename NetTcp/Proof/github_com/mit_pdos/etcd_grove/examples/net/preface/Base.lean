/-
Shared definitions of the proof of `examples/net/preface`: its package fact (`True`: no variables).
-/
module

public import NetTcp.GeneratedProof.github_com.mit_pdos.etcd_grove.examples.net.preface
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.mit_pdos.etcd_grove.examples.net.preface

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Tcp.tcpExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.preface :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.preface :=
  build_get_is_pkg_init_wf

end def_

end github_com.mit_pdos.etcd_grove.examples.net.preface
end Perennial
