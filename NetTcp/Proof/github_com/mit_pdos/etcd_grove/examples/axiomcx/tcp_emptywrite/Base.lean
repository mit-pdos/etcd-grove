/-
Shared definitions of the proof of `examples/axiomcx/tcp-emptywrite` (the counterexample of
`notes/axiom-review/tcp-semantics.md`): its package fact (`True`: no variables).
-/
module

public import NetTcp.GeneratedProof.github_com.mit_pdos.etcd_grove.examples.axiomcx.tcp_emptywrite
public import NetTcp.Proof.net.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.mit_pdos.etcd_grove.examples.axiomcx.tcp_emptywrite

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Tcp.tcpExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.axiomcx.tcp_emptywrite :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.axiomcx.tcp_emptywrite :=
  build_get_is_pkg_init_wf

end def_

end github_com.mit_pdos.etcd_grove.examples.axiomcx.tcp_emptywrite
end Perennial
