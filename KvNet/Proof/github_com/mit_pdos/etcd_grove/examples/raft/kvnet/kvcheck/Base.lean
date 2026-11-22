/-
# kvcheck: package initialization (2026-11-21)

`examples/raft/kvnet/kvcheck`'s `IsPkgInit` instance, with the fact `True`: the package has no
package-level variable (its constants are untyped or typed constants). Its initializer
(`etc/gen-init.py`) comes with kvnet's (notes/kvnet-part.md). The part's own file.
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Base
public import KvNet.GeneratedProof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.Base
public import Proof.github_com.anishathalye.porcupine.Defs
public import Perennial.Proof.github_com.goose_lang.primitive.Base
public import Proof.github_com.mit_pdos.gokv.trusted_proph.Base
public import Perennial.Proof.time.Base
public import Perennial.Proof.sync

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.Assumptions]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck :=
  build_get_is_pkg_init_wf

end init

end github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck

end Perennial
