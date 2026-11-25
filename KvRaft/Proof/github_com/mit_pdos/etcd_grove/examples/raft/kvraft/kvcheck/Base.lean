/-
# kvcheck: package initialization (2026-11-21)

`examples/raft/kvraft/kvcheck`'s `IsPkgInit` instance, with the fact `True`: the package has no
package-level variable (its constants are untyped or typed constants). Its initializer
(`etc/gen-init.py`) comes with kvraft's (notes/kvraft-part.md). The part's own file.
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Base
public import KvRaft.GeneratedProof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck
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

namespace github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.Assumptions]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck :=
  build_get_is_pkg_init_wf

end init

end github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck

end Perennial
