/-
# kvraft: package initialization (2026-11-21)

`examples/raft/kvraft`'s `IsPkgInit` instance, for now with the fact `True`: the package's only
variable is `StatNames` (stats.go, an array literal of the counters' names), which no proof reads
yet. Its fact (`StatNames` holds those names, read-only) comes with the package's initializer
(`etc/gen-init.py`'s `KVRAFT_INITS`, notes/kvraft-part.md), when a proof needs it.

The part's own file: the specs and proofs `etc/copy-part.py` takes from kvdurablenoax (the same Go
text, `RENAME_KVRAFT`) import this module in place of kvdurablenoax's `Base`.
-/
module

public import KvRaft.Proof.go_etcd_io.raft.v3.Base
public import KvRaft.Proof.go_etcd_io.raft.v3.PbModel
public import KvRaft.GeneratedProof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft
public import KvRaft.Proof.net.Base
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.lib.durable.PkgInit
public import Perennial.Proof.encoding.binary
public import Perennial.Proof.github_com.goose_lang.primitive.Base
public import Perennial.Proof.context.Base
public import Perennial.Proof.time.Base
public import Perennial.Proof.fmt.Base
public import Perennial.Proof.sync
public import Proof.github_com.anishathalye.porcupine.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.mit_pdos.etcd_grove.examples.raft.kvraft

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft :=
  build_get_is_pkg_init_wf

end init

end github_com.mit_pdos.etcd_grove.examples.raft.kvraft

end Perennial
