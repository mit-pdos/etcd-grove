/-
Lean-first (no Rocq counterpart).

# The harness's package initialization (2026-11-09)

`examples/raft/tracecheck` (the closed program's package: `main.go`, `concurrent.go`, `sim.go`)
has no package-level variable (`stepTimeout` is a constant), so its package fact is `True`; the
packages it imports have theirs (Perennial's; raft's and `raftpb`'s, `Proof/go_etcd_io/raft/v3/Base.lean`;
the checker's, `etcdraft/Base.lean`).
-/
module

public import Proof.go_etcd_io.raft.v3.Base
public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Base
public import Perennial.Proof.github_com.goose_lang.primitive.Base
public import Perennial.Proof.context.Base
public import Perennial.Proof.time.Base
public import Perennial.Proof.sync.Base
public import Perennial.Proof.sync.atomic.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.mit_pdos.etcd_grove.examples.raft.tracecheck

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck :=
  build_get_is_pkg_init_wf

end init

end github_com.mit_pdos.etcd_grove.examples.raft.tracecheck

end Perennial
