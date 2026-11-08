/-
Lean-first (no Rocq counterpart).

# The Go checker's package initialization (Draft, 2026-11-08)

`examples/raft/tracecheck/etcdraft` has package-level variables (`EmptyBag`, `Invariants`, the
tables `RaftMsgType`, `RaftMsgSubtype`, `ReceiveMessageTraceNames`). Draft: its package fact is
`True`, enough to state the checker's specs; the proofs (Draft S6 of
`notes/trace-validation-plan.md`) strengthen it with what they read of those variables (the
tables' contents, `Invariants`' functions), which callers get from the package's initialization
(`etc/gen-init.py`), not from the specs.
-/
module

public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft
public import Perennial.Proof.fmt
public import Perennial.Proof.strconv
public import Perennial.Proof.strings

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft :=
  build_get_is_pkg_init_wf

end init

end github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft

end Perennial
