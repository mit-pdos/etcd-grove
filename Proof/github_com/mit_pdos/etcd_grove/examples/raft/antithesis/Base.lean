/-
Lean-first (no Rocq counterpart).

# The harness's package initialization (#33 S4)

`examples/raft/antithesis` (`harness.go`, `main.go`) has no package-level variable, so its package
fact is `True`; the packages it imports have theirs (Perennial's; raft's, `raftpb`'s and protobuf's,
`Proof/go_etcd_io/raft/v3/Base.lean`; the checker's, `check/Base.lean`), as the trace check's
`tracecheck/Base.lean`.
-/
module

public import Proof.go_etcd_io.raft.v3.Base
public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Base
public import Perennial.Proof.github_com.goose_lang.primitive.Base
public import Perennial.Proof.strconv.Base
public import Perennial.Proof.time.Base
public import Perennial.Proof.sync.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.mit_pdos.etcd_grove.examples.raft.antithesis

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis :=
  build_get_is_pkg_init_wf

end init

end github_com.mit_pdos.etcd_grove.examples.raft.antithesis

end Perennial
