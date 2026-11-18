/- Lean-first (no Rocq counterpart).

`MainConfig(prefix)` (`examples/mvccfull/config.go`): `Main`'s configuration
(`mainConfigM`), its `Mix`'s seven weight slices fresh (owned, `mainMixOwn`), at the code's weights
(the read weights `[1, 1, 2, 1, 1, 0]`: no hash reads until F2).
-/
module

public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.mvccfull
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccfull

section model
variable [GooseExts]

/-- `MainConfig(prefix)` with the `Mix` `mx` (whose slices `mainMixOwn` gives). -/
def mainConfigM (pfx : GoString) (mx : Mix) : Config :=
  { Prefix' := pfx, Ops' := W64 12000, Depth' := W64 4, MaxVal' := W64 5000, Readers' := W64 2,
    Reads' := W64 4000, Streams' := W64 2, Watchers' := W64 64, BatchLimit' := W64 3,
    BatchInterval' := W64 0, CompactionBatchLimit' := W64 2, CompactionSleep' := W64 1000,
    Mix' := mx }

end model

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]

end spec

end mvccfull
end EtcdGrove
end Perennial
