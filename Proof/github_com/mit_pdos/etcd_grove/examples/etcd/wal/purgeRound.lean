module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.purgeRound

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt absDiskExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

/-- The trust boundary: `purgeRound` is names-only (WAL W4c, decision Q2); see its spec's
docstring for why Go's round does what the spec says, and `PurgeBody.lean` for its body over the
abstract disk's `"WalPurge"` step. -/
axiom purgeRound.wp_proof : purgeRound.spec (GF := GF) (hG := hG)

end proof

end etcd_wal
end EtcdGrove
end Perennial
