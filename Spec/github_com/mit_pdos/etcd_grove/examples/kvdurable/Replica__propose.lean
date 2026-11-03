/- Lean-first (no Rocq counterpart). kvreconf's.

`r.propose(op, timeout)` (kv.go): the operation of datum `d` (minted, its slot registered in the
store's invariant: `d ↪[γ.r.ops]□ γp`) proposed here, waiting up to `timeout`. With `ok`, `v` is
`d`'s answer in a committed log's history (`waitP`): the slot's answer, which `Cluster.do` collects.
The proposal's atomic update is persistent (raft may commit a duplicated `MsgProp` again:
`γ.dup = true`), built from the store's invariant (`kd_propAu`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

/-- See the file header. -/
abbrev Replica.propose.spec : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (id : w64) (r : Loc) (d : List w8)
    (γp : GName × GName) (opsl : GoSlice) (tmo : time.Duration),
  {{ isRep γ vs dir id r ∗ d ↪[γ.r.ops]□ γp ∗ ownSlice opsl d DFrac.discard }}
    (App (App (Val (r @!! go.GoType.PointerType kReplicaTy @!! go!"propose")) (Val #opsl)) (Val #tmo))
  {{ (v : List w8) (ok : Bool), RET (PairV #v #ok); if ok then waitP γ d v else iprop(True) }}

end spec

end kvdurable
end EtcdGrove
end Perennial
