/- Lean-first (no Rocq counterpart).

`r.propose(op, timeout)` (kv.go): the operation of datum `d` (minted, its slot registered in the
store's invariant: `d ↪[γr.ops]□ γp`) proposed here, waiting up to `timeout`. With `ok`, `v` is
`d`'s answer in a committed log's history (`waitP`): the slot's answer, which `Cluster.do` collects.
The proposal's atomic update is persistent (raft may commit a duplicated `MsgProp` again:
`γ.dup = true`), built from the store's invariant (`kvr_propAu`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.DefsCluster

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KvrStor GF]

attribute [local instance] kvrStorageModel

/-- See the file header. -/
abbrev Replica.propose.spec : Prop :=
  ∀ (γr : RNames) (vs : List w64) (id : w64) (r : Loc) (d : List w8) (γp : GName × GName)
    (opsl : GoSlice) (tmo : time.Duration),
  {{ isRep γr vs id r ∗ d ↪[γr.ops]□ γp ∗ ownSlice opsl d DFrac.discard }}
    (App (App (Val (r @!! go.GoType.PointerType rReplicaTy @!! go!"propose")) (Val #opsl)) (Val #tmo))
  {{ (v : List w8) (ok : Bool), RET (PairV #v #ok); if ok then waitP γr d v else iprop(True) }}

end spec

end kvreconf
end EtcdGrove
end Perennial
