/- Lean-first (no Rocq counterpart).

`r.conf()` (kv.go): the replica's configuration (a read-only conf state) and applied index.
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
abbrev Replica.conf.spec : Prop :=
  ∀ (γr : RNames) (vs : List w64) (id : w64) (r : Loc),
  {{ isRep γr vs id r }}
    (App (Val (r @!! go.GoType.PointerType rReplicaTy @!! go!"conf")) (Val #()))
  {{ (csp : Loc) (idx : w64), RET (PairV #csp #idx); ∃ c : ConfStateM, csOpt csp DFrac.discard c }}

end spec

end kvreconf
end EtcdGrove
end Perennial
