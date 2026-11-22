/- Lean-first (no Rocq counterpart).

`r.contents()` (`examples/raft/kvnet/replica.go`): under `mu`, a fresh copy `m` of the store's map
(the lock's half of it, `repShared`: every value fits a reply frame, `MapFits`), the applied index and
the configuration's pointer (read-only, `csOpt`). What `Node.status` reports.
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

attribute [local instance] kdStorageModel

/-- See the file header. -/
abbrev Replica.contents.spec : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (id : w64) (r : Loc),
  {{ isRep (GF := GF) γ vs dir id r }}
    (App (Val (r @!! go.GoType.PointerType kReplicaTy @!! go!"contents")) (Val #()))
  {{ (m : Loc) (idx : w64) (csp : Loc), RET (PairV (PairV #m #idx) #csp);
      ∃ (M : GMap (List w8) (List w8)) (c : ConfStateM), m ↦$ M ∗ ⌜MapFits M⌝ ∗
        csOpt csp DFrac.discard c }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
