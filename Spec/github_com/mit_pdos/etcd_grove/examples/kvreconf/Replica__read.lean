/- Lean-first (no Rocq counterpart).

`r.read(key, timeout)` (kv.go): a read of `key` by a read index here, waiting up to `timeout`.
With `ok`, the value is `key`'s in a history at least `L0`, the client's lower bound when the read
started (linearizable: `readCtx_commit_after`).
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
abbrev Replica.read.spec : Prop :=
  ∀ (γr : RNames) (vs : List w64) (id : w64) (r : Loc) (key : List w8) (tmo : time.Duration)
    (L0 : List (List w8)),
  (key.length : Int) < 2 ^ 61 →
  {{ isRep γr vs id r ∗ kvLb γr L0 }}
    (App (App (Val (r @!! go.GoType.PointerType rReplicaTy @!! go!"read")) (Val #key)) (Val #tmo))
  {{ (v : List w8) (ok : Bool), RET (PairV #v #ok);
      if ok then iprop(∃ L, kvLb γr L ∗ ⌜L0 <+: L ∧ v = kvFold L key⌝) else iprop(True) }}

end spec

end kvreconf
end EtcdGrove
end Perennial
