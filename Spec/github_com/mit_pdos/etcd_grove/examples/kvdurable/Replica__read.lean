/- Lean-first (no Rocq counterpart).

`r.read(key, timeout)` (kv.go): kvreconf's, with the read's sequence number from the cluster's
`readSeqs` (`readSeqs.next`, which mints the read's context at `(id, seq)`): a linearizable read by a
read index; `ok` false if no answer came (or the numbers are used up).
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
abbrev Replica.read.spec : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (id : w64) (r n st sts sq ms : Loc)
    (γs : MemStorNames) (ph : GName) (key : List w8) (tmo : time.Duration) (L0 : List (List w8)),
  (key.length : Int) < 2 ^ 61 →
  {{ isReplica γ vs dir id r n st sts sq ms γs ph ∗ kvLb γ L0 }}
    (App (App (Val (r @!! go.GoType.PointerType kReplicaTy @!! go!"read")) (Val #key)) (Val #tmo))
  {{ (v : List w8) (ok : Bool), RET (PairV #v #ok);
      if ok then iprop(∃ L, kvLb γ L ∗ ⌜L0 <+: L ∧ v = kvreconf.kvFold L key⌝) else iprop(True) }}

end spec

end kvdurable
end EtcdGrove
end Perennial
