/-
`SetFinishedCompact` (`store.go`) (2026-10-13, unit 5a).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvCompact

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `SetFinishedCompact(tx, value)`, `value ≥ 0`: its own critical section of the batch lock
(`LockInsideApply`, which runs the post-lock hook `f` on the caller's `Pre`: `{P ∗ Pre} f() {Q}`),
`UnsafeSetFinishedCompact`, `Unlock`; the caller's update, with the lock's resource `W` (the store updates
its record of the meta key there), before the `Unlock`: `Q ∗ W ={⊤}=∗ P ∗ W ∗ Post`. Over the batch
transaction in full generality (question 5's Draft, review round 14's F6, R9-3; the core stage, part
(1)): its read and write tokens `RT`/`WT` (lent to `LockInsideApply`, the read token given back),
put condition, tracked buckets' right and the compaction keys' write right `MW` are the caller's, and
the caller's swap of the lock's resource for that right (`mwSwap W MW`: the store's, from its write
right's invariant) gives the right for the `Meta` put. -/
abbrev mvcc.SetFinishedCompact.spec : Prop :=
  ∀ (bt : GoInterfaceOk) (View : Qp → mvcc.Bucket → IProp GF) (RT WT : IProp GF)
    (PutOk : mvcc.Bucket → mvcc.Puts → GoString → GoString → Prop) (Del : GoString → IProp GF)
    (W Dep : IProp GF) (Locked : mvcc.Puts → IProp GF) (P : IProp GF) (HF : val → IProp GF)
    (Rb : GMap GoString backend.BktData → IProp GF) (MW : IProp GF) (f : val) (value : w64)
    (Pre Q Post : IProp GF),
  0 ≤ sint.Z value →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.batchTxSpecG bt View RT WT PutOk Del W Dep True Locked P HF Rb MW ∗ mvcc.mwSwap W MW ∗
      RT ∗ WT ∗ HF f ∗ Pre ∗
      □ ({{ P ∗ Pre }} (App (Val f) (Val #())) {{ RET #(); Q }}) ∗ (Q ∗ W ={⊤}=∗ P ∗ W ∗ Post) }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.SetFinishedCompact)) (Val #(GoInterface.ok bt)))
      (Val #value))
  {{ RET #(); RT ∗ Post }}

end spec

end EtcdGrove
end Perennial
