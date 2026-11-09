/-
`concurrency.mkSTM(c, opts)` (`client/v3/concurrency/stm.go`), internal.

Users: `NewSTM`.

Proof sketch: by the level: a `*stmSerializable` (prefetch map allocated) with the conflicts
closure of its level (`SerializableSnapshot`: `readSet.cmps` and `writeSet.cmps(first() + 1)`;
`Serializable`: `readSet.cmps`), or a `*stm` with `WithSerializable()` reads (`RepeatableReads`:
`readSet.cmps`; `ReadCommitted`: none); the read set and write set `nil` until `reset`
(`stmStale`). `stmStale`'s realization holds the read permission (`etcdPerm γ T`, `T` reflexive)
and the methods' specs (`stm__*`, `stmSerializable__*`).

Changes: from `specs-ref`'s `mkSTM.lean`: over `stmStale`; any context.

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Concurrency

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- `mkSTM(c, opts)`: an STM of the options' level (valid: it panics otherwise), between attempts. -/
def mkSTM.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal) (op : Loc)
    (ov : go_etcd_io.etcd.client.v3.concurrency.stmOptions) (T : State → State → Prop),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isClient c γ who ∗ op ↦□ ov ∗ ⌜isoValid ov.iso'⌝ ∗ Context.ctxOk ov.ctx' ∗ ctxPrin ov.ctx' who ∗
      etcdPerm γ T ∗ ⌜effIn readEff T⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.concurrency.mkSTM)) (Val #c)) (Val #op))
  {{ (iv : GoInterface), RET #iv; stmStale iv γ who ov.iso' }}

end spec

end Concurrency
end EtcdGrove
end Perennial
