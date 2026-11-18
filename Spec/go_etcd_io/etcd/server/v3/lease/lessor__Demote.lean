/-
`(*lessor).Demote` (`server/lease/lessor.go`). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/lease/InvLessor.lean`. (The lessor-noax stage, 2026-11-18) proved;
until then the trust boundary. Stated at `HasLC.hasLC` (until then at any `hlc`), the instance of
every caller (`LessorOk.lean`): the proof spends a later credit on `demotec`'s close right, kept in
the expiry loop's invariant.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.lease lease

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- `le.Demote()` (write-locked): sets every lease's expiry to `forever`, clears the checkpoint
heap and the expiry notifier, and closes `demotec` if set (and sets it to nil); it touches only
the lessor's memory under its lock. -/
abbrev lease.lessor.Demote.spec : Prop :=
  ∀ (lp : Loc) (γl : GName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ lessorInv lp γl }}
    (App (Val (lp @!! go.GoType.PointerType lessor.ty @!! go!"Demote")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
