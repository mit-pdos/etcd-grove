/-
`(*lessor).findDueScheduledCheckpoints(limit)` (`server/lease/lessor.go:770-809`). Lean-first;
prove-ps2-newlessor3, 2026-11-21.
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- `le.findDueScheduledCheckpoints(limit)` with no checkpointer (`le.cp` nil: `lessorExtra`;
`NewLessor` installs none): `nil` (`lessor.go:771-773`). -/
abbrev lease.lessor.findDueScheduledCheckpoints.spec : Prop :=
  ∀ (lp : Loc) (dq : DFrac) (limit : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ lF go!"cp" lp ↦{dq} func.nil }}
    (App (Val (lp @!! go.GoType.PointerType lessor.ty @!! go!"findDueScheduledCheckpoints")) (Val #limit))
  {{ RET #(slice.nil : GoSlice); lF go!"cp" lp ↦{dq} func.nil }}

end spec

end EtcdGrove
end Perennial
