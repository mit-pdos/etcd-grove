/-
`clientv3.NewMaintenance(c)` (`client/v3`, names only; item 5: `newClient` calls it). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvClientNew

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `NewMaintenance(c)` of a client `New` builds (its connection, call options, configuration and
logger, read-only: `clientCoreAt`): a fresh `*maintenance` (`api := &maintenance{...}; return api`,
`maintenance.go:114`), which `New` stores in the client's `Maintenance` field. (Sweep repairs 1, B5,
2026-11-08: until then some value; `CheckClient`'s guard, `checkClientOk`, names it.) -/
abbrev NewMaintenance.spec : Prop :=
  ∀ (c : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientCoreAt c }}
    (App (Val (@! go_etcd_io.etcd.client.v3.NewMaintenance)) (Val #c))
  {{ (v : GoInterface), RET #v; ⌜∃ mp : Loc, mp ≠ null ∧
      v = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.maintenance.ty) #mp⌝ }}

end spec

end EtcdGrove
end Perennial
