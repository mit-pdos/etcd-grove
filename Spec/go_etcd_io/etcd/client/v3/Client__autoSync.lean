/-
`c.autoSync()` (`client/v3/client.go`; item 5: `newClient`'s goroutine). Lean-first (no Rocq
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `c.autoSync()` with no auto-sync interval (the configuration `cfg`, read-only): returns. -/
abbrev Client.autoSync.spec : Prop :=
  ∀ (c : Loc) (cfg : go_etcd_io.etcd.client.v3.Config),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientF c go!"cfg" ↦□ cfg ∗
      ⌜cfg.AutoSyncInterval' = W64 0⌝ }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"autoSync")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
