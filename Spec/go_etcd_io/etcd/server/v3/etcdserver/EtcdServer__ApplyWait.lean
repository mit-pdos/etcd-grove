/-
`s.ApplyWait()` (`interface.go`). Lean-first (no Rocq counterpart); the request path's unit 4b
(2026-10-13): a method of the read loop's `server` interface (`read/Inv.lean`, `isReadServer`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRead

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.ApplyWait(d)`: `s.applyWait.Wait(d)`, over the `WaitTime`'s contract (`isWaitTime`). -/
abbrev EtcdServer.ApplyWait.spec : Prop :=
  ∀ (s : Loc) (wt : GoInterface) (P : w64 → IProp GF) (d : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvApplyWaitAddr s ↦□ wt ∗ isWaitTime wt P }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"ApplyWait")) (Val #d))
  {{ (ch : Loc), RET #ch; ∃ Q : IProp GF, waitBcast ch Q ∗ □ (Q -∗ P d) }}

end spec

end EtcdGrove
end Perennial
