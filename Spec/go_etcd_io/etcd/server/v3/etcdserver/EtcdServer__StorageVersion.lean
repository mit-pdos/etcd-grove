/-
`(*EtcdServer).StorageVersion()` (`server.go`), translated with its body: etcd PR #22190's
verification (`notes/pr-verify/etcd-22190.md`; names-only before). Lean-first; see
`InvBackendLife.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBackendLife

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

/-- `s.StorageVersion()`, by a goroutine with a reader slot of `s.bemu`, the logger, and a view
`cl` of the `stopping` channel (any time after `start`, concurrently with `Cleanup`): it reads the
backend only while it is open (`DetectSchemaVersion`'s contract needs a fraction of the backend's
open token, `InvBackendLife.lean`) and returns `nil` or a fresh version; `nil` if the caller
knows `stopping` closed. The caller gets its slot and its view back. -/
abbrev EtcdServer.StorageVersion.spec : Prop :=
  ∀ (s l ch : Loc) (γ : ChanNames) (cl : Broadcast),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvBemuReader s ∗ srvLgAddr s ↦□ l ∗ ⌜l ≠ null⌝ ∗
      srvStoppingAddr s ↦□ ch ∗ ownStopChan ch γ iprop(True) cl }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"StorageVersion")) (Val #()))
  {{ (v : Loc), RET #v; srvBemuReader s ∗ ownStopChan ch γ iprop(True) cl ∗
      ⌜cl = .Done → v = null⌝ ∗
      (⌜v = null⌝ ∨ ∃ sv : github_com.Masterminds.semver.v3.Version, v ↦ sv) }}

end spec

end EtcdGrove
end Perennial
