/-
`(*EtcdServer).Cleanup()` (`server.go`; the last step of `run`'s shutdown before `close(s.done)`),
translated with its body: etcd PR #22190's verification (`notes/pr-verify/etcd-22190.md`; until
then names-only, an axiom with no precondition). Lean-first; see `InvBackendLife.lean`.
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

/-- `s.Cleanup()`, with what it needs (`srvCleanupRes`: a reader slot of `bemu`, the closer's
flag, the apply thread's half of `s.be`, the other fields' `Stop`/`Close` contracts) and the
done view of `stopping` (closed before): stops the lessor, closes the KV and the auth store,
closes the backend under `bemu`'s write lock (with all of its open token: no reader holds a
fraction), leaving it shut, and stops the compactor. -/
abbrev EtcdServer.Cleanup.spec : Prop :=
  ∀ (s ch : Loc) (γ : ChanNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvCleanupRes s ∗ srvStoppingAddr s ↦□ ch ∗ ownStopChan ch γ iprop(True) .Done }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Cleanup")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
