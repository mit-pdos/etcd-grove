/-
`Close` (the backend). `b.Close()`, with all of the clients' open token: the `run` goroutine stopped (its
`CommitAndStop`), then bbolt's database closed. Stated at `HasLC.hasLC` (Perennial's broadcast
channels are), with the stop channels `isStopChans` (`InvStop.lean`, which `New` gives with
`isBackend`) (2026-10-13: the stop protocol; it was over `isBackend` alone, at any `hlc`).
Lean-first (no Rocq counterpart); see `InvBackend.lean` and `notes/decisions.md`, "The backend:
the buffers, bbolt as a key-value contract, the locks and the views".
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvStop

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend backend

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `b.Close()`, with all of the clients' open token: the `run` goroutine stopped (its
`CommitAndStop`), then bbolt's database closed. -/
abbrev backend.backend.Close.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (WR : IProp GF) (b : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P WR b ∗ isStopChans γ b ∗
      bOpen γ 1 }}
    (App (Val (b @!! go.GoType.PointerType backend.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err; True }}

end spec

end EtcdGrove
end Perennial
