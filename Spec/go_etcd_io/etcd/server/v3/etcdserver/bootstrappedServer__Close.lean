/-
`(*bootstrappedServer).Close()` (`bootstrap.go:159-161`): `s.storage.Close()`. Lean-first (no Rocq
counterpart); stage R-D1, the one-shot `Close` (2026-11-04: until then `bootOk`'s trusted `#Hclose`,
`notes/decisions.md`, "R-D: the bootstrapped record's one-shot Close").
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvStop

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `b.Close()` (`bootstrap.go:159-161`: `b.storage.Close()`), with the record's pointers read-only
and the backend's whole open token (`backend.backend.Close.spec`'s): once (the token is exclusive; a
second call panics on `close(b.stopc)`). It closes only the backend: the WAL (`b.storage.wal.w`)
stays open with its file lock, and none of the three goroutines `NewServer` started before its
error is stopped (raft's `node.run`, the lessor's `runLoop`, the WAL's file pipeline, which keeps
its preallocated `0.tmp` locked: `nonissues/etcd-newserver-error-path-leaks.md`). `NewServer`'s
deferred close on its error paths after `bootstrap` (`server.go:306-310`). (R-D1, 2026-11-04: until
then `bootOk`'s trusted `#Hclose`, a persistent `{{ True }} b.Close() {{ True }}`, false.) -/
abbrev bootstrappedServer.Close.spec : Prop :=
  ∀ (b : Loc) (bs : bootstrappedServer) (sto : bootstrappedStorage) (bk : bootstrappedBackend)
    (γ : backend.BNames) (P : backend.BParams) (W Pk : IProp GF) (be : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      b ↦□ bs ∗ bs.storage' ↦□ sto ∗ sto.backend' ↦□ bk ∗
      ⌜bk.be' = interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #be⌝ ∗
      backend.isBackend γ P W Pk be ∗ backend.isStopChans γ be ∗ backend.bOpen γ 1 }}
    (App (Val (b @!! go.GoType.PointerType bootstrappedServer.ty @!! go!"Close")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
