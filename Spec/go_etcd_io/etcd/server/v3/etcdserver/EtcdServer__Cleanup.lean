/-
`s.Cleanup()` (`server/etcdserver/server.go`; the restart plan's R2b-3c part 2b, 2026-11-04): the
shutdown's closes, after `run`'s loop, the scheduler, the server's goroutines and the raft node have
stopped: the lessor's loop, the KV store, the auth store, the backend (under `bemu`'s write side),
the compactor. Lean-first (no Rocq counterpart); `notes/restart-plan.md`, "R2b-3c, part 2b".
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRun
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapRO
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorBackend
public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.EtcdBackend
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvStop

@[expose] public section

set_option linter.unusedSectionVars false

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

/-- **`s.Cleanup()`** of a server whose apply thread and raft node have stopped, from the right to
close each of what it closes (`server.go`'s `Cleanup`; each field's `nil` check is passed):
* the lessor `lp` (`s.lessor`), with the right to stop it once (`lessorStopTok`, `NewLessor`'s):
  `lessor.Stop`;
* the store (`s.kv`, a handle `kv` of mvcc's API at `γ`), with its open token (`mvccOpen`, what
  `KV.Close.contract` takes; the `lean` merge, 2026-11-06: until then the watchable store's
  internal closer `mvcc.wsCloserM`);
* the auth store `stl` (`s.authStore`), with a closer of it at a resource `K`, given back
  (`authCloser`; R2b-3d stage 5b, 2026-11-05: with auth off, `NewAuthStore`'s `authCloseOk`, `K`
  empty; with auth on, `authStore.Close`'s proof at the token provider's admin share; until then
  the store's invariant and that share): `authStore.Close`, whose error `Cleanup` ignores;
* the backend `d` (`s.be`): a reader slot of `bemu` (its `Lock` takes it, `Unlock` gives it back),
  the apply side's half of `s.be` and a part of `bemu`'s ghost variable (which name `d` under the
  lock; any fraction `dq`, H2, 2026-11-05: the shutdown keeps a part of the apply thread's quarter
  in the write budget, `stop_monitorRT`; until then the quarter), its stop channels at the client resources `W`, `Pk` and the clients' whole open token
  (R2b-3d stage 5c, 2026-11-05: as an update from what `kv.Close` gives back, gap 4's census;
  until then `bOpen 1` up front, which the stop could not give: the loops hold their readers until
  `kv.Close`. The `lean` merge, 2026-11-06, the reader tokens: the update takes the closed store
  `mvccClosed γ`, every reader token of the store, `mvccReaders γ mvccReaderN`, which the caller
  holds, so that no read of the store is in flight when the backend closes, and a share of the
  store's backend, as `mvccClosed_rest.law`; until then from `mvcc.wsCloseRes`, the loops' store
  readers and the compaction job's resource, the caller retiring every other store reader; R6,
  2026-11-07: the update gives the store's backend share back, and `Cleanup` returns it, for the
  stopped backend's image, `mvccImage_stop.law`):
  `backend.Close`, whose post `Cleanup`
  passes on (the data `D` the stop's commit left, what the
  stopped batch lock held at it, `bStopView`, and the file holding `D`, or bbolt's close error);
* the compactor (`s.compactor`), nil or with its contract (`compactorOk`, whose `Stop` needs
  nothing). -/
abbrev EtcdServer.Cleanup.spec : Prop :=
  ∀ (s lp : Loc) (kv : GoInterface) (γ : mvcc.api.MvccName) (q : Qp) (Pkm : IProp GF) (stl : Loc)
    (K : IProp GF) (γbe : GName) (d : mvcc.KBReal) (dq : DFrac) (W Pk : IProp GF) (cp : GoInterface)
    (X Y : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvLessorAddr s ↦□ lease.lessorIface lp ∗ lease.lessorStopTok lp ∗
      srvKVAddr s ↦□ kv ∗ mvcc.api.isMvcc kv γ ∗ mvcc.api.mvccOpen γ ∗
      mvcc.api.mvccReaders γ mvcc.api.mvccReaderN ∗
      mvcc.api.mvccBackend γ q (mvcc.api.etcdStorage d) Pkm ∗
      srvAuthStoreAddr s ↦□ auth.authIface stl ∗ authCloser stl K ∗ K ∗
      srvBemuReaderAt s γbe ∗ srvBeAddr s ↦{DFrac.own (1 : Qp).half} srvBeIface d.be ∗
      dghostVar γbe dq (bkKey d) ∗
      backend.isBackend d.γB d.P W Pk d.be ∗ backend.isStopChans d.γB d.P W Pk d.be ∗
      (mvcc.api.mvccClosed γ ∗ mvcc.api.mvccReaders γ mvcc.api.mvccReaderN ∗
        mvcc.api.mvccBackend γ q (mvcc.api.etcdStorage d) Pkm ={⊤}=∗
        backend.bOpen d.γB 1 ∗ mvcc.api.mvccBackend γ q (mvcc.api.etcdStorage d) Pkm) ∗
      -- (2026-11-04, R2b-3d stage 3) a request `X ⇒ Y` of the backend's stop commit
      X ∗ backend.commitReq d.γB d.P Pk d.be X Y ∗
      srvCompactorAddr s ↦□ cp ∗ compactorOk cp }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Cleanup")) (Val #()))
  {{ RET #(); K ∗ mvcc.api.mvccBackend γ q (mvcc.api.etcdStorage d) Pkm ∗
      srvBemuReaderAt s γbe ∗ srvBeAddr s ↦{DFrac.own (1 : Qp).half} srvBeIface d.be ∗
      dghostVar γbe dq (bkKey d) ∗ Y ∗
      ∃ D : backend.Data, backend.bStopView d.γB d.P W Pk D ∗
        ((∃ path : GoString, backend.bFile d.γB path ∗ backend.fileHolds path D) ∨
          ⌜¬ backend.dbCloseOk⌝) }}

end spec

end EtcdGrove
end Perennial
