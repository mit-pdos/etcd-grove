/-
`s.Cleanup()` (`server/etcdserver/server.go`; the restart plan's R2b-3c part 2b, 2026-11-04): the
shutdown's closes, after `run`'s loop, the scheduler, the server's goroutines and the raft node have
stopped: the lessor's loop, the KV store, the auth store, the backend (under `bemu`'s write side),
the compactor. Lean-first (no Rocq counterpart); `notes/restart-plan.md`, "R2b-3c, part 2b".
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRun
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorBackend
public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.WsCloserR
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
* the watchable store `wsl` (`s.kv`), with its closer by the mode (`wsCloserM`, what
  `watchableStore.Close` takes);
* the auth store `stl` (`s.authStore`), with the token provider's admin share (`tpAdmin`, given
  back): `authStore.Close`, whose error `Cleanup` ignores;
* the backend `d` (`s.be`): a reader slot of `bemu` (its `Lock` takes it, `Unlock` gives it back),
  the apply side's half of `s.be` and quarter of `bemu`'s ghost variable (which name `d` under the
  lock), its stop channels at the client resources `W`, `Pk` and the clients' whole open token:
  `backend.Close`, whose post `Cleanup` passes on (the data `D` the stop's commit left, what the
  stopped batch lock held at it, `bStopView`, and the file holding `D`, or bbolt's close error);
* the compactor (`s.compactor`), nil or with its contract (`compactorOk`, whose `Stop` needs
  nothing). -/
abbrev EtcdServer.Cleanup.spec : Prop :=
  ∀ (s lp wsl st : Loc) (γw : mvcc.WsNames) (c : Int) (stl : Loc) (R : IProp GF)
    (M : auth.AuthMode) (γbe : GName) (d : mvcc.KBReal) (W Pk : IProp GF) (cp : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvLessorAddr s ↦□ lease.lessorIface lp ∗ lease.lessorStopTok lp ∗
      srvKVAddr s ↦□ (interface.mkOk (go.GoType.PointerType
        go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #wsl : GoInterface) ∗
      mvcc.isWatchableStore wsl st γw ∗ mvcc.wsCloserM wsl st γw.st c ∗
      srvAuthStoreAddr s ↦□ auth.authIface stl ∗ auth.authInv stl R M ∗ auth.tpAdmin stl M ∗
      srvBemuReaderAt s γbe ∗ srvBeAddr s ↦{DFrac.own (1 : Qp).half} srvBeIface d.be ∗
      dghostVar γbe (DFrac.own (1 : Qp).half.half) d ∗
      backend.isBackend d.γB d.P W Pk d.be ∗ backend.isStopChans d.γB d.P W Pk d.be ∗
      backend.bOpen d.γB 1 ∗
      srvCompactorAddr s ↦□ cp ∗ compactorOk cp }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Cleanup")) (Val #()))
  {{ RET #(); auth.tpAdmin stl M ∗
      srvBemuReaderAt s γbe ∗ srvBeAddr s ↦{DFrac.own (1 : Qp).half} srvBeIface d.be ∗
      dghostVar γbe (DFrac.own (1 : Qp).half.half) d ∗
      ∃ D : backend.Data, backend.bStopView d.γB d.P W Pk D ∗
        ((∃ path : GoString, backend.bFile d.γB path ∗ backend.fileHolds path D) ∨
          ⌜¬ backend.dbCloseOk⌝) }}

end spec

end EtcdGrove
end Perennial
