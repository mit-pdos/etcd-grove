/-
`(*EtcdServer).purgeFile()` (`server.go:608-625`; one of the goroutines `Start` attaches). Lean-first (the
request path's unit 4c; with its body since wal-link L2, 2026-11-17, `notes/wal-link-scope.md` §1 #9: until
then an axiom). Proved in `Proof/.../etcdserver/EtcdServer__purgeFile.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvGoAttach
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer

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

/-- `s.purgeFile()` returns, once `s.stopping` is closed, under a configuration that purges no WAL file
(`s.Cfg.MaxWALFiles` zero, read-only: `srvMonitorsOff`'s; no example sets it, `notes/wal-link-scope.md`
C7): it starts no purge, takes `s.Logger()` (an `lgMu` reader slot borrowed from `GoAttach`'s pool,
`raftPool` in `srvGoAttachOk`, with its goroutine's level-1 token, and given back), and waits on a nil
channel (never ready) and `s.stopping`. Over `GoAttach`'s protocol (the logger, the `stopping` channel,
the pool) and its goroutine's thread tokens, given back.

(Sweep repairs 1, R1-3, 2026-11-08: the fork's `purgeFile` no longer purges `.snap.db` files, a4d2bb172,
`nonissues/etcd-purge-snapdb-unopened.md`.) Until wal-link L2 an axiom over `isServerReadM` (premise
fixes 6, family axiom #23). A configuration that purges WAL files is wal-link L6. -/
abbrev EtcdServer.purgeFile.spec : Prop :=
  ∀ (s : Loc) (γg : GoNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvGoAttachOk s γg ∗ srvCfgFieldAddr s go!"MaxWALFiles" ↦□ (W64 0) ∗ threadTokFrom 1 }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"purgeFile")) (Val #()))
  {{ RET #(); threadTokFrom 1 }}

end spec

end EtcdGrove
end Perennial
