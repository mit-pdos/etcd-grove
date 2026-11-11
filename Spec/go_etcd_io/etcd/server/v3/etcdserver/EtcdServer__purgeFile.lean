/-
`(*EtcdServer).purgeFile()` (`server.go`): the trust boundary (names-only; one of the goroutines `Start`
attaches). Lean-first (the request path's unit 4c).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReadOn

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

/-- `s.purgeFile()` returns (names-only: until `stopping` is closed it purges old WAL files, if
`MaxWALFiles > 0`). (Sweep repairs 1, R1-3, 2026-11-08: the fork's `purgeFile` no longer purges
`.snap.db` files, a4d2bb172, `nonissues/etcd-purge-snapdb-unopened.md`; until then it removed the
oldest beyond five, `.snap.db` files `snapDirInv` keeps, and this triple was false next to it. The
WAL purge's right, `walPurgeRight`, is sweep repairs 1's W1, not yet here.) It reads `s.Logger()` and logs through it (`PurgeFileWithoutFlock`'s
`lg.Info`), and `s.stopping`: its premise is the server's read-side fields (`isServerReadM`, whose
`srvReadFieldsAtM` holds `zapLoggerOk` of `s.lg`; premise fixes 6, family axiom #23: until then
nothing on `s`). -/
abbrev EtcdServer.purgeFile.spec : Prop :=
  ∀ (on : Bool) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReadM on s E γr }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"purgeFile")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
