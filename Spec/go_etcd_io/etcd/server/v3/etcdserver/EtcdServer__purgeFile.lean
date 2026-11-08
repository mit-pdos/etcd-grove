/-
`(*EtcdServer).purgeFile()` (`server.go`): the trust boundary (names-only; one of the goroutines `Start`
attaches). Lean-first (the request path's unit 4c).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier

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
WAL purge's right, `walPurgeRight`, is sweep repairs 1's W1, not yet here.) -/
abbrev EtcdServer.purgeFile.spec : Prop :=
  ∀ (s : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"purgeFile")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
