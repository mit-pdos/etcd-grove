/-
`config.ServerConfig.WALDir` (`config.go:302-307`; claim #34, stage 3, 2026-11-23: translated with its
body, `bootstrap`'s callee). Lean-first; proved in
`Proof/go_etcd_io/etcd/server/v3/config/ServerConfig__WALDir.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.config.Defs
public import GeneratedProof.go_etcd_io.etcd.server.v3.config
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `c.WALDir()` with a dedicated WAL directory (`c.DedicatedWALDir` read, at any fraction, not
empty): that directory (`if c.DedicatedWALDir != "" { return c.DedicatedWALDir }`). The other branch
(`datadir.ToWALDir(c.DataDir)`) is not covered: every configuration `bootstrap`'s contracts cover has
one (`wal.bootRes`: `srvWalDirOf DataDir`). -/
abbrev config.ServerConfig.WALDir.spec : Prop :=
  ∀ (c : Loc) (dq : DFrac) (w : GoString), w ≠ [] →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.config ∗
      (structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"DedicatedWALDir" c ↦{dq} w :
        IProp GF) }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.config.ServerConfig.ty @!!
      go!"WALDir")) (Val #()))
  {{ RET #w;
      structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"DedicatedWALDir" c ↦{dq} w }}

end spec

end EtcdGrove
end Perennial
