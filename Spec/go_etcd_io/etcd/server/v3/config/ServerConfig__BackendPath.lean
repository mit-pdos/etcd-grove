/-
`config.ServerConfig.BackendPath` (`config.go`: `datadir.ToBackendFileName(c.DataDir)`). D22 S-f,
2026-10-19 (until 2026-11-22 names-only and an axiom; bkarea: translated with its body and proved
in `Proof/go_etcd_io/etcd/server/v3/config/ServerConfig__BackendPath.lean` over `datadir`'s).
Lean-first (no Rocq counterpart); the vocabulary is `Proof/go_etcd_io/etcd/server/v3/config/Defs.lean`.
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

/-- `c.BackendPath()` (`c.DataDir` read, at any fraction): `backendPathOf c.DataDir`. (bkarea,
2026-11-22, proving it) For a data directory shorter than `2^60` bytes (`filepath.Join`'s
premise: its elements' lengths sum below `2^62`), with the package's initialization (its import
`datadir`'s, `filepath`'s). -/
abbrev config.ServerConfig.BackendPath.spec : Prop :=
  ∀ (c : Loc) (dq : DFrac) (d : GoString), d.length < 2 ^ 60 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.config ∗
      (structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"DataDir" c ↦{dq} d : IProp GF) }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.config.ServerConfig.ty @!!
      go!"BackendPath")) (Val #()))
  {{ RET #(config.backendPathOf d);
      structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"DataDir" c ↦{dq} d }}

end spec

end EtcdGrove
end Perennial
