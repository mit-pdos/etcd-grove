/-
`config.ServerConfig.BackendPath` (`config.go`: `datadir.ToBackendFileName(c.DataDir)`; names
only). The trust boundary (D22 S-f, 2026-10-19; an axiom in
`Proof/go_etcd_io/etcd/server/v3/config/ServerConfig__BackendPath.lean`). Lean-first (no Rocq
counterpart); the vocabulary is `Proof/go_etcd_io/etcd/server/v3/config/Defs.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.config.Defs
public import GeneratedProof.go_etcd_io.etcd.server.v3.config

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

/-- `c.BackendPath()` (`c.DataDir` read, at any fraction): `backendPathOf c.DataDir`. -/
abbrev config.ServerConfig.BackendPath.spec : Prop :=
  ∀ (c : Loc) (dq : DFrac) (d : GoString),
  {{ (structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"DataDir" c ↦{dq} d : IProp GF) }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.config.ServerConfig.ty @!!
      go!"BackendPath")) (Val #()))
  {{ RET #(config.backendPathOf d);
      structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"DataDir" c ↦{dq} d }}

end spec

end EtcdGrove
end Perennial
