/-
`config.ServerConfig.SnapDir` (`config.go:309`: `filepath.Join(c.MemberDir(), "snap")`; claim #34,
stage 3, 2026-11-23: translated with its body, `bootstrapSnapshot`'s callee). Lean-first; proved in
`Proof/go_etcd_io/etcd/server/v3/config/ServerConfig__SnapDir.lean` over `MemberDir`'s and
`filepath.Join`'s specs.
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

/-- `c.SnapDir()` (`c.DataDir` read, at any fraction): `config.snapDirOf DataDir`, Go's
`filepath.Join(filepath.Join(DataDir, "member"), "snap")`, which is `filepath.Join(DataDir, "member",
"snap")` (`path.joinModel_triple`), for a data directory shorter than `2^60` bytes. -/
abbrev config.ServerConfig.SnapDir.spec : Prop :=
  ∀ (c : Loc) (dq : DFrac) (d : GoString), d.length < 2 ^ 60 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.config ∗
      (structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"DataDir" c ↦{dq} d : IProp GF) }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.config.ServerConfig.ty @!!
      go!"SnapDir")) (Val #()))
  {{ RET #(config.snapDirOf d);
      structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"DataDir" c ↦{dq} d }}

end spec

end EtcdGrove
end Perennial
