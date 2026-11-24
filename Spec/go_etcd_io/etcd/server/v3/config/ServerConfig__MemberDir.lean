/-
`config.ServerConfig.MemberDir` (`config.go:300`: `datadir.ToMemberDir(c.DataDir)`; claim #34, stage 3,
2026-11-23: translated with its body, `bootstrap`'s callee). Lean-first; proved in
`Proof/go_etcd_io/etcd/server/v3/config/ServerConfig__MemberDir.lean` over `datadir.ToMemberDir`'s.
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

/-- `c.MemberDir()` (`c.DataDir` read, at any fraction): Go's `filepath.Join(DataDir, "member")`
(`path.joinModel`, `datadir.ToMemberDir`'s), for a data directory shorter than `2^60` bytes
(`filepath.Join`'s premise), with the package's initialization. -/
abbrev config.ServerConfig.MemberDir.spec : Prop :=
  ∀ (c : Loc) (dq : DFrac) (d : GoString), d.length < 2 ^ 60 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.config ∗
      (structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"DataDir" c ↦{dq} d : IProp GF) }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.config.ServerConfig.ty @!!
      go!"MemberDir")) (Val #()))
  {{ RET #(path.joinModel [d, go!"member"]);
      structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"DataDir" c ↦{dq} d }}

end spec

end EtcdGrove
end Perennial
