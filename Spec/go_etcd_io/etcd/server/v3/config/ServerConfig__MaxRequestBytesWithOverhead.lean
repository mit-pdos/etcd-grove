/-
`config.ServerConfig.MaxRequestBytesWithOverhead` (`config.go`: `MaxRequestBytes + grpcOverheadBytes`).
Lean-first (no Rocq counterpart); the watch slice's unit W-S (2026-10-14).
-/
module

-- `InvServer`'s `ServerConfig` `TypeRepr` instances (as `ServerConfig__ReqTimeout.lean`)
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvServer

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `c.MaxRequestBytesWithOverhead()` (the field read-only): the budget plus `512 * 1024`
(wrapping, as Go's `uint` addition). -/
abbrev config.ServerConfig.MaxRequestBytesWithOverhead.spec : Prop :=
  ∀ (c : Loc) (m : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.config ∗
      structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"MaxRequestBytes" c ↦□ m }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.config.ServerConfig.ty @!!
      go!"MaxRequestBytesWithOverhead")) (Val #()))
  {{ RET #(m + W64 (512 * 1024)); True }}

end spec

end EtcdGrove
end Perennial
