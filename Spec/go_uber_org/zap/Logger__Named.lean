/-
zap's `(*Logger).Named(s)` (zap v1.28.0 `logger.go`: `s == ""` returns the logger, otherwise a clone with
the name `s`, or `name + "." + s`). Claim #34, stage 4 (2026-11-25; `raftConfig`'s
`cfg.Logger.Named("raft")`). Lean-first.

**Not proved: a hypothesis** (`?` in the server's `Link.lean`): `Named` is names-only in zap's
translation (`Code/go_uber_org/zap.toml`). It holds of Go: the clone (`log.clone()`, a copy of the
`Logger` struct, translated) keeps the core, the development flag, the caller flag, the terminal hooks and
the clock, and only its `name` is written, before it is returned, so the clone is a logger as `NewNop`
builds it (`zapLoggerOk`) when `lg` is.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import GeneratedProof.go_uber_org.zap
public import Spec.go_uber_org.zap.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_uber_org

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev zap.Logger.Named.spec : Prop :=
  ∀ (l : Loc) (s : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap ∗ zapLoggerOk l }}
    (App (Val (l @!! go.GoType.PointerType zap.Logger.ty @!! go!"Named")) (Val #s))
  {{ (l' : Loc), RET #l'; zapLoggerOk l' }}

end spec

end EtcdGrove
end Perennial
