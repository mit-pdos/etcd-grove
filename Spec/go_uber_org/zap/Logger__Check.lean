/-
`zap.Logger.Check`: the trust boundary (`go.uber.org/zap` is names-only). Lean-first (no Rocq
counterpart); the auth plan's S5 (2026-10-24: `auth.authStore.Authenticate` logs through it).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import GeneratedProof.go_uber_org.zap

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

/-- `l.Check(lvl, msg)` (a non-nil logger, any level) returns a `*zapcore.CheckedEntry`: `nil` if
the level is not enabled, else an entry to write (logging has no effect here). -/
abbrev zap.Logger.Check.spec : Prop :=
  ∀ (l : Loc) (lvl : val) (msg : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap ∗ ⌜l ≠ null⌝ }}
    (App (App (Val (l @!! go.GoType.PointerType zap.Logger.ty @!! go!"Check")) (Val lvl)) (Val #msg))
  {{ (ce : Loc), RET #ce; True }}

end spec

end EtcdGrove
end Perennial
