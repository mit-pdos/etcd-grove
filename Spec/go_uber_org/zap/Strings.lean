/-
`zap.Strings` (`go.uber.org/zap` is names-only): the trust boundary, as `zap.String`. The auth
plan's S4 (2026-10-24): the admin side logs a user's roles. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_uber_org

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `zap.Strings(k, v)` returns a field. -/
abbrev zap.Strings.spec : Prop :=
  ∀ (k : GoString) (v : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap }}
    (App (App (Val (@! zap.Strings)) (Val #k)) (Val #v))
  {{ (f : zap.zapcore.Field), RET #f; True }}

end spec

end EtcdGrove
end Perennial
