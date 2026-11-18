/-
`zap.NewNop`: the trust boundary (`go.uber.org/zap` is names-only). Lean-first (no Rocq counterpart).
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

/-- `zap.NewNop()` returns a zap logger (`zapLoggerOk`: non-nil, as zap's constructors build it;
one that logs nothing). (Sweep repairs 1, R1-2: until then only `l ≠ null`.) -/
abbrev zap.NewNop.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap }}
    (App (Val (@! zap.NewNop)) (Val #()))
  {{ (l : Loc), RET #l; zapLoggerOk l }}

end spec

end EtcdGrove
end Perennial
