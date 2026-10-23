/-
`zap.Strings`: the trust boundary (`go.uber.org/zap` is names-only; rafthttp stage 6c, the
transport's `AddPeer`/`AddRemote` logs). Lean-first.
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `zap.Strings(k, ss)` of a slice of strings (read): some field (which refers to the slice; the
logger reads it during the call it is passed to), the slice back. -/
abbrev zap.Strings.spec : Prop :=
  ∀ (k : GoString) (sl : GoSlice) (dq : DFrac) (ss : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap ∗ sl ↦*{dq} ss }}
    (App (App (Val (@! zap.Strings)) (Val #k)) (Val #sl))
  {{ (f : zap.zapcore.Field), RET #f; sl ↦*{dq} ss }}

end spec

end EtcdGrove
end Perennial
