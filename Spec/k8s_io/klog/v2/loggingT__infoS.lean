/-
`logging.infoS(logger, filter, depth, msg, keysAndValues...)` (klog v2.140.0, `klog.go:822-831`),
on klog's global `logging`: with no logger and no filter, `printS(nil, InfoLog, depth+1, ...)`.
Proved over its translated body (`Proof/k8s_io/klog/v2/loggingT__infoS.lean`; klog-infos,
2026-11-23, etcd-grove#25). The keys and values are `klog.infoSArgOk` (what the trusted serializer
follows); their slice, read at any fraction, comes back. Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.klog.v2.KVArgs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev klog.loggingT.infoS.spec : Prop :=
  ∀ (logger : Loc) (filter : GoInterface) (depth : w64) (msg : GoString) (args : GoSlice)
    (xs : List GoInterface) (dq : DFrac),
  (∀ x ∈ xs, klog.infoSArgOk x) → (msg.length : Int) ≤ maxAddr →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.klog.v2 ∗
      ⌜logger = null ∧ filter = interface.nil⌝ ∗ args ↦*{dq} xs }}
    (App (App (App (App (App
      (Val (globalAddr k8s_io.klog.v2.logging @!! go.GoType.PointerType k8s_io.klog.v2.loggingT.ty
        @!! go!"infoS"))
      (Val #logger)) (Val #filter)) (Val #depth)) (Val #msg)) (Val #args))
  {{ RET #(); args ↦*{dq} xs }}

end spec

end EtcdGrove
end Perennial
