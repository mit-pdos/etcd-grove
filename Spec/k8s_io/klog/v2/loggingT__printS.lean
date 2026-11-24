/-
`logging.printS(err, s, depth, msg, keysAndValues...)` (klog v2.140.0, `klog.go:835-854`), on klog's
global `logging`, with no error: the message quoted (`strconv.AppendQuote`) into a buffer from klog's
pool, the keys and values serialized after it (`serialize.FormatKVs`), the buffer printed
(`printDepth`, `fmt.Fprint` of it) and given back to the pool. Proved over its translated body
(`Proof/k8s_io/klog/v2/loggingT__printS.lean`; klog-infos, 2026-11-23, etcd-grove#25). The keys and
values are `klog.infoSArgOk` (with `err`, `errKV` would hold an `error`, which the trusted
serializer does not follow); `s` a valid severity. Lean-first (no Rocq counterpart).
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
abbrev klog.loggingT.printS.spec : Prop :=
  ∀ (err : GoInterface) (s : w32) (depth : w64) (msg : GoString) (args : GoSlice)
    (xs : List GoInterface) (dq : DFrac),
  (∀ x ∈ xs, klog.infoSArgOk x) → (msg.length : Int) ≤ maxAddr →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.klog.v2 ∗
      ⌜err = interface.nil ∧ (s = W32 0 ∨ s = W32 1 ∨ s = W32 2 ∨ s = W32 3)⌝ ∗ args ↦*{dq} xs }}
    (App (App (App (App (App
      (Val (globalAddr k8s_io.klog.v2.logging @!! go.GoType.PointerType k8s_io.klog.v2.loggingT.ty
        @!! go!"printS"))
      (Val #err)) (Val #s)) (Val #depth)) (Val #msg)) (Val #args))
  {{ RET #(); args ↦*{dq} xs }}

end spec

end EtcdGrove
end Perennial
