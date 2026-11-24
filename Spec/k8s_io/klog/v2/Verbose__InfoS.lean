/-
`v.InfoS(msg, keysAndValues...)`: structured logging, a no-op for the watcher's results. Until
klog-infos (2026-11-23) names-only, the trust boundary: an axiom (T5-g, decided by etcd-grove-81
2026-11-15). Go evidence: `examples/premisefix/watcherctx/infos_test.go`
(`TestKlogInfoSDisabledReturns`, `TestKlogInfoSEnabledReturns`: the call shape at `-v=0` and `-v=3`,
adversarial strings, ints and durations, the arguments' slice unchanged). Restricted to the call shape the watcher makes
(`block_logger.go:69-75`): keys and values whose dynamic types are `string`, `int`,
`time.Duration` or `schema.GroupResource` (klog's text serializer formats them through
`fmt`/`String()`, which return for these types). Lean-first (no Rocq counterpart).

(klog-infos, 2026-11-23, etcd-grove#25) Proved over its translated body
(`Proof/k8s_io/klog/v2/Verbose__InfoS.lean`: when `v` is enabled, `logging.infoS`, then `printS`:
`strconv.AppendQuote` of the message, a buffer from klog's pool, the trusted serializer
`serialize.FormatKVs`, which is stuck on a key or value other than `klog.infoSArgOk`, and `printDepth`,
`fmt.Fprint` of the buffer), for a `v` with no logger (`v.logger` is `nil`, which `klog.V`'s post
gives: ledger, 2026-11-23), as `Verbose.Infof`, and a message of at most `maxAddr` bytes
(Perennial's `strconv.AppendQuote` needs it: `appendQuotedWith`'s `make` capacity `len(buf)+1+len(s)+1`
overflows for a string near `2^63`, which Perennial's unbounded string values allow; ledger).
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
abbrev klog.Verbose.InfoS.spec : Prop :=
  ∀ (v : k8s_io.klog.v2.Verbose) (msg : GoString) (args : GoSlice) (xs : List GoInterface)
    (dq : DFrac), v.logger' = null → (msg.length : Int) ≤ maxAddr →
  (∀ x ∈ xs, klog.infoSArgOk x) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.klog.v2 ∗ args ↦*{dq} xs }}
    (App (App (Val (v @!! k8s_io.klog.v2.Verbose.ty @!! go!"InfoS")) (Val #msg)) (Val #args))
  {{ RET #(); args ↦*{dq} xs }}

end spec

end EtcdGrove
end Perennial
