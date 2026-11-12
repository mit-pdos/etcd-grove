/-
`context.TODO()`'s context as the `node` API's (`nodeCtx`): what the pipeline's and the snapshot's
handlers pass `Process` (moved from `pipelineHandler__ServeHTTP.lean`, 2026-10-25, stage 7e).
Lean-first.
-/
module

public import Spec.context.TODO
public import Proof.go_etcd_io.raft.v3.InvNodeCtx

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.context.Assumptions]

/-- `context.TODO()`'s `Done()` is `nil` (as `mvcc`'s `wp_todoCtx_Done`, for `todoCtx`). -/
theorem wp_todoCtx_Done' :
    {{ (True : IProp GF) }}
      (App (Val #(methods context.todoCtx.ty go!"Done" #(zero_val context.todoCtx))) (Val #()))
    {{ RET #chan.nil; True }} := by
  wp_start
  wp_method_call
  wp_auto
  iapply HΦ
  itrivial

end lemmas

end EtcdGrove
end Perennial
