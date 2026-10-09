/-
`watcher.enqueueResponse(resp)`. Lean-first (no Rocq counterpart); see `InvWatcher.lean`.
-/
import EtcdGrove.Cache.InvWatcher

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- The outcome of `enqueueResponse` for a response `r`, from log `sent`: a response the filter
drops is not sent and reported delivered (`true`); otherwise the filtered one (`filterResp`)
was sent if `ok`, and nothing was sent if not (the non-blocking send found the buffer full). -/
def enqueueResult (pred : Option (GoString → Bool)) (r : RespModel) (sent : List RespModel)
    (ok : Bool) (sent' : List RespModel) : Prop :=
  match filterResp pred r with
  | none => ok = true ∧ sent' = sent
  | some r' => if ok then sent' = sent ++ [r'] else sent' = sent

/-- `w.enqueueResponse(resp)` by the producer (`watcherOpen`, so the channel is open and the
send cannot panic): see `enqueueResult`. The response sent has a non-nil `Header`
(`respSent`). Not stated: that `ok = false` only when the buffer is full, which needs the
consumer's view. -/
abbrev watcher.enqueueResponse.spec : Prop :=
  ∀ (w : Loc) (γ : WatcherNames) (pred : Option (GoString → Bool)) (sent : List RespModel)
    (resp : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      isWatcher w γ pred ∗ watcherOpen γ sent ∗ respAt resp r }}
    (App (Val (w @!! go.GoType.PointerType watcher.ty @!! go!"enqueueResponse")) (Val #resp))
  {{ (ok : Bool), RET #ok; ∃ sent', watcherOpen γ sent' ∗ ⌜enqueueResult pred r sent ok sent'⌝ }}

end spec

end EtcdGrove
end Perennial
