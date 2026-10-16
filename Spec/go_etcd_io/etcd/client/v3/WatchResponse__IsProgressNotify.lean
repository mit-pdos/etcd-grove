/-
`clientv3.WatchResponse.IsProgressNotify()` (`client/v3/watch.go`, translated
for the store). Lean-first (no Rocq counterpart); see `InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `wr.IsProgressNotify()`: `RespModel.isProgressNotify` (no events, not canceled, not
created, no compact revision, a non-zero header revision). A read, on any fraction; the header
is read only if there are no events (Go's `&&` stops at the first false operand: the watch
slice's unit W-C, whose `dispatchEvent` owns the header's `Revision` of a response with events
and hands it on, `watchHdrOwn`). -/
abbrev WatchResponse.IsProgressNotify.spec : Prop :=
  ∀ (wr : Loc) (resp : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      wr ↦{dq} resp ∗ eventsAt resp.Events' r.events ∗
      (⌜r.events = []⌝ -∗ hdrAt resp.Header' r.hdrRev) ∗
      ⌜resp.CompactRevision' = r.compactRev ∧ resp.Canceled' = r.canceled ∧
        resp.Created' = r.created⌝ }}
    (App (Val (wr @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.WatchResponse.ty @!! go!"IsProgressNotify")) (Val #()))
  {{ RET #(r.isProgressNotify); wr ↦{dq} resp }}

/-- A response modelled by `r` (`respAt`) meets `IsProgressNotify`'s precondition. -/
theorem respAt_isProgressPre (resp : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) :
    respAt (GF := GF) resp r ⊢ eventsAt resp.Events' r.events ∗
      (⌜r.events = []⌝ -∗ hdrAt resp.Header' r.hdrRev) ∗
      ⌜resp.CompactRevision' = r.compactRev ∧ resp.Canceled' = r.canceled ∧
        resp.Created' = r.created⌝ := by
  unfold respAt
  iintro ⟨#He, #Hh, %Hf⟩
  iframe He
  isplitr
  · iintro -; iexact Hh
  ipureintro; exact Hf

end spec

end EtcdGrove
end Perennial
