/-
`notify.Notifier.Receive` (`notify.go`: the current channel, under the read lock). Lean-first (no Rocq counterpart); the request path's unit 4b (2026-10-13).
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.notify.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `n.Receive()`, with a reader slot (given back): the current channel, closed by the next
`Notify` (`notifyChan`). -/
abbrev notify.Notifier.Receive.spec : Prop :=
  ∀ (n : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.notify ∗ notifyReader n }}
    (App (Val (n @!! go.GoType.PointerType notify.Notifier.ty @!! go!"Receive")) (Val #()))
  {{ (ch : Loc), RET #ch; notifyReader n ∗ notifyChan ch }}

end spec

end EtcdGrove
end Perennial
