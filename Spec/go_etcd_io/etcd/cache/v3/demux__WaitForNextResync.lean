/-
`demux.WaitForNextResync(ctx)` (`cache/demux.go`). Lean-first (no Rocq counterpart); see `InvDemux.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvDemux

@[expose] public section

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

/-- `d.WaitForNextResync(ctx)` (`d.resynced.wait(ctx)`), with a handle on the demux's notifier and
a lower bound `k0` on its notifications: `nil` once a resync loop iteration completed after the
`k0`-th (`notifierLb γn (k0 + 1)`), or a non-nil error once the context is done
(`notifierWaitResult`). -/
abbrev demux.WaitForNextResync.spec : Prop :=
  ∀ (d : Loc) (γn : NotifierNames) (k0 : Nat) (ctx : GoInterfaceOk)
    (s : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      demuxResyncHandle d γn ∗ notifierLb γn k0 ∗ context.isContext ctx s }}
    (App (Val (d @!! go.GoType.PointerType demux.ty @!! go!"WaitForNextResync"))
      (Val #(GoInterface.ok ctx)))
  {{ (err : GoInterface), RET #err; demuxResyncHandle d γn ∗ notifierWaitResult γn k0 s err }}

end spec

end EtcdGrove
end Perennial
