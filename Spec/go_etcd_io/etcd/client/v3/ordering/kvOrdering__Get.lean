/-
`(*kvOrdering).Get(ctx, key, opts...)` (`client/v3/ordering/kv.go`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.ordering.InvOrdering

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ordering

open Iris Iris.BI go_etcd_io.etcd.client.v3.ordering go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.ordering.Assumptions]

/-- `kv.Get(ctx, key, opts...)`: reads `prevRev := kv.getPrevRev()`, builds `op := OpGet(key, opts...)`,
and loops `kv.KV.Do(ctx, op)` until either `Do` fails, `resp.Header.Revision ≥ prevRev` (advancing
`kv.prevRev` when `resp.Header.Revision > prevRev`), or `kv.orderViolationFunc(op, r, prevRev)`
returns a non-nil error. -/
abbrev kvOrdering.Get.spec : Prop :=
  ∀ (kvp : Loc) (kv : go_etcd_io.etcd.client.v3.KV) (vf : OrderViolationFunc)
    (ctx : context.Context) (key : GoString) (sl : GoSlice) (gs : List (OpFull → OpFull))
    (R : w64 → IProp GF) (PostOk : Loc → w64 → IProp GF) (PostErr : GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.ordering ∗
      isKvOrdering kvp kv vf ∗
      kvOrderingHandle kvp R ∗
      optsAt sl gs ∗ ⌜¬ opGetPanics gs⌝ ∗
      kvDoGetSpec kv ctx (opGetModel key gs) R PostOk PostErr ∗
      orderViolationSpec vf R PostErr }}
    (App (App (App (Val (kvp @!! go.GoType.PointerType kvOrdering.ty @!! go!"Get"))
      (Val #ctx)) (Val #key)) (Val #sl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      kvOrderingHandle kvp R ∗
      if decide (err = GoInterface.nil) then
        ∃ (prevRev rev : w64) (hdr : Loc),
          ⌜resp ≠ null ∧ hdr ≠ null ∧ sint.Z prevRev ≤ sint.Z rev⌝ ∗
          structFieldRef etcdserverpb.RangeResponse go!"Header" resp ↦□ hdr ∗
          structFieldRef etcdserverpb.ResponseHeader go!"Revision" hdr ↦□ rev ∗
          □ R prevRev ∗ □ R rev ∗ PostOk resp rev
      else
        ⌜resp = null⌝ ∗ PostErr err }}

end spec

end ordering
end EtcdGrove
end Perennial
