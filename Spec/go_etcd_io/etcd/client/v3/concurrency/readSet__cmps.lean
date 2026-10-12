/-
`concurrency.readSet.cmps()` (`client/v3/concurrency/stm.go`). Lean-first (no Rocq counterpart); see
`InvSTM.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvSTM

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- `rs.cmps()`: one `isKeyCurrent` comparison per read, in the map's order (`ReadCmpsOk`).
The slice's capacity is the caller's (`mkSTM`'s conflicts closure appends to it). -/
abbrev readSet.cmps.spec : Prop :=
  ∀ (m : Loc) (dq : DFrac) (pfx : GoString) (rsMap : GMap GoString Loc)
    (reads : GMap GoString ReadM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ m ↦${dq} rsMap ∗ readsAt pfx rsMap reads }}
    (App (Val (m @!! readSet.ty @!! go!"cmps")) (Val #()))
  {{ (sl : GoSlice), RET #sl; m ↦${dq} rsMap ∗
      ∃ ms : List CmpModel, cmpsAt sl ms ∗ ownSliceCap go_etcd_io.etcd.client.v3.Cmp sl (DFrac.own 1) ∗
        ⌜ReadCmpsOk reads ms⌝ }}

end spec

end concurrency
end EtcdGrove
end Perennial
