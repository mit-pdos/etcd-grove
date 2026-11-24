/-
`(*alarmBackend).unsafeGetAllAlarms(tx)` (`server/storage/schema/alarm.go:91`). Lean-first (no Rocq
counterpart); for `GetAllAlarms` (prove-ps2-v3alarm, 2026-11-24).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.RdPool
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`ab.unsafeGetAllAlarms(tx)` over the held shared read transaction**, at a readers' state `rv` whose
alarm bucket is empty (`rvBkt`; the state well formed, `rv.2.Wf`, as every held one is, `rtHeld_wf`): no
record, no error. Go: `tx.UnsafeForEach(Alarm, visitor)` walks the readers' entries of the bucket
(`rtForEach`: exactly those of `rvBkt`, none), so the visitor (`proto.Unmarshal` of each key into a fresh
`AlarmMember`, appended to `ms`) is never called, and `ms` stays nil. -/
abbrev schema.alarmBackend.unsafeGetAllAlarms.spec : Prop :=
  ∀ (abl : Loc) (γ : backend.BNames) (P : backend.BParams) (W Pk : IProp GF) (be rt rtx : Loc)
    (rv : backend.RView) (p : Qp),
  P.has mvcc.alarmBI → backend.rvBkt P rv go!"alarm" = ∅ → rv.2.Wf →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      backend.isBackend γ P W Pk be ∗ backend.bF go!"readTx" be ↦□ rt ∗ backend.rtHeldF γ P be rtx rv p }}
    (App (Val (abl @!! go.GoType.PointerType
      go_etcd_io.etcd.server.v3.storage.schema.alarmBackend.ty @!! go!"unsafeGetAllAlarms"))
      (Val #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.readTx.ty)
        #rt : GoInterface)))
  {{ (ms : GoSlice) (err : GoInterface), RET (PairV #ms #err); ⌜err = GoInterface.nil⌝ ∗
      ms ↦* ([] : List Loc) ∗ backend.rtHeldF γ P be rtx rv p }}

end spec

end EtcdGrove
end Perennial
