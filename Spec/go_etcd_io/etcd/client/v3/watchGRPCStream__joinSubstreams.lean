/-
`(*clientv3.watchGRPCStream).joinSubstreams()` (`client/v3/watch.go`; (the watch slice's unit W-C). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvWatch

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- `w.joinSubstreams()`: waits for the `donec` of every substream in `substreams` and of every
non-nil one in `resuming` (D24: each the current lifetime's, `Df ws`, with `run`'s half of the
field, all of them substreams of `U`), and gets what each published. -/
abbrev watchGRPCStream.joinSubstreams.spec : Prop :=
  ∀ (wgs m : Loc) (M : GMap w64 Loc) (s : GoSlice) (l : List Loc) (dq1 dq2 dq3 dq4 : DFrac)
    (U : GMap Loc Unit) (Df : Loc → DnInfo GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      wgsF wgs go!"substreams" ↦{dq1} m ∗ ownMap m dq2 M ∗
      wgsF wgs go!"resuming" ↦{dq3} s ∗ s ↦*{dq4} l ∗
      ([∗map] ws ↦ _u ∈ U, donecAt ws (Df ws)) ∗
      ⌜(∀ X ws, M !! X = some ws → U !! ws = some ()) ∧
        (∀ ws ∈ l, ws ≠ null → U !! ws = some ())⌝ }}
    (App (Val (wgs @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"joinSubstreams")) (Val #()))
  {{ RET #(); wgsF wgs go!"substreams" ↦{dq1} m ∗ ownMap m dq2 M ∗
      wgsF wgs go!"resuming" ↦{dq3} s ∗ s ↦*{dq4} l ∗
      ([∗map] ws ↦ _u ∈ U, donecAt ws (Df ws)) ∗
      (□ ∀ (X : w64) (ws : Loc), ⌜M !! X = some ws⌝ → □ (Df ws).Q) ∗
      (□ ∀ ws : Loc, ⌜ws ∈ l ∧ ws ≠ null⌝ → □ (Df ws).Q) }}

end spec

end EtcdGrove
end Perennial
