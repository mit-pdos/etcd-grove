/-
`concurrency.writeSet.get(keys...)` (`client/v3/concurrency/stm.go`). Lean-first (no Rocq counterpart); see
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- `ws.get(keys...)`: nil if no key of `keys` is written; otherwise a fresh copy of the write of
one of them (the first in `keys`). -/
abbrev writeSet.get.spec : Prop :=
  ∀ (m : Loc) (dq : DFrac) (pfx : GoString) (wsMap : GMap GoString stmPut)
    (writes : GMap GoString WriteM) (ksl : GoSlice) (ks : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ m ↦${dq} wsMap ∗ writesAt pfx wsMap writes ∗ ksl ↦*□ ks }}
    (App (Val (m @!! writeSet.ty @!! go!"get")) (Val #ksl))
  {{ (p : Loc), RET #p; m ↦${dq} wsMap ∗
      (⌜p = null ∧ ∀ k ∈ ks, writes !! k = none⌝ ∨
        ∃ (k : GoString) (w : WriteM) (sp : stmPut),
          ⌜k ∈ ks ∧ writes !! k = some w ∧ sp.val' = w.val⌝ ∗ p ↦ sp) }}

end spec

end concurrency
end EtcdGrove
end Perennial
