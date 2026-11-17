/-
`(*lessor).Attach` (`server/lease/lessor.go`). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/lease/InvLessor.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.lease lease

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- `le.Attach(id, items)` (locked), by the lease owner (`leaseOwn γl L I`) for a live `id`
(`id ∈ L`) and items on no other lease: adds the items to the lease's item set and the item map
(the owner's `I`, unit T3, L2b) and returns `nil`.
(auth-lease S4 item 7b, 2026-11-17) In the owner's open window `w` (`leaseOwnW`; `leaseOwn` is `w = none`),
the items it changes go to the window's target (`winStep`), so the snapshot it pushes is stable in the window. -/
abbrev lease.lessor.Attach.spec : Prop :=
  ∀ (lp : Loc) (γl : GName) (id : w64) (items : GoSlice) (xs : List LeaseItem) (dq : DFrac)
    (L : List w64) (I : GMap LeaseItem w64) (w : Option LWin),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ lessorInv lp γl ∗
      leaseOwnW γl L I w ∗ ⌜winStep w I (insertAll I xs id)⌝ ∗ ⌜id ∈ L⌝ ∗
      ⌜∀ it ∈ xs, I.lookup it = none ∨ I.lookup it = some id⌝ ∗
      ⌜∀ it ∈ xs, (it.Key'.length : Int) < 2 ^ 63 - 1⌝ ∗ items ↦*{dq} xs }}
    (App (App (Val (lp @!! go.GoType.PointerType lessor.ty @!! go!"Attach")) (Val #id)) (Val #items))
  {{ RET #GoInterface.nil; leaseOwnW γl L (insertAll I xs id) w ∗ items ↦*{dq} xs }}

end spec

end EtcdGrove
end Perennial
