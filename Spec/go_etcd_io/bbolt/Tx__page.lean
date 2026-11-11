/-
`Tx.page` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U4; used by U5 (`Tx.init`), U6 (`Tx.page_r`), U7 (`Bucket.node`), U8, U9, U10, U11. Proof:
`Proof/go_etcd_io/bbolt/Tx__page.lean` (a `sorry` until U4).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `tx.page(id)` (general, over the fields it reads; design §4.2 row 1): the page cache's page
`pm[id]` if there is one (a writer's `tx.pages`; a reader's is nil), else page `id` of the
mapping (`db.page`). The page's header must name `id` and be of a valid type (`FastCheck`, which
panics otherwise); its bytes are only read, at any fraction. -/
abbrev Tx.page.spec : Prop :=
  ∀ (tx db : Loc) (pmv : GoMap) (pm : GMap w64 Loc) (data : Loc) (id : w64) (p : Loc)
    (pg : List w8) (dqt dqm dqd dq : DFrac),
  (pm !! id = some p ∨
    (pm !! id = none ∧ 0 < data.addr ∧ id.toNat * 4096 < 0xFFFFFFFFFFFF ∧
      p = data +ₗ ((id.toNat * 4096 : Nat) : Int))) →
  16 ≤ pg.length → pageId pg = id.toNat →
  (pageFlags pg = branchPageFlag ∨ pageFlags pg = leafPageFlag ∨ pageFlags pg = metaPageFlag ∨
    pageFlags pg = freelistPageFlag) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗
      tx.[Tx, go!"pages"] ↦{dqt} pmv ∗
      (if pmv = null then iprop(⌜pm = ∅⌝) else iprop(pmv ↦${dqm} pm)) ∗
      tx.[Tx, go!"db"] ↦{dqt} db ∗ db.[DB, go!"data"] ↦{dqd} data ∗
      db.[DB, go!"pageSize"] ↦□ W64 4096 ∗ bytesPointsto p dq pg }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"page")) (Val #id))
  {{ RET #p; tx.[Tx, go!"pages"] ↦{dqt} pmv ∗
      (if pmv = null then iprop(⌜pm = ∅⌝) else iprop(pmv ↦${dqm} pm)) ∗
      tx.[Tx, go!"db"] ↦{dqt} db ∗ db.[DB, go!"data"] ↦{dqd} data ∗ bytesPointsto p dq pg }}

end spec

end bbolt
end EtcdGrove
end Perennial
