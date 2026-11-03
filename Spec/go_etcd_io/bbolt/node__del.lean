/-
`node.del` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U7; used by U7 (`Delete`, `DeleteBucket`), U8 (`node.rebalance`'s `parent.del`). Proof:
`Proof/go_etcd_io/bbolt/node__del.lean` (a `sorry` until U7).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `n.del(key)` on a live node of the writer's heap whose entries are sorted and not stale: the
entry of key `key` at its search index is removed and the node marked unbalanced, if there is
one (`wsDelAt`); else nothing changes. -/
abbrev node.del.spec : Prop :=
  ∀ (v : View) (n bl : Loc) (r : NRec) (qv : Qp) (key : GoSlice) (kb : List w8) (ks : Src),
  wsSorted r.ws → wsLive r.ws → ks ≠ Src.stale →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗
      objOwn v n (DFrac.own 1) true (WObj.node bl r) ∗ viewCells qv v ∗ srcOwn v key ks kb }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"del")) (Val #key))
  {{ RET #(); (⌜¬ wsFound r.ws kb⌝ ∗ objOwn v n (DFrac.own 1) true (WObj.node bl r) ∨
        ⌜wsFound r.ws kb⌝ ∗ ∃ (s : GoSlice) (ins : List Inode),
          objOwn v n (DFrac.own 1) true
            (WObj.node bl (r.withEntsU s ins (wsDelAt r.ws kb) true))) ∗
      viewCells qv v }}

end spec

end bbolt
end EtcdGrove
end Perennial
