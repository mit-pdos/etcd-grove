/-
`node.del` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U7; used by U7 (`Delete`, `DeleteBucket`), U8 (`node.rebalance`'s `parent.del`). Proof:
`Proof/go_etcd_io/bbolt/node__del.lean` (a `sorry` until U7).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx
public import Proof.go_etcd_io.bbolt.Read.Src

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
one (`wsDelAt`; its inode removed at the same index, batch 28); else nothing changes. The view's base is a mapped address (`0 < v.base.addr`, from
`mapFields`). The key is only read (`node.go:145-159`): a `keyR` key (caller-owned at a fraction,
as `Bucket.Delete`'s, or the view's), given back (review F1, U7h; a persistent `srcOwn` key, as
rebalance's node keys, converts with `srcOwn_keyR`, `node.del.specS`). -/
abbrev node.del.spec : Prop :=
  ∀ (v : View) (n bl : Loc) (r : NRec) (qv : Qp) (key : GoSlice) (kb : List w8) (kr : KeyR),
  r.capOwn = true → wsSorted r.ws → wsLive r.ws → 0 < v.base.addr →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗
      objOwn v n (DFrac.own 1) true (WObj.node bl r) ∗ viewCells qv v ∗ keyR v key kr kb }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"del")) (Val #key))
  {{ RET #(); (⌜¬ wsFound r.ws kb⌝ ∗ objOwn v n (DFrac.own 1) true (WObj.node bl r) ∨
        ⌜wsFound r.ws kb⌝ ∗ ∃ (s : GoSlice),
          objOwn v n (DFrac.own 1) true
            (WObj.node bl (r.withEntsU s (r.ins.eraseIdx (wsIdx r.ws kb)) (wsDelAt r.ws kb)
              true))) ∗
      viewCells qv v ∗ keyR v key kr kb }}

end spec

end bbolt
end EtcdGrove
end Perennial
