/-
`node.del` with a persistent key (U7h, review F1): `node.del.spec` takes a `keyR` key (given
back); a caller holding a live `srcOwn` key (rebalance's `n.parent.del(n.key)`, `node.go:414,447`)
converts it with `srcOwn_keyR`.
-/
module

public import Spec.go_etcd_io.bbolt.node__del

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`n.del(key)` with a live persistent key** (`srcOwn`, not stale), from `node.del.spec`. -/
theorem node.del.specS (hDel : node.del.spec (GF := GF) (hG := hG))
    (v : View) (n bl : Loc) (r : NRec) (qv : Qp) (key : GoSlice) (kb : List w8) (ks : Src)
    (hc : r.capOwn = true) (hs : wsSorted r.ws) (hl : wsLive r.ws) (hks : ks ≠ Src.stale)
    (hb : 0 < v.base.addr) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗
      objOwn v n (DFrac.own 1) true (WObj.node bl r) ∗ viewCells qv v ∗ srcOwn v key ks kb }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"del")) (Val #key))
  {{ RET #(); (⌜¬ wsFound r.ws kb⌝ ∗ objOwn v n (DFrac.own 1) true (WObj.node bl r) ∨
        ⌜wsFound r.ws kb⌝ ∗ ∃ (s : GoSlice),
          objOwn v n (DFrac.own 1) true
            (WObj.node bl (r.withEntsU s (r.ins.eraseIdx (wsIdx r.ws kb)) (wsDelAt r.ws kb)
              true))) ∗
      viewCells qv v }} := by
  iintro %Φ ⟨#Hpk, Ho, Hv, Hk⟩ HΦ
  icases srcOwn_keyR v key ks kb hks $$ Hk with ⟨%kr, Hk⟩
  iapply hDel v n bl r qv key kb kr hc hs hl hb $$ [Ho Hv Hk]
  · iframe; iframe #
  inext
  iintro ⟨Hd, Hv, -⟩
  iapply HΦ
  iframe

end proof

end bbolt
end EtcdGrove
end Perennial
