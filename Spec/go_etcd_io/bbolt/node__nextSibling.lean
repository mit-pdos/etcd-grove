module
public import Spec.go_etcd_io.bbolt.Bucket__node

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section defs
variable [ext : FfiSyntax]

/-- What `nextSibling`/`prevSibling` of the node `nl` (record `r`) of the bucket `bl` need: its
parent `pl` (if any) is another branch node of the bucket, sorted, its bytes not stale, and each
child it names can be materialized (`Bucket.node.spec`). -/
def siblingOK (W : WView) (B : BRec) (pm : GMap w64 Loc) (bl nl : Loc) (r : NRec) : Prop :=
  r.nv.parent' = null ∨
  ∃ rp, B.ns !! r.nv.parent' = some rp ∧ r.nv.parent' ≠ nl ∧ rp.nv.isLeaf' = false ∧
    rp.nv.bucket' = bl ∧ wsSorted rp.ws ∧ wsLive rp.ws ∧ r.ksrc ≠ Src.stale ∧
    ∀ w ∈ rp.ws, (∀ l, B.nm !! w.pgid = some l → l ≠ null) ∧
      (B.nm !! w.pgid = none → ∃ p pg src, nodeSrcOK W B pm w.pgid p pg src)

/-- What they did: nothing (no sibling), or `b.node` of the parent's child `i`. -/
def siblingRes (B : BRec) (bl : Loc) (r : NRec) (l : Loc) (B' : BRec)
    (st st' : go_etcd_io.bbolt.TxStats) : Prop :=
  (l = null ∧ B' = B ∧ st' = st) ∨
  ∃ (rp : NRec) (i : Nat) (w : WEntry) (p : Loc) (pg : List w8) (src : Src),
    B.ns !! r.nv.parent' = some rp ∧ rp.ws[i]? = some w ∧
    nodeRes B bl w.pgid r.nv.parent' p pg src l B' st st'

end defs

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `n.nextSibling()` of the node `nl` of the bucket `bl`: nil for a root or a last child, else
the parent's next child (`childAt`, which may materialize it). -/
abbrev node.nextSibling.spec : Prop :=
  ∀ (W : WView) (bl : Loc) (B : BRec) (txl : Loc) (st : TxStats) (pmap : GoMap)
    (pm : GMap w64 Loc) (dqp : DFrac) (nl : Loc) (r : NRec),
  viewOK W → B.bv.tx' = txl → B.ns !! nl = some r → siblingOK W B pm bl nl r →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ bktOwn W bl B ∗ wView W ∗
      structFieldRef Tx go!"stats" txl ↦ st ∗ structFieldRef Tx go!"pages" txl ↦{dqp} pmap ∗
      pmap ↦${dqp} pm ∗ structFieldRef Tx go!"db" txl ↦{dqp} W.dbl }}
    (App (Val (nl @!! go.GoType.PointerType node.ty @!! go!"nextSibling")) (Val #()))
  {{ (l : Loc) (B' : BRec) (st' : TxStats), RET #l;
      bktOwn W bl B' ∗ wView W ∗
      structFieldRef Tx go!"stats" txl ↦ st' ∗ structFieldRef Tx go!"pages" txl ↦{dqp} pmap ∗
      pmap ↦${dqp} pm ∗ structFieldRef Tx go!"db" txl ↦{dqp} W.dbl ∗
      ⌜siblingRes B bl r l B' st st'⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
