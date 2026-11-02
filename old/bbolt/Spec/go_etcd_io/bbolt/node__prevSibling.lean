module
public import Spec.go_etcd_io.bbolt.node__nextSibling

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `n.prevSibling()`: nil for a root or a first child, else the parent's previous child. -/
abbrev node.prevSibling.spec : Prop :=
  ∀ (W : WView) (bl : Loc) (B : BRec) (txl : Loc) (st : TxStats) (pmap : GoMap)
    (pm : GMap w64 Loc) (dqp : DFrac) (nl : Loc) (r : NRec),
  viewOK W → B.bv.tx' = txl → B.ns !! nl = some r → siblingOK W B pm bl nl r →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ bktOwn W bl B ∗ wView W ∗
      structFieldRef Tx go!"stats" txl ↦ st ∗ structFieldRef Tx go!"pages" txl ↦{dqp} pmap ∗
      pmap ↦${dqp} pm ∗ structFieldRef Tx go!"db" txl ↦{dqp} W.dbl }}
    (App (Val (nl @!! go.GoType.PointerType node.ty @!! go!"prevSibling")) (Val #()))
  {{ (l : Loc) (B' : BRec) (st' : TxStats), RET #l;
      bktOwn W bl B' ∗ wView W ∗
      structFieldRef Tx go!"stats" txl ↦ st' ∗ structFieldRef Tx go!"pages" txl ↦{dqp} pmap ∗
      pmap ↦${dqp} pm ∗ structFieldRef Tx go!"db" txl ↦{dqp} W.dbl ∗
      ⌜siblingRes B bl r l B' st st'⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
