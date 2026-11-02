module
public import Proof.go_etcd_io.bbolt.NodeTree

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `n.dereference()` on a subtree of nodes of the bucket `bl` (`d` levels deep): every node's
key, inode keys and inode values become heap copies (`derefPost`), and the transaction's
`NodeDeref` statistic grows (by the number of nodes). It panics on an empty inode key, and on
an empty node key of a node that has a page (`derefPre` rules both out). -/
abbrev node.dereference.spec : Prop :=
  ∀ (d : Nat) (nl bl : Loc) (bv : Bucket) (dqb : DFrac) (st : TxStats),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ nodeTree (derefPre bl) d nl ∗
      bl ↦{dqb} bv ∗ structFieldRef Tx go!"stats" bv.tx' ↦ st }}
    (App (Val (nl @!! go.GoType.PointerType node.ty @!! go!"dereference")) (Val #()))
  {{ (k : w64), RET #(); nodeTree (derefPost bl) d nl ∗ bl ↦{dqb} bv ∗
      structFieldRef Tx go!"stats" bv.tx' ↦ ({ st with NodeDeref' := st.NodeDeref' + k } : TxStats) }}

end spec

end bbolt
end EtcdGrove
end Perennial
