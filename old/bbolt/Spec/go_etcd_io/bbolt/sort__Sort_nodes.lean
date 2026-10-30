module
public import Proof.go_etcd_io.bbolt.Init

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

/-- `sort.Sort(n.children)` (`node.spill`): a slice of `nodes`, whose `Less` (`nodes.Less`)
compares the nodes' first keys; it reads, of each node `l` of the slice, its struct (`f l`),
its inodes (`g l`, at least one: `Less` panics otherwise) and its first inode's key (`k l`), at
the fractions `qn l`, `qi l`, `qk l`, and gives them back. The slice ends a permutation of what it held.
`sort.Sort` is translated names-only; this spec is an axiom (`Proof/go_etcd_io/bbolt/
sort__Sort_nodes.lean`). -/
abbrev sort.Sort.nodes_spec : Prop :=
  ∀ (s : GoSlice) (xs : List Loc) (f : Loc → node) (g : Loc → List internal.common.Inode)
    (k : Loc → List w8) (qn qi qk : Loc → DFrac),
  (∀ l ∈ xs, g l ≠ []) →
  {{ s ↦* xs ∗ [∗list] l ∈ xs, (l ↦{qn l} f l ∗ (f l).inodes' ↦*{qi l} g l ∗
      ((g l).headD (zero_val internal.common.Inode)).key' ↦*{qk l} k l : IProp GF) }}
    (App (Val #(functions _root_.Perennial.sort.«Sort» [])) (Val #(interface.mkOk nodes.ty #s)))
  {{ (ys : List Loc), RET #(); ⌜ys.Perm xs⌝ ∗ s ↦* ys ∗ [∗list] l ∈ xs, (l ↦{qn l} f l ∗
      (f l).inodes' ↦*{qi l} g l ∗ ((g l).headD (zero_val internal.common.Inode)).key' ↦*{qk l} k l) }}

end spec

end bbolt
end EtcdGrove
end Perennial
