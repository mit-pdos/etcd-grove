/-
`SetNodeMap.Descend(pe)`: the child set at `pe`, created empty (`&Set{}`, inserted in order) if
absent, for `Set.Insert`'s descent: the child is lent out owned with a wand putting a new version of
it back. Over the raw trie (`ownNodesT`): the new child is empty, so the trie is not canonical until
`Set.Insert` has put a path in it. Internal, mirrors the code.

Draft (2026-11-19, notes/smd-plan.md, "The call DAG"): internal.
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI
open sigs_k8s_io.structured_merge_diff.v7

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : fieldpath.Assumptions]

/-- See the file header. -/
abbrev fieldpath.SetNodeMap.Descend.spec : Prop :=
  ∀ (l : Loc) (cs : List (PE × Trie)) (e : fieldpath.PathElement) (pe : PE),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ ownNodesT l cs ∗ isPE e pe ∗ ⌜PE.Sorted (cs.map (·.1)) ∧ cs.length + 1 < 2 ^ 63⌝ }}
    (App (Val (l @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap.ty @!! go!"Descend")) (Val #e))
  {{ (q : Loc), RET #q; ∃ t : Trie,
      ⌜nodesLookup pe cs = some t ∨ (nodesLookup pe cs = none ∧ t = Trie.empty)⌝ ∗
      trieOwn q t ∗ (∀ t' : Trie, trieOwn q t' -∗ ownNodesT l (nodesSet pe t' cs)) }}

end spec

end smd
end EtcdGrove
end Perennial
