/-
`(*Updater).addBackOwnedItemsForVersion(merged, pruned, version, managed)` (internal): the merged
object (returned first, the same pointer: the identity converter) and the merged object less what
it has and neither the pruned object nor the managed set has, each closed by `ensureNamed`
(`addBackOwned`: `merged.RemoveItems(ens(fs merged) \ (ens(fs pruned) ∪ ens managed))`). No error
in the scope (the identity converter; `ToFieldSet` of conforming values).

Internal to `merge`: mirrors the code over the abstract stage. Draft (2026-11-19,
notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.merge.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.merge.Defs

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
variable [package_sem : merge.Assumptions]

/-- See the file header. -/
abbrev merge.Updater.addBackOwnedItemsForVersion.spec : Prop :=
  ∀ (u : Loc) (cv : merge.Converter) (igf igfl : GoMap) (rion : Bool) (sc : Loc) (S : Schema) (t : TypeRef)
    (mp : Loc) (merged : UVal) (pp : Loc) (pruned : UVal) (ver : GoString) (ms : Loc) (managed : PathSet),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.merge ∗ isUpdater u cv igf igfl rion ∗ isIdentityConverter cv ∗ isTV mp sc S t merged ∗ isTV pp sc S t pruned ∗ isSet ms managed }}
    (App (App (App (App (Val (u @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.merge.Updater.ty @!! go!"addBackOwnedItemsForVersion"))
      (Val #mp)) (Val #pp)) (Val #ver)) (Val #ms))
  {{ (mp' pp' : Loc) (err : GoInterface), RET (PairV (PairV #mp' #pp') #err);
      ⌜mp' = mp ∧ err = interface.nil⌝ ∗ isTV pp' sc S t (addBackOwned S t merged pruned managed) }}

end spec

end smd
end EtcdGrove
end Perennial
