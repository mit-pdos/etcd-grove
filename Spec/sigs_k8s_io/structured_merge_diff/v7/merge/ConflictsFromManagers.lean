/-
`ConflictsFromManagers(sets)`: one conflict per (manager, path) of the managed fields `sets`, each
pair once (`l.Nodup`; the managers are distinct keys, each set's paths are iterated once each), in
an order not stated (Go ranges over a map, then `Set.Iterate`'s trie order): the list holds
exactly `mfPairs sets` (`FSet.ofList l`). Each path is a fresh copy. `sets` is only read.

Its caller is `Updater.update` (on the conflicts it collected: `mfPairs (conflictsMF ...)` is
`conflictsOf`, `mfPairs_conflictsMF`), whose error `Apply` returns; the API spec of `Apply` states
the same existential list. Draft (2026-11-19, notes/smd-plan.md).
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
abbrev merge.ConflictsFromManagers.spec : Prop :=
  ∀ (sets : fieldpath.ManagedFields) (cmf : MF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.merge ∗ isMF sets cmf }}
    (App (Val (@! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.merge.ConflictsFromManagers)) (Val #sets))
  {{ (s : merge.Conflicts), RET #s;
      ∃ l : List (GoString × Path), ⌜l.Nodup ∧ FSet.ofList l = mfPairs cmf⌝ ∗ isConflicts s l }}

end spec

end smd
end EtcdGrove
end Perennial
