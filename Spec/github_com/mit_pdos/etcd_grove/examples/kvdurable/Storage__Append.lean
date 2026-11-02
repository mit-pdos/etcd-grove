/- Lean-first (no Rocq counterpart).

`s.Append(entries)` (storage.go): the image's append (`image.append`: `imgAppend`), then
`MemoryStorage.Append(entries)`. Stated over any triple of the `MemoryStorage`'s call that takes the
entries `es` (consecutive from `k`) at `dq` and gives them back (`MemoryStorage.Append.spec`'s, with
`P` the rest of its precondition and `Q` of its postcondition), under the image's premises: the
caller holds the replica's `dmu` (the image), or owns the storage before its node runs.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Image
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.KdStorage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]

/-- See the file header. -/
abbrev Storage.Append.spec : Prop :=
  ∀ (s ms : Loc) (γs : MemStorNames) (ip : Loc) (I : StorFile) (sl : GoSlice) (dq : DFrac)
    (k : Nat) (es : List EntryM) (P Q : IProp GF),
  (∀ (j : Nat) (e : EntryM), es[j]? = some e → uint.nat e.Index' = k + j) →
  (es ≠ [] → k ≤ uint.nat I.prev + 1 + I.ents.length) →
  uint.nat I.prev + 1 + I.ents.length + es.length < 2 ^ 63 →
  {{ P ∗ entsPts sl dq es }}
    (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"Append")) (Val #sl))
  {{ RET #interface.nil; entsPts sl dq es ∗ Q }} →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvdurable ∗
      kdStorRec s ms γs ∗ s.[KStorage, go!"img"] ↦□ ip ∗ ownImage ip I ∗ entsPts sl dq es ∗ P }}
    (App (Val (s @!! go.GoType.PointerType kStorageTy @!! go!"Append")) (Val #sl))
  {{ RET #(); entsPts sl dq es ∗ Q ∗ ownImage ip (imgAppend I k es) }}

end spec

end kvdurable
end EtcdGrove
end Perennial
