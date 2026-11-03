/- Lean-first (no Rocq counterpart).

`s.Compact(i)` (storage.go): the image's compaction (`image.compact`), whose answer it returns, then
`MemoryStorage.Compact(i)`. Stated over any triple of the `MemoryStorage`'s call
(`MemoryStorage.Compact.spec`'s, with `P` its precondition and `Q` its postcondition), under the
image's premise (`i` at most the image's last index): the caller holds the replica's `dmu` (the
image), or owns the storage before its node runs.
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
abbrev Storage.Compact.spec : Prop :=
  ∀ (s ms : Loc) (γs : MemStorNames) (ip : Loc) (I : StorFile) (i : w64) (eco : GoInterface)
    (P : IProp GF) (Q : GoInterface → IProp GF),
  uint.nat i ≤ uint.nat I.prev + I.ents.length →
  {{ P }}
    (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"Compact")) (Val #i))
  {{ (e : GoInterface), RET #e; Q e }} →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvdurable ∗
      kdStorRec s ms γs ∗ s.[KStorage, go!"img"] ↦□ ip ∗ ownImage ip I ∗
      globalAddr ErrCompacted ↦□ eco ∗ P }}
    (App (Val (s @!! go.GoType.PointerType kStorageTy @!! go!"Compact")) (Val #i))
  {{ (err : GoInterface), RET #err; (∃ e : GoInterface, Q e) ∗
      (if imgCompactStale I i then iprop(⌜err = eco⌝ ∗ ownImage ip I)
       else iprop(⌜err = interface.nil⌝ ∗ ownImage ip (imgCompact I i))) }}

end spec

end kvdurable
end EtcdGrove
end Perennial
