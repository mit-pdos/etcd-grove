/-
## `(*snapshot).Size()` (bbolt's `(*Tx).Size`, promoted): trusted (names only)

**Users.** 2d's `createMergedSnapshotMessage` (`snapshot_merge.go:49`: the message's size), the
maintenance server. **Why it is true.** bbolt's `Tx.Size` is the transaction's file size
(`pgid * pageSize`), the length of what `WriteTo` writes (4c). **Changes.** The size is the bytes'
length (`imgBytes_size`: below `2^48`). **Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Backend

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **`s.Size()`**: the length of the snapshot's bytes. -/
def snapshot.Size.spec : Prop :=
  ∀ (γ : BeNames) (s : Loc) (I : Image) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ beSnap γ s I bs }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.snapshot.ty @!! go!"Size")) (Val #()))
  {{ (n : w64), RET #n; beSnap γ s I bs ∗ ⌜uint.nat n = bs.length⌝ }}

end spec

end Backend
end EtcdGrove
end Perennial
