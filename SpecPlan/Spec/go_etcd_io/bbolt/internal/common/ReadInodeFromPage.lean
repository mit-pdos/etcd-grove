/-
## `ReadInodeFromPage(p)` (`internal/common/inode.go`)

**Users.** node.go:165 (`node.read`: a page of the mmap, a dirty page, or a bucket's inline page). Snippet `ReqNodeRoundTrip`.
**Proof sketch.** `make(Inodes, count)`; per element, `LeafPageElement(i)`/`BranchPageElement(i)` and their getters (the page-relative specs above), the `Inode` setters on `&inodes[i]`, `Assert(len(key) > 0)` (`pageReadable`). The keys' bytes are not read; a caller reaches them with `pageKV_access`.
**Changes.** from `specs-ref`'s file of the same name: `pageReadable` restated over the decoded page (elements and data inside the bytes, keys non-empty); the address premises dropped (implied by the bytes).
**Margin.** none: the post is what the code computes.
-/
module

public import SpecPlan.Spec.go_etcd_io.bbolt.internal.common.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace BboltCommon

open Iris Iris.BI go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- `ReadInodeFromPage(p)`: a new slice of the page's inodes (`pageInodesAt`: each item's flags or page id, its key and value as slices into the page). It panics on an empty key, which `pageReadable` excludes. -/
def ReadInodeFromPage.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ bytesPointsto p dq bs ∗ ⌜pageHeaderSize ≤ bs.length ∧ pageReadable bs⌝ }}
    (App (Val (@! go_etcd_io.bbolt.internal.common.ReadInodeFromPage)) (Val #p))
  {{ (s : GoSlice), RET #s; bytesPointsto p dq bs ∗ s ↦* pageInodesAt p bs ∗
      ownSliceCap Inode s (DFrac.own 1) }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
