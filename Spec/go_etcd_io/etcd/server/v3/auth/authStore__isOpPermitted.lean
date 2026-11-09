/-
## `(*authStore).isOpPermitted(userName, revision, key, rangeEnd, permTyp)` (internal helper)

**Users.** `IsPutPermitted`, `IsRangePermitted`, `IsDeleteRangePermitted`.

**Proof sketch.** `IsAuthEnabled` (off: `nil`, at `jf`); revision `0`: `ErrUserEmpty`; `Revision()` above `revision`: `ErrAuthOldRevision`; `lockedReadTx` (at `jx`): the user (absent: `ErrPermissionDenied`, so not root), `hasRootRole` (the stored roles are sorted: `authBackendAt`); `isRangeOpPermitted` (at `jc`); the deferred `RUnlock`.

**Changes.** The old spec restated over `Api.lean`'s and `Internal.lean`'s vocabulary.

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.Internal

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Auth

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- The permission type `isOpPermitted` checks (`authpb.Permission_READ` is `0`, `WRITE` `1`). -/
def ptOf (pt : w32) : PermType := if pt = W32 0 then .read else .write

/-- **`as.isOpPermitted(u, rev, key, rangeEnd, pt)`** for `READ` or `WRITE`: `checkPost`. -/
def authStore.isOpPermitted.spec : Prop :=
  ∀ (st : Loc) (γ : Cluster) (γa : AuthNames) (i0 : Nat) (u : GoString) (rev : w64)
    (key re : GoSlice) (dk de : DFrac) (k e : List w8) (pt : w32),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authStoreAt st γ γa ∗ authLb γa i0 ∗ threadTok ∗ key ↦*{dk} k ∗ re ↦*{de} e ∗
      ⌜(pt = W32 0 ∨ pt = W32 1) ∧ sint.Z key.len < 2 ^ 63 - 1 ∧ sint.Z re.len < 2 ^ 63 - 1⌝ }}
    (App (App (App (App (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!! go!"isOpPermitted")) (Val #u)) (Val #rev)) (Val #key)) (Val #re))
      (Val #pt))
  {{ (err : GoInterface), RET #err; threadTok ∗ key ↦*{dk} k ∗ re ↦*{de} e ∗
      checkPost γa i0 u rev (ptOf pt) { key := k, rangeEnd := e } err }}

end spec
end Auth
end EtcdGrove
end Perennial
