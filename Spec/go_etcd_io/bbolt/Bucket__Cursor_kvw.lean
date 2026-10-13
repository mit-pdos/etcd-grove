/-
`Bucket.Cursor_kvw` (bbolt). `b.Cursor()` in the write transaction: a cursor over the bucket's entries now.
The trust boundary: bbolt's key-value contract as the backend uses it (`InvBbolt.lean`), from the
Go documentation; an axiom in `Proof/go_etcd_io/bbolt/Bucket__Cursor_kvw.lean`. Lean-first (no Rocq
counterpart); see `notes/decisions.md`, "The backend: the buffers, bbolt as a key-value contract,
the locks and the views".
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.bbolt backend

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `b.Cursor()` in the write transaction: a cursor over the bucket's entries now. -/
abbrev bbolt.Bucket.Cursor_kvw.spec : Prop :=
  ∀ (tx : Loc) (γ : DBNames) (D S : Data) (b : Loc) (n : GoString) (m : BktData),
  S.lookup n = some m →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownWTx tx γ D S ∗ wBkt tx b n }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"Cursor")) (Val #()))
  {{ (c : Loc), RET #c; ownCur tx c (bktEnts m) none ∗ ownWTx tx γ D S }}

end spec

end EtcdGrove
end Perennial
