/-
`Bucket.Cursor_kvr` (bbolt). `b.Cursor()` in a read transaction: a cursor over the bucket's entries, not positioned.
The trust boundary: bbolt's key-value contract as the backend uses it (`InvBbolt.lean`), from the
Go documentation; an axiom in `Proof/go_etcd_io/bbolt/Bucket__Cursor_kvr.lean`. Lean-first (no Rocq
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

/-- `b.Cursor()` in a read transaction: a cursor over the bucket's entries, not positioned. -/
abbrev bbolt.Bucket.Cursor_kvr.spec : Prop :=
  ∀ (tx b : Loc) (q : Qp) (es : List Ent),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ rBkt tx b es ∗ rtxStats tx ∗ txLive tx q }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"Cursor")) (Val #()))
  {{ (c : Loc), RET #c; ownCur tx c es none ∗ rtxStats tx ∗ txLive tx q }}

end spec

end EtcdGrove
end Perennial
