/-
`Cursor.Next` (bbolt). `c.Next()` of a positioned cursor: the next entry (nil, nil past the end, where it stays).
The trust boundary: bbolt's key-value contract as the backend uses it (`InvBbolt.lean`), from the
Go documentation; an axiom in `Proof/go_etcd_io/bbolt/Cursor__Next_kv.lean`. Lean-first (no Rocq
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

/-- `c.Next()` of a positioned cursor: the next entry (nil, nil past the end, where it stays). -/
abbrev bbolt.Cursor.Next.kvspec : Prop :=
  ∀ (tx c : Loc) (es : List Ent) (i : Nat) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownCur tx c es (some i) ∗ txLive tx q }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"Next")) (Val #()))
  {{ (k v : GoSlice), RET (PairV #k #v); ownCur tx c es (some (min (i + 1) es.length)) ∗
      txLive tx q ∗ curAt tx es (i + 1) k v }}

end spec

end EtcdGrove
end Perennial
