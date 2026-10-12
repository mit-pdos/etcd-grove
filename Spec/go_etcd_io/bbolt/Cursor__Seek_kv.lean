/-
`Cursor.Seek_kv` (bbolt). `c.Seek(key)`: the first entry whose key is not below `key` (nil, nil past the end).
The trust boundary: bbolt's key-value contract as the backend uses it (`InvBbolt.lean`), from the
Go documentation; an axiom in `Proof/go_etcd_io/bbolt/Cursor__Seek_kv.lean`. Lean-first (no Rocq
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

/-- `c.Seek(key)`: the first entry whose key is not below `key` (nil, nil past the end). -/
abbrev bbolt.Cursor.Seek_kv.spec : Prop :=
  ∀ (tx c : Loc) (es : List Ent) (pos : Option Nat) (q : Qp) (key : GoSlice) (kb : GoString)
    (dk : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownCur tx c es pos ∗ txLive tx q ∗ key ↦*{dk} kb }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"Seek")) (Val #key))
  {{ (k v : GoSlice), RET (PairV #k #v); ownCur tx c es (some (seekIdx es kb)) ∗ txLive tx q ∗
      key ↦*{dk} kb ∗ curAt tx es (seekIdx es kb) k v }}

end spec

end EtcdGrove
end Perennial
