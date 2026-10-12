/-
`Tx.Bucket` (bbolt). `tx.Bucket(name)` in the write transaction: its handle of the bucket, or nil.
The trust boundary: bbolt's key-value contract as the backend uses it (`InvBbolt.lean`), from the
Go documentation; an axiom in `Proof/go_etcd_io/bbolt/Tx__Bucket_kvw.lean`. Lean-first (no Rocq
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

/-- `tx.Bucket(name)` in the write transaction: its handle of the bucket, or nil. -/
abbrev bbolt.Tx.Bucket.kvwspec : Prop :=
  ∀ (tx : Loc) (γ : DBNames) (D S : Data) (name : GoSlice) (n : GoString) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownWTx tx γ D S ∗ name ↦*{dq} n }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"Bucket")) (Val #name))
  {{ (b : Loc), RET #b; ownWTx tx γ D S ∗ name ↦*{dq} n ∗
      ((⌜S.lookup n = none ∧ b = Loc.null⌝) ∨
       (⌜S.lookup n ≠ none ∧ b ≠ Loc.null⌝ ∗ wBkt tx b n)) }}

end spec

end EtcdGrove
end Perennial
