/-
`Tx.CreateBucketIfNotExists` (bbolt). `tx.CreateBucketIfNotExists(name)` (a name of `1..MaxKeySize` bytes): the bucket, empty if
it was absent, and its handle (bbolt copies the name).
The trust boundary: bbolt's key-value contract as the backend uses it (`InvBbolt.lean`), from the
Go documentation; an axiom in `Proof/go_etcd_io/bbolt/Tx__CreateBucketIfNotExists_kv.lean`. Lean-first (no Rocq
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

/-- `tx.CreateBucketIfNotExists(name)` (a name of `1..MaxKeySize` bytes): the bucket, empty if
it was absent, and its handle (bbolt copies the name). -/
abbrev bbolt.Tx.CreateBucketIfNotExists.kvspec : Prop :=
  ∀ (tx : Loc) (γ : DBNames) (D S : Data) (name : GoSlice) (n : GoString) (dq : DFrac),
  0 < n.length → n.length ≤ maxKeySize →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownWTx tx γ D S ∗ name ↦*{dq} n }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"CreateBucketIfNotExists")) (Val #name))
  {{ (b : Loc) (err : GoInterface), RET (PairV #b #err); ⌜err = GoInterface.nil⌝ ∗
      ownWTx tx γ D (if S.lookup n = none then S.insert n ∅ else S) ∗ wBkt tx b n ∗
      name ↦*{dq} n }}

end spec

end EtcdGrove
end Perennial
