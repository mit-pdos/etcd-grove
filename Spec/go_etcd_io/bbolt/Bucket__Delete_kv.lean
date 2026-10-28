/-
`Bucket.Delete_kv` (bbolt). `b.Delete(key)` in the write transaction: the entry removed (if present).
The trust boundary: bbolt's key-value contract as the backend uses it (`InvBbolt.lean`), from the
Go documentation; an axiom in `Proof/go_etcd_io/bbolt/Bucket__Delete_kv.lean`. Lean-first (no Rocq
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `b.Delete(key)` in the write transaction: the entry removed (if present). -/
abbrev bbolt.Bucket.Delete_kv.spec : Prop :=
  ∀ (tx : Loc) (γ : DBNames) (D S : Data) (G : GoString → Nat) (b : Loc) (n : GoString) (g : Nat)
    (m : BktData) (key : GoSlice) (kb : GoString) (dk : DFrac),
  G n = g → S.lookup n = some m →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownWTxG tx γ D S G ∗ wBkt tx b n g ∗ key ↦*{dk} kb }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"Delete")) (Val #key))
  {{ RET #GoInterface.nil; ownWTxG tx γ D (S.insert n (m.delete kb)) G ∗ key ↦*{dk} kb }}

end spec

end EtcdGrove
end Perennial
