/-
`Tx.DeleteBucket_kv` (bbolt). `tx.DeleteBucket(name)`: the bucket deleted, or, if absent, `errors.ErrBucketNotFound`'s
value.
The trust boundary: bbolt's key-value contract as the backend uses it (`InvBbolt.lean`), from the
Go documentation; an axiom in `Proof/go_etcd_io/bbolt/Tx__DeleteBucket_kv.lean`. Lean-first (no Rocq
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

/-- `tx.DeleteBucket(name)`: the bucket deleted and its name's generation bumped, so that the
handles of the deleted bucket are no longer current (bbolt frees its nodes: an old handle panics
on `Put`, `issues/bbolt-deleted-bucket-handle.md`); or, if absent, `errors.ErrBucketNotFound`'s
value. (Until 2026-10-27 handles had no generation and outlived the delete: false, found by
`etc/spec-test/bbolt`.) -/
abbrev bbolt.Tx.DeleteBucket_kv.spec : Prop :=
  ∀ (tx : Loc) (γ : DBNames) (D S : Data) (G : GoString → Nat) (name : GoSlice) (n : GoString)
    (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownWTxG tx γ D S G ∗ name ↦*{dq} n }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"DeleteBucket")) (Val #name))
  {{ (err : GoInterface), RET #err; name ↦*{dq} n ∗
      ((⌜S.lookup n = none⌝ ∗ ownWTxG tx γ D S G ∗
        globalAddr go_etcd_io.bbolt.errors.ErrBucketNotFound ↦□ err) ∨
       (⌜S.lookup n ≠ none ∧ err = GoInterface.nil⌝ ∗ ownWTxG tx γ D (S.delete n) (fun x => if x = n then G n + 1 else G x))) }}

end spec

end EtcdGrove
end Perennial
