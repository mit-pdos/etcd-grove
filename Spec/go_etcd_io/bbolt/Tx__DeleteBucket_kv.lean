/-
`Tx.DeleteBucket_kv` (bbolt). `tx.DeleteBucket(name)`.
A corollary of bbolt's proved `Tx.DeleteBucket` (`Spec/go_etcd_io/bbolt/Tx__DeleteBucket.lean`) over the backend's
vocabulary (`InvBbolt.lean`), proved in `Proof/go_etcd_io/bbolt/Tx__DeleteBucket_kv.lean` (stage S1 of
`notes/bbolt-integration-plan.md`, 2026-11-17; until then an axiom, the backend's trust boundary).
Lean-first (no Rocq counterpart); see `notes/decisions.md`, "The backend: the buffers, bbolt as a
key-value contract, the locks and the views".
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
on `Put`, `nonissues/bbolt-deleted-bucket-handle.md`); or, if absent, the value of
`errors.ErrBucketNotFound` or (S1: bbolt's proved spec, for the empty name,
`nonissues/bbolt-deletebucket-empty-name.md`) of `errors.ErrIncompatibleValue`. -/
abbrev bbolt.Tx.DeleteBucket_kv.spec : Prop :=
  ∀ (tx : Loc) (γ : DBNames) (D S : backend.Data) (G : GoString → Nat) (name : GoSlice) (n : GoString)
    (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownWTxG tx γ D S G ∗ name ↦*{dq} n }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"DeleteBucket")) (Val #name))
  {{ (err : GoInterface), RET #err; name ↦*{dq} n ∗
      ((⌜S.lookup n = none⌝ ∗ ownWTxG tx γ D S G ∗
        globalAddr go_etcd_io.bbolt.errors.ErrBucketNotFound ↦□ err) ∨
       (⌜n = [] ∧ S.lookup n = none⌝ ∗ ownWTxG tx γ D S G ∗
        globalAddr go_etcd_io.bbolt.errors.ErrIncompatibleValue ↦□ err) ∨
       (⌜S.lookup n ≠ none ∧ err = GoInterface.nil⌝ ∗
        ownWTxG tx γ D (S.delete n) (fun x => if x = n then G n + 1 else G x))) }}

end spec

end EtcdGrove
end Perennial
