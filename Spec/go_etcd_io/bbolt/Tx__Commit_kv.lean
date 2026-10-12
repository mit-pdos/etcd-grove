/-
`Tx.Commit_kv` (bbolt). `tx.Commit()` of the write transaction: its contents committed (the write token back), or
an error.
The trust boundary: bbolt's key-value contract as the backend uses it (`InvBbolt.lean`), from the
Go documentation; an axiom in `Proof/go_etcd_io/bbolt/Tx__Commit_kv.lean`. Lean-first (no Rocq
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

/-- `tx.Commit()` of the write transaction: its contents committed (the write token back), or
an error. -/
abbrev bbolt.Tx.Commit_kv.spec : Prop :=
  ∀ (db tx : Loc) (γ : DBNames) (D S : Data),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownDB db γ D ∗ txDB tx db ∗ ownWTx tx γ D S }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"Commit")) (Val #()))
  {{ (err : GoInterface), RET #err; txDone tx ∗
      ((⌜err = GoInterface.nil⌝ ∗ ownDB db γ S ∗ wrTok γ) ∨ ⌜err ≠ GoInterface.nil⌝) }}

end spec

end EtcdGrove
end Perennial
