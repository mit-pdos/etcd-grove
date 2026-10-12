module
public import Proof.go_etcd_io.bbolt.DBWriter

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

/-- `db.beginRWTx()` (sequential use, no writer open; every open reader's txid in
`[1, 2^64 - 2]`): an error if the database is read-only; otherwise a write transaction of the
current meta, the database with it as its writer (`DBState.addWriter`) and its freelist's
pending pages that no reader sees released (`ReleasePendingPages`, up to order). -/
abbrev DB.beginRWTx.spec : Prop :=
  ∀ (I : FLImpl (GF := GF)) (dbl : Loc) (γ : DBNames) (σ : DBState),
  I.ReleasePendingSpec → σ.wr = none →
  (∀ r ∈ σ.fl.readonly, 1 ≤ uint.Z r ∧ uint.Z r < 2 ^ 64 - 1) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownDB I dbl γ σ }}
    (App (Val (dbl @!! go.GoType.PointerType DB.ty @!! go!"beginRWTx")) (Val #()))
  {{ (txl : Loc) (err : GoInterface), RET (PairV #txl #err);
      (⌜err ≠ interface.nil⌝ ∗ ownDB I dbl γ σ) ∨
      (⌜err = interface.nil⌝ ∗ ∃ (fl' : FLState) (w : Reader) (v0 v1 : internal.common.Meta),
        ⌜fl'.equiv σ.fl.releasePending⌝ ∗
        ownDB I dbl γ ({ σ with fl := fl' }.addWriter txl w) ∗
        wtxInit dbl txl w σ.data σ.ps v0 v1) }}

end spec

end bbolt
end EtcdGrove
end Perennial
