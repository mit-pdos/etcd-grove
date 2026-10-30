module
public import Proof.go_etcd_io.bbolt.DBEnd

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

/-- `db.removeTx(tx)` of an open read transaction (sequential use, no writer open): the
database no longer accounts for it (`DBState.removeReader`), and gets its fractions back; the
transaction is left (its statistics merged into the database's). -/
abbrev DB.removeTx.spec : Prop :=
  ∀ (I : FLImpl (GF := GF)) (dbl : Loc) (γ : DBNames) (σ : DBState) (txl : Loc) (k : Nat)
    (r : Reader) (m : Bool),
  I.RemoveReadonlySpec →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownDB I dbl γ σ ∗
      ownReadTx dbl γ txl k r σ.data σ.ps m }}
    (App (Val (dbl @!! go.GoType.PointerType DB.ty @!! go!"removeTx")) (Val #txl))
  {{ RET #(); ∃ (ro : List w64) (t : Tx), ⌜σ.readers !! k = some r⌝ ∗
      ownDB I dbl γ (σ.removeReader k r ro) ∗ txl ↦ t ∗ ⌜t.db' = dbl ∧ t.writable' = false⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
