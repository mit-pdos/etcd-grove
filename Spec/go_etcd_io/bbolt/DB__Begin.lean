module
public import Proof.go_etcd_io.bbolt.DBBegin
public import Proof.go_etcd_io.bbolt.DBAcc

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

/-- `db.Begin(false)` (sequential use, no writer open, the database's logger the default one,
so nothing is logged): `beginTx`. -/
abbrev DB.Begin.spec : Prop :=
  ∀ (I : FLImpl (GF := GF)) (dbl : Loc) (γ : DBNames) (σ : DBState),
  I.AddReadonlySpec → σ.readers.size + 1 < Int.toNat sync.rwmutex.actualMaxReaders →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownDB I dbl γ σ }}
    (App (Val (dbl @!! go.GoType.PointerType DB.ty @!! go!"Begin")) (Val #false))
  {{ (txl : Loc), RET (PairV #txl #interface.nil);
      ∃ (k : Nat) (r : Reader), ⌜σ.readers !! k = none⌝ ∗
        ownDB I dbl γ (σ.addReader k r) ∗ ownReadTx dbl γ txl k r σ.data σ.ps false }}

end spec

end bbolt
end EtcdGrove
end Perennial
