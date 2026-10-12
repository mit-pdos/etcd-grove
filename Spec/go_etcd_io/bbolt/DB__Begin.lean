module
public import Proof.go_etcd_io.bbolt.DBBegin
public import Proof.go_etcd_io.bbolt.DBAcc
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

/-- `db.Begin(writable)` (sequential use, the database's logger the default one, so nothing is
logged): `beginRWTx` (no writer open; readers' txids in `[1, 2^64 - 2]`) or `beginTx` (fewer
readers than an RWMutex allows). -/
abbrev DB.Begin.spec : Prop :=
  ∀ (I : FLImpl (GF := GF)) (dbl : Loc) (γ : DBNames) (σ : DBState) (w : Bool),
  (if w then I.ReleasePendingSpec ∧ σ.wr = none ∧
      (∀ r ∈ σ.fl.readonly, 1 ≤ uint.Z r ∧ uint.Z r < 2 ^ 64 - 1)
   else I.AddReadonlySpec ∧ σ.readers.size + 1 < Int.toNat sync.rwmutex.actualMaxReaders) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownDB I dbl γ σ }}
    (App (Val (dbl @!! go.GoType.PointerType DB.ty @!! go!"Begin")) (Val #w))
  {{ (txl : Loc) (err : GoInterface), RET (PairV #txl #err);
      if w then
        (⌜err ≠ interface.nil⌝ ∗ ownDB I dbl γ σ) ∨
        (⌜err = interface.nil⌝ ∗ ∃ (fl' : FLState) (wr : Reader) (v0 v1 : internal.common.Meta),
          ⌜fl'.equiv σ.fl.releasePending⌝ ∗
          ownDB I dbl γ ({ σ with fl := fl' }.addWriter txl wr) ∗
          wtxInit dbl txl wr σ.data σ.ps v0 v1)
      else
        ⌜err = interface.nil⌝ ∗ ∃ (k : Nat) (r : Reader), ⌜σ.readers !! k = none⌝ ∗
          ownDB I dbl γ (σ.addReader k r) ∗ ownReadTx dbl γ txl k r σ.data σ.ps false }}

end spec

end bbolt
end EtcdGrove
end Perennial
