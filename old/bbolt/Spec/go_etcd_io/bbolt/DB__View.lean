module
public import Spec.go_etcd_io.bbolt.Tx__Rollback
public import Spec.go_etcd_io.bbolt.DB__Begin

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

variable [AllG GF]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

/-- `fn`'s spec, as `View` calls it: given the database and an open read transaction (managed:
`fn` must not roll it back) and `P`, it returns an error `e` with the transaction still open,
`Q e`, and the database (in some state, its mapping the same). -/
def viewFnSpec (I : FLImpl (GF := GF)) (dbl : Loc) (γ : DBNames) (fn : GoFunc) (P : IProp GF)
    (Q : GoInterface → IProp GF) : Prop :=
  ∀ (txl : Loc) (k : Nat) (r : Reader) (σ1 : DBState), σ1.readers !! k = some r →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownDB I dbl γ σ1 ∗ ownReadTx dbl γ txl k r σ1.data σ1.ps true ∗ P }}
    (App (Val #fn) (Val #txl))
  {{ (e : GoInterface), RET #e; ∃ (σ2 : DBState), ⌜σ2.data = σ1.data ∧ σ2.ps = σ1.ps⌝ ∗
      ownDB I dbl γ σ2 ∗ ownReadTx dbl γ txl k r σ1.data σ1.ps true ∗ Q e }}

/-- `db.View(fn)` (sequential use, no writer open, the default logger): `fn` on a new read
transaction, rolled back after; `fn`'s error. -/
abbrev DB.View.spec : Prop :=
  ∀ (I : FLImpl (GF := GF)) (dbl : Loc) (γ : DBNames) (σ : DBState) (fn : GoFunc)
    (P : IProp GF) (Q : GoInterface → IProp GF),
  I.AddReadonlySpec → I.RemoveReadonlySpec →
  σ.readers.size + 1 < Int.toNat sync.rwmutex.actualMaxReaders →
  viewFnSpec I dbl γ fn P Q →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownDB I dbl γ σ ∗ P }}
    (App (Val (dbl @!! go.GoType.PointerType DB.ty @!! go!"View")) (Val #fn))
  {{ (e : GoInterface), RET #e; ∃ (σ' : DBState), ownDB I dbl γ σ' ∗ Q e }}

end spec

end bbolt
end EtcdGrove
end Perennial
