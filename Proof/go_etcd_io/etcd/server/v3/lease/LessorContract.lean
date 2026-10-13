/-
mvcc's lessor contract (`mvcc.isLessor`) and the txn package's (`txn.isTxnLessor`, with
`Lookup`) derived from the lessor's proofs (2026-10-13, unit 8). Lean-first (no Rocq
counterpart); see `InvLessor.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__GetLease
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Attach
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Detach
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__SetRangeDeleter
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Lookup
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lease

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- **mvcc's lessor contract, of the real lessor**: the lessor at `lp` (`lessorInv`) is the
store's `isLessor` (its `GetLease`, `Attach`, `Detach`, `SetRangeDeleter`). -/
theorem isLessor_of_lessorInv
    (hGL : lease.lessor.GetLease.spec (GF := GF) (hG := hG))
    (hAt : lease.lessor.Attach.spec (GF := GF) (hG := hG))
    (hDt : lease.lessor.Detach.spec (GF := GF) (hG := hG))
    (hSRD : lease.lessor.SetRangeDeleter.spec (GF := GF) (hG := hG))
    (lp : Loc) (γl : GName) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ lessorInv lp γl ⊢
      mvcc.isLessor (lessorIface lp) γl := by
  iintro ⟨#Hpkg, #Hinv⟩
  ihave #Hinv' := Hinv
  iunfold lessorInv at Hinv'
  icases Hinv' with ⟨%Hlp, #Hpin, -⟩
  iunfold mvcc.isLessor
  iexists lp
  isplitr
  · ipureintro; rfl
  iframe Hpin
  isplitr
  · iintro !> %item %Φ !> Hrd HΦ
    iapply (hGL lp γl item) $$ [Hrd] HΦ
    iframe Hpkg Hinv Hrd
  isplitr
  · iintro !> %id %items %l %dq %L %Φ !> ⟨Hown, %Hin, Hitems⟩ HΦ
    iunfold leaseOwn at Hown
    iapply (hAt lp γl id items l dq _ L) $$ [Hown Hitems]
    · iframe Hpkg Hinv Hown Hitems
    iintro !> %err ⟨Hown, Hitems, %Herr⟩
    rw [Herr Hin]
    iapply HΦ
    iunfold leaseOwn
    iframe Hown Hitems
  isplitr
  · iintro !> %id %items %l %dq %Φ !> Hitems HΦ
    iapply (hDt lp γl id items l dq) $$ [Hitems] HΦ
    iframe Hpkg Hinv Hitems
  · iintro !> %f %Φ !> - HΦ
    iapply (hSRD lp γl f) $$ [] HΦ
    iframe Hpkg Hinv

/-- **The txn package's lessor contract, of the real lessor**: mvcc's, and `Lookup(id)` by the
lease owner (`lessorUser γl L`) returns nil or a lease of the live set `L`. -/
theorem isTxnLessor_of_lessorInv
    (hGL : lease.lessor.GetLease.spec (GF := GF) (hG := hG))
    (hAt : lease.lessor.Attach.spec (GF := GF) (hG := hG))
    (hDt : lease.lessor.Detach.spec (GF := GF) (hG := hG))
    (hSRD : lease.lessor.SetRangeDeleter.spec (GF := GF) (hG := hG))
    (hLk : lease.lessor.Lookup.spec (GF := GF) (hG := hG))
    (lp : Loc) (γl : GName) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ lessorInv lp γl ⊢
      txn.isTxnLessor (lessorIface lp) γl := by
  iintro ⟨#Hpkg, #Hinv⟩
  iunfold txn.isTxnLessor
  isplitl []
  · iapply isLessor_of_lessorInv hGL hAt hDt hSRD lp γl $$ [$Hpkg $Hinv]
  iexists ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty, #lp⟩
  isplitr
  · ipureintro; rfl
  ihave #Hinv' := Hinv
  iunfold lessorInv at Hinv'
  icases Hinv' with ⟨%Hlp, #Hpin, -⟩
  iintro !> %id %L %Φ !> Hu HΦ
  iunfold lessorUser at Hu
  icases Hu with ⟨Hown, Hrdo⟩
  iunfold lessorRdOf at Hrdo
  icases Hrdo with ⟨%lp', #Hpin', Hrd⟩
  ihave %Heq := lessorPin_agree γl lp lp' $$ [$Hpin $Hpin']
  subst Heq
  iunfold leaseOwn at Hown
  iapply (hLk lp γl id _ L) $$ [Hrd Hown]
  · iframe Hpkg Hinv Hrd Hown
  iintro !> %l ⟨Hrd, Hown, %Hl, -⟩
  iapply HΦ
  isplitl [Hrd Hown]
  · iunfold lessorUser; iunfold leaseOwn; iframe Hown
    iunfold lessorRdOf; iexists lp; iframe Hpin Hrd
  by_cases hn : l = null
  · ileft; ipureintro; exact hn
  · iright; ipureintro
    exact Classical.byContradiction (fun hni => hn (Hl.2 hni))

end proof

end lease
end EtcdGrove
end Perennial
