/-
The apply package's lessor contract (`apply.isApplyLessor`) of the real lessor, from the
lessor's proofs (2026-10-13, unit 9 of the backend). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/lease/InvLessor.lean` and `LessorBackend.lean`.

`isApplyLessor_of_lessorInv`: the lessor at `lp` (`lease.lessorInv`, its configuration
`lease.lessorCfg`, its backend `lease.lessorBackend`, a contract on the backend's `Lease` bucket
under the batch lock) meets the contract's `isTxnLessor` (unit 8), `Grant` and `Checkpoint`
clauses (proved); its `Revoke` and `Lookup` clauses, not yet proved of the real lessor, are the
theorem's premises (stated as in the contract). The lessor's errors are the package's
`errors.New` variables (`lease.leaseErrVar`, the shape of `errVarLeaf`): `applyErrIs`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Contracts
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorContract
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Grant
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Checkpoint
public import Spec.go_etcd_io.etcd.server.v3.lease.Lease__TTL

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apply

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- A lessor error is one `errors.Is` can take. -/
theorem lessorErrIs_applyErrIs (err : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
      lease.lessorErrIs err ⊢ applyErrIs err := by
  iintro ⟨#Hpkg, #Herr⟩
  ihave Hli : (go_etcd_io.etcd.server.v3.lease.leaseInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hli with ⟨#Hnf, #Hex, #Htl, -⟩
  iunfold lease.lessorErrIs at Herr
  icases Herr with ⟨%g, %e, %Hg, #Hge, %He⟩
  ihave #Hv : errVarLeaf (GF := GF) g $$ []
  · rcases Hg with rfl | rfl | rfl
    · iunfold go_etcd_io.etcd.server.v3.lease.leaseErrVar at Hnf
      iunfold errVarLeaf; iunfold errLeaf; iunfold errMsgOk; iexact Hnf
    · iunfold go_etcd_io.etcd.server.v3.lease.leaseErrVar at Hex
      iunfold errVarLeaf; iunfold errLeaf; iunfold errMsgOk; iexact Hex
    · iunfold go_etcd_io.etcd.server.v3.lease.leaseErrVar at Htl
      iunfold errVarLeaf; iunfold errLeaf; iunfold errMsgOk; iexact Htl
  iapply errVar_applyErrIs g err $$ Hv
  iexists e; iframe Hge; ipureintro; exact He

/-- **The apply package's lessor contract, of the real lessor** at `lp`, for a store whose lessor
ghost map is the lessor's: its `isTxnLessor`, `Grant` and `Checkpoint` from the proofs, its
`Revoke` and `Lookup` clauses (not yet proved of the real lessor) given. -/
theorem isApplyLessor_of_lessorInv
    (hGL : lease.lessor.GetLease.spec (GF := GF) (hG := hG))
    (hAt : lease.lessor.Attach.spec (GF := GF) (hG := hG))
    (hDt : lease.lessor.Detach.spec (GF := GF) (hG := hG))
    (hSRD : lease.lessor.SetRangeDeleter.spec (GF := GF) (hG := hG))
    (hLk : lease.lessor.Lookup.spec (GF := GF) (hG := hG))
    (hGrant : lease.lessor.Grant.spec (GF := GF) (hG := hG))
    (hCk : lease.lessor.Checkpoint.spec (GF := GF) (hG := hG))
    (hTTL : lease.Lease.TTL.spec (GF := GF) (hG := hG))
    (lp : Loc) (γ : mvcc.StoreNames) (P : IProp GF) (f : val) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
      lease.lessorInv lp γ.leases ∗ lease.lessorCfg lp ∗ lease.lessorBackend lp P f ∗
      □ (∀ (id : w64) (log : mvcc.Log) (L : List w64) (Pre Q Post : IProp GF),
        {{ mvcc.csContract P f Pre Q Post ∗ txn.soleWriter γ log ∗ mvcc.storeWT γ ∗
            lease.leaseOwn γ.leases L ∗ txn.leasesKnown L (mvcc.stateAfter log) }}
          (App (Val (lp @!! go.GoType.PointerType lease.lessor.ty @!! go!"Revoke")) (Val #id))
        {{ (err : GoInterface), RET #err; (Post ∨ Pre) ∗
            (∃ (pend : List mvcc.Change) (L' : List w64), ⌜∀ c ∈ pend, c.isDel = true⌝ ∗
              txn.soleWriter γ (mvcc.commitLog log pend) ∗ lease.leaseOwn γ.leases L' ∗
              txn.leasesKnown L' (mvcc.stateAfter (mvcc.commitLog log pend))) ∗
            applyErrIs err }}) ∗
      □ (∀ id : w64,
        {{ True }} (App (Val (lp @!! go.GoType.PointerType lease.lessor.ty @!! go!"Lookup"))
          (Val #id))
        {{ (l : Loc), RET #l; ⌜l = null⌝ ∨ leaseIs l id }}) ⊢
      isApplyLessor (lease.lessorIface lp) γ P f := by
  iintro ⟨#Hpkg, #Hinv, #Hcfg, #Hbe, #HRevoke, #HLookup⟩
  iunfold isApplyLessor
  isplitl []
  · iapply lease.isTxnLessor_of_lessorInv hGL hAt hDt hSRD hLk lp γ.leases $$ [$Hpkg $Hinv]
  iexists (interface.mk (go.GoType.PointerType lease.lessor.ty) #lp)
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro !> %id %ttl %L %Pre %Q %Post %Φ !> ⟨Hcs, Hown⟩ HΦ
    iapply (hGrant lp γ.leases id ttl L P f Pre Q Post) $$ [Hcs Hown]
    · iframe; iframe #
    iintro !> %l %err (⟨%Hne, #Herr, Hown, HPre⟩ | ⟨%Hok, Hown, HPost, #HID, ⟨%t, #Ht⟩⟩)
    · iapply HΦ
      isplitl [HPre]
      · iright; iexact HPre
      isplitl [Hown]
      · iexists L; iframe Hown
        isplitr
        · ipureintro; intro x hx; exact hx
        ileft; ipureintro; exact Hne
      iapply lessorErrIs_applyErrIs err $$ [$Hpkg $Herr]
    · obtain ⟨Herr, Hln, Hnin⟩ := Hok
      subst Herr
      iapply HΦ
      isplitl [HPost]
      · ileft; iexact HPost
      isplitl [Hown]
      · iexists (L ++ [id]); iframe Hown
        isplitr
        · ipureintro; intro x hx; exact List.mem_append_left _ hx
        iright
        isplitr
        · ipureintro; rfl
        iexists id
        isplitl
        · iunfold leaseTTLIs
          iframe HID
          isplitr
          · ipureintro; exact Hln
          iintro !> %Φ' !> - HΦ'
          iapply (hTTL l t DFrac.discard) $$ [$Hpkg $Ht]
          iintro !> -
          iapply HΦ'; itrivial
        ipureintro; exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
      iapply applyErrIs_nil
  isplitr
  · iexact HRevoke
  isplitr
  · iintro !> %id %rem %Pre %Q %Post %Φ !> Hcs HΦ
    iapply (hCk lp γ.leases id rem P f Pre Q Post) $$ [Hcs]
    · iframe; iframe #
    iintro !> %err ⟨%He, HPP⟩
    subst He
    iapply HΦ
    iframe HPP
    iapply applyErrIs_nil
  · iexact HLookup

end proof

end apply
end EtcdGrove
end Perennial
