/-
**The auto-compactor's environment on the server** (M2, `notes/m2-plan.md`, S4; review round 1,
S3-3): the laws that make the server what the frozen compactor contracts take, so that
`EtcdServer.Compact.spec` is checked against `v3compactor.compactableOk`:

* `errTreeOk_of_applyErrIs`, `errTreeOk_nil`: an error the request path reports, or `nil`, is one
  the compactor's `errors.Is(err, ErrCompacted)` can test (`v3compactor.errTreeOk`);
* `compactableOk_server`: the server is a `Compactable` for the compactor's revision permit over
  `srvRevLb` (a permit's `□ RevLb (r + ret)` gives `r` reached, what `Compact.spec` takes), with the
  resource every call gives back (the caller's reader slots and the store's reader).

Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Compact
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3 go_etcd_io.etcd.server.v3.etcdserver

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **An error the request path reports is one `errors.Is` can test** (the compactor's
`errTreeOk`: `applyErrIs`'s tree, whose target condition `ptrTarget` is the compactor's). -/
theorem errTreeOk_of_applyErrIs (err : GoInterface) :
    applyErrIs (GF := GF) err ⊢ v3compactor.errTreeOk err := by
  iintro H
  iunfold applyErrIs at H
  icases H with ⟨#Ht, -⟩
  iunfold v3compactor.errTreeOk
  imodintro
  iExactEq Ht; rfl

/-- `nil` is one too. -/
theorem errTreeOk_nil : ⊢ v3compactor.errTreeOk (GF := GF) GoInterface.nil := by
  iintro
  iapply errTreeOk_of_applyErrIs
  iapply applyErrIs_nil

/-- `Compact`'s outcome gives what the compactor tests of its error. -/
theorem errTreeOk_of_compactOutIs (E : apply.AEnv GF) (resp : Loc) (err : GoInterface) :
    compactOutIs (GF := GF) E resp err ⊢ v3compactor.errTreeOk err := by
  iintro H
  iunfold compactOutIs at H
  icases H with (⟨%Hok, -⟩ | ⟨-, Herr⟩)
  · rw [Hok.1]; iapply errTreeOk_nil
  · iapply errTreeOk_of_applyErrIs; iexact Herr

/-- **What a compactor's `Compact` call borrows and gives back** on the server `s`: the caller's
reader slots (the lead-time and logger mutexes', the auth store's, `E.RD`) and the store's reader. -/
def srvCompactR (s : Loc) (E : apply.AEnv GF) : IProp GF :=
  iprop(srvLeadTimeReader s ∗ srvLgReader s ∗ E.RD ∗ mvcc.storeReaderC E.s E.γ)

/-- **The server is the compactor's `Compactable`** (review round 1, S3-3): from `Compact.spec`,
for the revision compactor's permit over `srvRevLb` at a non-negative retention, borrowing
`srvCompactR`. -/
theorem compactableOk_server (hC : EtcdServer.Compact.spec (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (ret : Int) (hret : 0 ≤ ret) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqC s E ρ ∗ isServerRead s E γr ∗ idCred ρ.ids 1 ⊢
      v3compactor.compactableOk
        (interface.mkOk (go.GoType.PointerType EtcdServer.ty) #s)
        (v3compactor.revPermit (srvRevLb E.γ) ret) (srvCompactR s E) := by
  iintro ⟨#Hpkg, #Hsrv, #Hsrd, #Hcred⟩
  iunfold v3compactor.compactableOk
  iexists _
  isplitr
  · ipureintro; rfl
  imodintro
  iintro %r %ctx %cd %p %Φ !> ⟨Hpm, HR, #Hctx, #Htr, Hreq⟩ HΦ
  iunfold v3compactor.revPermit at Hpm
  icases Hpm with ⟨%Hr, #Hlb⟩
  iunfold srvCompactR at HR
  icases HR with ⟨Hlt, Hlr, Hrd, Hst⟩
  ihave #Hlb' : srvRevLb E.γ r $$ []
  · iapply srvRevLb_mono E.γ r (r + ret) (by omega); iexact Hlb
  -- (M2, the storage side, item 35) the permit's revision is past `0`: the scope premise
  iapply (hC s E ρ γr ctx cd p r (by omega)) $$ [Hlt Hlr Hrd Hst Hreq]
  · iframe Hlt Hlr Hrd Hst Hreq; iframe #
  inext
  iintro %resp %err ⟨Hlt, Hlr, Hrd, Hst, Hout⟩
  iapply HΦ
  iunfold srvCompactR
  iframe Hlt Hlr Hrd Hst
  iapply errTreeOk_of_compactOutIs; iexact Hout

end laws

end EtcdGrove
end Perennial
