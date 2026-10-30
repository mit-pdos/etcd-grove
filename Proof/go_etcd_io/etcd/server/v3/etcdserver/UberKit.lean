/-
**The server's uber-applier contracts with auth on, from the construction's kit** (step 6 of the
auth-mode merge, 2026-10-30; `notes/decisions.md`, "Step 6: one `apply.Apply.spec`"). Lean-first (no
Rocq counterpart).

Whoever constructs the uber-applier establishes its contract: with auth on, `NewServer` builds the
row `srvUberOn` (the uber-applier's latest-state KV and admin contracts, `apply.uberKVC`/
`apply.uberAdmC`, for every uber-applier the server holds) once, from `uberKitM true`: the
uber-applier's own latest-state triples and the base applier's interface-method specs they are
built over (`srv_uberKVL_on`, `srv_uberAuthStepsL_at`). `uberKitM false` is `True`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyNormalOn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section kit
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **What `NewServer` takes to build the uber-applier's contracts, in the auth mode `on`**: `True`
off; on, the uber-applier's latest-state triples and the base applier's interface-method specs
the server's row is built over. -/
def uberKitM (on : Bool) : Prop :=
  match on with
  | false => True
  | true =>
    apply.uberApplier.Apply.kvSpecL (GF := GF) (hG := hG) ∧
    apply.uberApplier.Apply.adminSpecL (GF := GF) (hG := hG) ∧
    apply.authApplierV3.Range.specL (GF := GF) (hG := hG) ∧
    apply.authApplierV3.DeleteRange.specL (GF := GF) (hG := hG) ∧
    apply.authApplierV3.Put.specL (GF := GF) (hG := hG) ∧
    apply.authApplierV3.Txn.specL (GF := GF) (hG := hG) ∧
    apply.applierV3backend.UserAdd.fuelSpecX (GF := GF) (hG := hG) ∧
    apply.applierV3backend.RoleAdd.fuelSpecX (GF := GF) (hG := hG) ∧
    apply.applierV3backend.UserGrantRole.fuelSpecX (GF := GF) (hG := hG) ∧
    apply.applierV3backend.RoleGrantPermission.fuelSpecX (GF := GF) (hG := hG) ∧
    apply.applierV3backend.AuthEnable.fuelSpecX (GF := GF) (hG := hG) ∧
    apply.applierV3backend.Authenticate.specX (GF := GF) (hG := hG) ∧
    apply.authApplierV3.Apply.specL (GF := GF) (hG := hG) ∧
    apply.applierV3backend.Apply.spec (GF := GF) (hG := hG)

/-- **The row from the kit**: `srvUberOn s` (with the apply package initialized). -/
theorem srvUberOn_of_kit (hk : uberKitM (GF := GF) (hG := hG) true) (s : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ⊢
      srvUberOn (GF := GF) s := by
  obtain ⟨hK, hAd, hRange, hDel, hPut, hTxn, hUA, hRA, hUGR, hRGP, hAE, hAu, hApplyL, hApply⟩ := hk
  iintro #Hpkg
  iunfold srvUberOn
  iintro !> %E %γa %ua %hM #Hb
  isplitl
  · iintro #Hln
    ihave ⟨%stl, #Hf, #HL⟩ := srv_uberKVL_on hRange hDel hPut hTxn s ua E γa hM $$ [$Hpkg $Hb $Hln]
    iexists stl
    iframe Hf
    iapply apply.uberKVC_of hK
    iframe Hpkg HL
  · iintro %stl %bel %T #Hf #Hsteps
    iapply apply.uberAdmC_of hAd
    iframe Hpkg
    iapply srv_uberAuthStepsL_at hUA hRA hUGR hRGP hAE hAu hApplyL hApply s ua E γa stl bel T hM
    iframe Hpkg Hb Hf Hsteps

end kit

end EtcdGrove
end Perennial
