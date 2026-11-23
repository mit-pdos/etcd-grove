/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/DescBundle.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
**The Löb bundle** (round 44, sv-swb; D53 (3); plan R8.2 (10), F8): `handleDesc`'s spec as an
`IProp` (`handleDescR`), proved by Löb induction from the top-down proof (`handleDesc.wp_proofT`,
whose pre carries `depAll`) and `depAll` under the induction hypothesis (`dep_of`: a creation from an
owner forks `handleDesc`, `wp_coreO`). Then `handleDesc.specD` (`specD_of`) and `depAll` itself
(`depAll_of_bundle`), which `seqSpecD.wp_proofT` takes.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HandleDescProofDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section bundle
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions] [hook.Assumptions]

/-- **`go r.handleDesc(desc, cmdId)`'s spec as an `IProp`** (the bundle's second part). -/
def swift.handleDescR (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX) (RC : Loc → Loc → w32 → IProp netDistGF) :
    IProp netDistGF :=
  iprop(∀ (rp : Loc) (g : swift.DescG) (d : Loc) (y : swift.CommandId) (γi γsg : GName),
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
        swift.goPre γ0 γc γm x rp (RC rp) g d y γi γsg }}
      (App (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"handleDesc")) (Val #d))
        (Val #y))
    {{ RET #(); True }})

instance swift.handleDescR_persistent (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX)
    (RC : Loc → Loc → w32 → IProp netDistGF) : Persistent (swift.handleDescR γ0 γc γm x RC) := by
  unfold swift.handleDescR; infer_instance

/-- **The bundle** (see the file header): Löb induction over `handleDescR`. -/
theorem swift.descBundle (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX) (RC : Loc → Loc → w32 → IProp netDistGF)
    (wp_hd : swift.Replica.handleDesc.specDD γ0 γc γm x RC)
    (dep_of : ⊢ □ ▷ swift.handleDescR γ0 γc γm x RC -∗ swift.depAll γ0 γc γm x) :
    ⊢ swift.handleDescR γ0 γc γm x RC := by
  iloeb as IH
  ihave #Hd := dep_of $$ IH
  iunfold swift.handleDescR
  iintro %rp %g %d %y %γi %γsg
  imodintro
  iintro %Φ ⟨#Hpkg, Hpre⟩ HΦ
  iapply (wp_hd rp g d y γi γsg) $$ [Hpre] [HΦ]
  · iframe Hpkg Hpre Hd
  · iexact HΦ

/-- `handleDesc.specD` from the bundle. -/
theorem swift.Replica.handleDesc.specD_of (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX)
    (RC : Loc → Loc → w32 → IProp netDistGF) (h : ⊢ swift.handleDescR γ0 γc γm x RC) :
    swift.Replica.handleDesc.specD γ0 γc γm x RC := by
  intro rp g d y γi γsg
  iintro %Φ Hpre HΦ
  ihave #H := h
  iunfold swift.handleDescR at H
  ispecialize H $$ %rp %g %d %y %γi %γsg
  iapply H $$ [Hpre] [HΦ]
  · iexact Hpre
  · iexact HΦ

/-- `depAll` from the bundle. -/
theorem swift.depAll_of_bundle (γ0 : sp.Names) (γc γm : GName) (x : swift.RunX)
    (RC : Loc → Loc → w32 → IProp netDistGF) (h : ⊢ swift.handleDescR γ0 γc γm x RC)
    (dep_of : ⊢ □ ▷ swift.handleDescR γ0 γc γm x RC -∗ swift.depAll γ0 γc γm x) :
    ⊢ swift.depAll γ0 γc γm x := by
  ihave #H := h
  iapply dep_of
  imodintro
  inext
  iexact H

end bundle

end Perennial.github_com.imdea_software.swiftpaxos
