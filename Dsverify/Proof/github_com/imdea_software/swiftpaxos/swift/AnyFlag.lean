/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/AnyFlag.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`deliveredAny` (fork change P2-A, notes/prove-swift.md §13): its loads and stores under its
invariant `swift.anyInv r` (Proof/swift/Defs.lean).

* `swift.wp_anyLoad`: `r.deliveredAny.Load()` returns some Boolean (BeTheLeader);
* `swift.wp_anyStore`: `r.deliveredAny.Store(v)` (deliver: `true`; handleSync: `false`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Defs
public import Perennial.Spec.sync.atomic.Bool__Load
public import Perennial.Spec.sync.atomic.Bool__Store

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [sync.atomic.Assumptions]

theorem swift.wp_anyLoad (wp_Load : sync.atomic.Bool.Load.spec (GF := netDistGF) (hG := hG))
    (r : Loc) :
    {{ swift.anyInv r }}
      (App (Val ((swift.fld r go!"deliveredAny") @!! go.GoType.PointerType sync.atomic.Bool'.ty
        @!! go!"Load")) (Val #()))
    {{ (b : Bool), RET #b; True }} := by
  iintro %Φ #Hany HΦ
  iunfold swift.anyInv at Hany
  icases Hany with ⟨#Hpkg, #Hinv⟩
  iapply (wp_Load (swift.fld r go!"deliveredAny") (DFrac.own 1)) $$ %Φ Hpkg
  iinv Hinv with ⟨%b, Hb⟩ Hclose
  imod (fupd_mask_subseteq (E1 := ⊤ \ ↑swift.anyN) (E2 := ∅) (by simp)) with Hback
  imodintro
  inext
  iexists b
  iframe Hb
  iintro Hb
  imod Hback with -
  imod Hclose $$ [Hb] with -
  · inext; iexists b; iexact Hb
  imodintro
  iapply HΦ
  itrivial

theorem swift.wp_anyStore (wp_Store : sync.atomic.Bool.Store.spec (GF := netDistGF) (hG := hG))
    (r : Loc) (v : Bool) :
    {{ swift.anyInv r }}
      (App (Val ((swift.fld r go!"deliveredAny") @!! go.GoType.PointerType sync.atomic.Bool'.ty
        @!! go!"Store")) (Val #v))
    {{ RET #(); True }} := by
  iintro %Φ #Hany HΦ
  iunfold swift.anyInv at Hany
  icases Hany with ⟨#Hpkg, #Hinv⟩
  iapply (wp_Store (swift.fld r go!"deliveredAny") v) $$ %Φ Hpkg
  iinv Hinv with ⟨%b, Hb⟩ Hclose
  imod (fupd_mask_subseteq (E1 := ⊤ \ ↑swift.anyN) (E2 := ∅) (by simp)) with Hback
  imodintro
  inext
  iexists b
  iframe Hb
  iintro Hb
  imod Hback with -
  imod Hclose $$ [Hb] with -
  · inext; iexists v; iexact Hb
  imodintro
  iapply HΦ
  itrivial

end proof

end Perennial.github_com.imdea_software.swiftpaxos
