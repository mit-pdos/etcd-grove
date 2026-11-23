/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/CmapBridge.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The concurrent map's strong specs (Proof/cmap/Specs.lean, over its ghost view `cmapView`) as
the HOCAP-form instances the descriptor proofs state (`swift.cmapHasV.spec`,
`swift.cmapSetV.spec`, Proof/swift/Deliver.lean): `swift.cmapHasV_of`, `swift.cmapSetV_of`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Deliver
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.orcaman.concurrent_map.Specs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [github_com.orcaman.concurrent_map.Assumptions] [sync.Assumptions]

theorem swift.cmapHasV_of
    (wp_HasV : github_com.orcaman.concurrent_map.ConcurrentMap.HasV.spec (GF := netDistGF))
    (dm : GoSlice) (γdl : GName) : swift.cmapHasV.spec dm γdl := by
  intro key E Q
  iintro %Φ ⟨#Hpkg, Hrd, Hau⟩ HΦ
  iapply (wp_HasV dm γdl swift.deliveredR key) $$ %Φ [$Hpkg $Hrd]
  inext
  imod Hau with ⟨%M, HV, Hcl⟩
  imod (fupd_mask_subseteq (E1 := E) (E2 := ∅) (by simp)) with Hback
  imodintro
  iexists M
  iframe HV
  iintro HV
  imod Hback with -
  imod Hcl $$ HV with HQ
  imodintro
  iintro %ok ⟨Hrd, %Hok, -⟩
  iapply HΦ
  iframe Hrd
  rw [Hok]
  iexact HQ

theorem swift.cmapSetV_of
    (wp_SetV : github_com.orcaman.concurrent_map.ConcurrentMap.SetV.spec (GF := netDistGF))
    (dm : GoSlice) (γdl : GName) : swift.cmapSetV.spec dm γdl := by
  intro key v E Q
  iintro %Φ ⟨#Hpkg, #Hm, Hau⟩ HΦ
  iapply (wp_SetV dm γdl swift.deliveredR key v) $$ %Φ [$Hpkg $Hm]
  · iintro !>; itrivial
  inext
  imod Hau with ⟨%M, HV, Hcl⟩
  imod (fupd_mask_subseteq (E1 := E) (E2 := ∅) (by simp)) with Hback
  imodintro
  iexists M
  iframe HV
  iintro HV
  imod Hback with -
  imod Hcl $$ HV with HQ
  imodintro
  iintro _
  iapply HΦ
  iexact HQ

end proof

end Perennial.github_com.imdea_software.swiftpaxos
