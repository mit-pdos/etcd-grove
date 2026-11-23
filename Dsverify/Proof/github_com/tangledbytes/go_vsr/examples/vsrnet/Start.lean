/-
The vr kit's deployment start (notes/dsv-vr.md): from the protocol library's registry and the deployment's
addresses unset (what `robust_of_distProtoRB`'s start gets), the ghost layer (`ghost_alloc`), the
addresses' protocols (go-vsr's `VsrWire.protoOf γ` both ways, the configuration addresses'
`confProto γ`/`ackProto`, the client machines' remote's `reqP`/`repP` of the far side's store
`kvR γ.gn`), remote's slot map and the client addresses' call budgets, 24 each (`mapCtx_alloc`) and pending library (`pend_alloc` over the
abstract state `absOwn γ`), and each machine's share: the orchestrator's (`orchShare`), client
`c`'s (`clientShare`, with its request counter `nextReq γ (c + 1) 1`), server `id`'s (`srvShare`,
`ServerProof.lean`), the orchestrator's with the client addresses' call units, client `c`'s with
its address's budget. With `Mains.lean`, each machine's `main` runs from its share.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.Mains
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.TopLevelDefs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open VsrModel VsrGhost

namespace github_com.tangledbytes.go_vsr.examples.vsrnet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote

attribute [local instance] GooseGlobalGS.gooseInvGS

section start
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-- The orchestrator's share: `Orch.spec`'s precondition but its package's fact. -/
def orchShare [ρ : RemoteGS] (γ : Names) (γp : PendNames) : IProp GF :=
  iprop(sysInv γ ∗ sizeTok γ ∗ confProtos γ ∗
    ([∗list] a ∈ clientAddrs, remoteAddr (Gg := G) (kvR γ.gn) a) ∗
    mapCtx (Gg := G) (I := KIn) ∗ pendCtx (Gg := G) (kvR γ.gn) (kvS0 (GF := GF)) γp ∗
    pendLib (Gg := G) (kvS0 (GF := GF)) γp (kvS0 (GF := GF)).M.init ∗
    [∗list] a ∈ clientAddrs, budUnits (Gg := G) a 24)

/-- Client machine `c`'s share: `Client.spec`'s precondition but its package's fact. -/
def clientShare [ρ : RemoteGS] (γ : Names) (c : Nat) : IProp GF :=
  iprop(confProtos γ ∗ VsrWire.protos γ ∗ sysInv γ ∗ regInv γ ∗ nextReq γ (c + 1) 1 ∗
    remoteAddr (Gg := G) (kvR γ.gn) (clientAddrs.getD c []) ∗
    ⌜ρ.bud (clientAddrs.getD c []) = some 24⌝)

theorem clientAddrs_getD (c : Nat) (hc : c < 6) :
    clientAddrs[c]? = some (clientAddrs.getD c []) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa [clientAddrs] using hc)]
  rfl

/-- **The start**: the ghost layer, the addresses' protocols, remote's slot map and pending
library, and every machine's share. -/
theorem vr_start :
    ⊢ regCtx (Gg := G) -∗ ([∗list] a ∈ vrKitAddrs, addrUnset (Gg := G) a) ={⊤}=∗
      ∃ (ρ : RemoteGS) (γ : Names) (γp : PendNames), orchShare γ γp ∗
        ([∗list] c ∈ List.range 6, clientShare γ c) ∗
        ([∗list] s ∈ List.range 5, srvShare γ (s + 1)) := by
  iintro #Hreg Hs
  unfold vrKitAddrs
  icases BigSepL.bigSepL_append.1 $$ Hs with ⟨Hs, Hsc⟩
  icases BigSepL.bigSepL_append.1 $$ Hs with ⟨Hsv, Hscf⟩
  imod mapCtx_alloc (Gg := G) (I := KIn) ⊤ clientAddrs 24 (by decide) with ⟨%ρ, %Hρ, #Hmap, Hunits⟩
  imod ghost_alloc (GF := GF) with ⟨%γ, #Hsys, #HregI, Habs, Hsize, Hreps, Hnexts⟩
  imod addrs_set_proto (Gg := G) ⊤ (fun _ => VsrWire.protoOf γ) (fun _ => VsrWire.protoOf γ)
    VsrWire.addrs $$ Hreg Hsv with #Hpv
  imod addrs_set_proto (Gg := G) ⊤ (fun _ => confProto γ) (fun _ => ackProto) cfgAddrs
    $$ Hreg Hscf with #Hpcf
  imod addrs_set_proto (Gg := G) ⊤ (fun a => reqP (Gg := G) (RBase.svc (kvR γ.gn)) a)
    (fun _ => repP (Gg := G) (RBase.svc (kvR γ.gn))) clientAddrs $$ Hreg Hsc with #Hpc
  have hv : absOwn (G := G) γ (fun _ => none) ⊢
      (kvR (Gg := G) γ.gn).sysState (kvR (Gg := G) γ.gn).B.init := .rfl
  ihave Habs := hv $$ Habs
  imod pend_alloc (Gg := G) (kvR γ.gn) ⊤ (kvS0 (GF := GF)) rfl $$ Habs with ⟨%γp, #Hpend, Hlib⟩
  ihave #Hvp : VsrWire.protos (G := G) γ $$ [Hpv]
  · unfold VsrWire.protos; iexact Hpv
  ihave #Hcp : confProtos (G := G) γ $$ [Hpcf]
  · unfold confProtos; iexact Hpcf
  ihave #Hra : [∗list] a ∈ clientAddrs, remoteAddr (Gg := G) (kvR γ.gn) a $$ [Hpc]
  · unfold remoteAddr svcAddr; iexact Hpc
  imodintro
  iexists ρ, γ, γp
  isplitl [Hsize Hlib Hunits]
  · unfold orchShare
    iframe #
    iframe
  isplitl [Hnexts]
  · iapply (BigSepL.bigSepL_impl (Φ := fun _ c => nextReq (G := G) γ (c + 1) 1)) $$ Hnexts
    imodintro
    iintro %k %c %hk Hn
    have hc : c < 6 := by
      have := List.mem_of_getElem? hk
      simpa using this
    unfold clientShare
    iframe #
    iframe Hn
    isplitl []
    · iapply BigSepL.bigSepL_lookup (clientAddrs_getD c hc) $$ Hra
    ipureintro
    rw [Hρ, if_pos (List.mem_of_getElem? (clientAddrs_getD c hc))]
  · iapply (BigSepL.bigSepL_impl (Φ := fun _ r => repOwn (G := G) γ r VsrModel.initRep)) $$ Hreps
    imodintro
    iintro %k %s %hk Hr
    unfold srvShare
    rw [Nat.add_sub_cancel]
    iframe #
    iframe Hr

end start

end github_com.tangledbytes.go_vsr.examples.vsrnet
end Perennial
