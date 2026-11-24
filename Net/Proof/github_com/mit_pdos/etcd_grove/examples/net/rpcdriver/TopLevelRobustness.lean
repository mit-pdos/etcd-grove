/- Lean-first (no Rocq counterpart).

# `net/rpcdriver`: the top-level robustness result, proved

`rpcdriver_robust`, stated in
`Net/Spec/github_com/mit_pdos/etcd_grove/examples/net/rpcdriver/TopLevelRobustness.lean`, through the
all-stable bridge with the main thread's token (`robust_of_distBootI`,
`Net/Statement/DistBridgeExts.lean`, at `netExts`). The start: the net protocol library's registry
(`netProto_alloc`), the rpc world's connection registry and the request ids' ghost map (`γid`), and
the server's two listeners' protocols (`rpcLisP_set`, from the addresses unset: an exact listener's
`lisUnset` is its address's, `addrUnset_lisUnset`). Each machine's boot: its command's first
initialization (`CmdBootLinked.lean`), then its `main` (`cmd/*/Main.lean`) over the linked specs.
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.TopLevelRobustness
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.Link
public import Net.Statement.DistBridge

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Robustness

namespace github_com.mit_pdos.etcd_grove.examples.net.rpcdriver

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet
  GooseGlobalGS.gooseInvGS

section start
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netGF]

/-- At a valid address, the address unset is the listener at it unset (an exact listener; the
dsverify kits'). -/
theorem addrUnset_lisUnset (a : GoString) (h : addrOk a = true) :
    addrUnset (GF := netGF) a ⊢ lisUnset a := by
  have hl : PartialMap.get? (addrSpace ()) a = some () := by
    rw [gmap_get?_eq]; exact addrSpace_lookup_ok () h
  unfold addrUnset lisUnset
  have key : ∀ {k : GoString} {v : Unit}, PartialMap.get? (Std.delete (addrSpace ()) a) k = some v →
      (iprop(□ True) : IProp netGF) ⊢
        iprop(⌜lisAccepts a k⌝ → netPend (NG (Gg := G)) k ∅ ∗ netLisTok (NG (Gg := G)) k) := by
    intro k v hk
    iintro - %hacc
    have hk' : a = k := (lisAccepts_addrOk h).mp hacc
    subst hk'
    rw [gmap_get?_eq] at hk
    have : (GMap.delete a (addrSpace ())) !! a = none := GMap.lookup_delete _ _
    rw [show Std.delete (addrSpace ()) a = GMap.delete a (addrSpace ()) from rfl, this] at hk
    cases hk
  refine Entails.trans ?_ (BigSepM.bigSepM_delete hl).2
  iintro ⟨Hp, -, Ht⟩
  isplitl [Hp Ht]
  · iintro %_; iframe Hp Ht
  · iapply (BigSepM.bigSepM_intro key)
    imodintro; itrivial

end start

theorem rpcdriver_robust : rpcdriver_robust.spec := by
  intro _ lctx sem srv_sem cli_sem field_sem _ σs σc g threads
  refine robust_of_distBootI (GF := netGF) rpcAddrs (system σs σc) g threads rpcStepBound
    (fun hg hl => ⟨extsInitgP_of_init ⟨net_init_compat, trivial⟩ hg,
      fun m hm => extsInitP_of_init ⟨net_init_compat, trivial⟩ (hl m hm)⟩) ?_
  intro G hrb
  iintro Hs
  unfold rpcAddrs
  icases BigSepL.bigSepL_cons.1 $$ Hs with ⟨Ht, Hs⟩
  icases BigSepL.bigSepL_cons.1 $$ Hs with ⟨Hh, -⟩
  ihave Hlt := addrUnset_lisUnset tcpAddr (by decide) $$ Ht
  ihave Hlh := addrUnset_lisUnset httpAddr (by decide) $$ Hh
  imod netProto_alloc ⊤ with ⟨%π, #Hreg⟩
  imod ghost_map_alloc_empty (GF := netGF) (K := w64) (V := Unit) with ⟨%γid, Hids⟩
  imod ghost_map_alloc_empty (GF := netGF) (K := Nat) (V := net.rpc.RpcConnNames) with ⟨%γw, Hw⟩
  imod inv_alloc net.rpc.regN' ⊤ (net.rpc.regInv (π := π) (drvWorld γid γw)) $$ [Hw] with #HregW
  · inext
    unfold net.rpc.regInv
    iexists ∅
    iframe Hw
    iapply BigSepM.bigSepM_empty.2; iempintro
  imod net.rpc.rpcLisP_set (π := π) ⊤ (drvWorld γid γw) tcpAddr [] [] (by decide)
    (fun a ha => by
      have : a = tcpAddr := ((lisAccepts_addrOk (by decide)).1 ha.2).symm
      subst this; exact ⟨(drvWorld_tcp γid γw).2.1, (drvWorld_tcp γid γw).2.2⟩)
    $$ Hreg HregW Hlt with #Htl
  imod net.rpc.rpcLisP_set (π := π) ⊤ (drvWorld γid γw) httpAddr
    (net.rpc.connectReq net.rpc.defaultRPCPath) net.rpc.connectAns (by decide)
    (fun a ha => by
      have : a = httpAddr := ((lisAccepts_addrOk (by decide)).1 ha.2).symm
      subst this; exact ⟨(drvWorld_http γid γw).2.1, (drvWorld_http γid γw).2.2⟩)
    $$ Hreg HregW Hlh with #Hhl
  imodintro
  let Pl : IProp netGF := iprop(net.rpc.rpcLisP (π := π) (drvWorld γid γw) tcpAddr [] [] ∗
    net.rpc.rpcLisP (π := π) (drvWorld γid γw) httpAddr
      (net.rpc.connectReq net.rpc.defaultRPCPath) net.rpc.connectAns)
  iexists fun i => if i = 0 then Pl else iprop(Pl ∗ ghostMapAuth (K := w64) (V := Unit) γid 1 ∅)
  isplitr
  · ipureintro
    intro i m hm hG hGG hctx hrb' hT
    obtain ⟨G', L⟩ := hG
    dsimp only at hGG hctx
    subst hGG hctx
    letI hG : HeapGS .hasLC netGF := ⟨G', L⟩
    have hTb : threadBound netGF ≤ 2 ^ 31 := by unfold rpcStepBound at hrb'; omega
    have hRb : receiptBound netGF ≤ 2 ^ 64 := by unfold rpcStepBound at hrb'; omega
    match i, hm with
    | 0, hm =>
      cases hm
      dsimp only
      iintro ⟨#Htl, #Hhl⟩ - Hgs Htok
      imodintro
      unfold boot_server boot
      wp_apply cmd.server.wp_boot $$ Hgs as ⟨Hown, #Hpkg, Hres⟩
      wp_auto
      wp_apply (cmd.server.wp_main wp_Register wp_Server γid γw) $$ [Hres]
      · iframe Hpkg Hres Htl Hhl
        ipureintro; exact hTb
      wp_auto
      itrivial
    | 1, hm =>
      cases hm
      dsimp only
      iintro ⟨⟨#Htl, #Hhl⟩, Hids⟩ - Hgs Htok
      imodintro
      unfold boot_client boot
      wp_apply cmd.client.wp_boot $$ Hgs as ⟨Hown, #Hpkg, Hres⟩
      wp_auto
      ihave #Htcp := net.rpc.rpcLisP_addrOk _ _ _ _ (by decide) $$ Htl
      ihave #Hha := net.rpc.rpcLisP_addrOk _ _ _ _ (by decide) $$ Hhl
      wp_apply (cmd.client.wp_main wp_Register wp_Client γid γw) $$ [Hres Htok Hids] as -
      · iframe Hpkg Hres Htok Htcp Hha Hids
        ipureintro; exact ⟨hTb, hRb⟩
      wp_auto
      itrivial
  · simp only [system]
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · iframe Htl Hhl
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hids]
    · iframe Htl Hhl Hids
    iapply BigSepL.bigSepL_nil.2
    iempintro

end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver
end Perennial

#print axioms Perennial.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.rpcdriver_robust
