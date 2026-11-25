/- Lean-first (no Rocq counterpart).

# `lib/grpcdriver`: the top-level robustness result, proved

`grpcdriver_robust`, stated in
`Spec/github_com/mit_pdos/etcd_grove/examples/lib/grpcdriver/TopLevelRobustness.lean`, through the
all-stable bridge with the main thread's token and `Robust`'s thread bound (`robust_of_distBootIT`,
`Net/Statement/DistBridgeExts.lean`, at `netExts`). The start: the net protocol library's registry
(`netProto_alloc`), the slot map (`depSlots_alloc`), the ids' ghost map (`γid`), the server address's
listening token in its invariant and the address set to serve the driver's table (`addr_set_proto_tok`,
`grpcAddrAt`, at the table over the global ghost state, `drvSvcG`, which is each machine's `drvSvc`:
`drvSvc_eq_G`). Each machine's boot: its command's initialization (the generated `wp_initialize'`, from
the empty package state, `ownInitializing_of_empty`), then its `main` (`cmd/*/Main.lean`) over the
linked specs (`Link.lean`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.TopLevelRobustness
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.SvcG
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.cmd.server.Init
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.cmd.client.Init
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.cmd.server.PkgTable
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.cmd.client.PkgTable
public import Proof.runtime.InitEmpty
public import Net.Statement.DistBridgeExts

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Robustness EtcdGrove

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet
  GooseGlobalGS.gooseInvGS

theorem grpcdriver_robust : grpcdriver_robust.spec := by
  intro _ lctx sem srv_sem cli_sem field_sem _ σs σc g
  refine robust_of_distBootIT (GF := netGF) grpcAddrs (system σs σc) g grpcThreads grpcSteps
    (fun hg hl => ⟨extsInitgP_of_init ⟨net_init_compat, trivial⟩ hg,
      fun m hm => extsInitP_of_init ⟨net_init_compat, trivial⟩ (hl m hm)⟩) ?_
  intro G hrb
  iintro Hs
  rw [show grpcAddrs = [drvAddr] from rfl]
  icases BigSepL.bigSepL_cons.1 $$ Hs with ⟨Ha, -⟩
  imod netProto_alloc ⊤ with ⟨%π, #Hreg⟩
  imod depSlots_alloc (π := π) ⊤ with ⟨%σ, #Hsl⟩
  imod ghost_map_alloc_empty (GF := netGF) (K := w64) (V := Unit) with ⟨%γid, Hids⟩
  iunfold addrUnset at Ha
  icases Ha with ⟨Hp, #Ht, Htk⟩
  imod inv_alloc (lisTokN drvAddr) ⊤ (netLisTok (NG (Gg := G)) drvAddr) $$ [Htk] with #Htok
  · inext; iexact Htk
  imod addr_set_proto_tok ⊤ drvAddr (grpcCliPI (drvSvcG (Gg := G) γid))
      (grpcSrvPI (drvSvcG (Gg := G) γid)) $$ Hreg Hp Ht [] with #Hpr
  · unfold lisTokInv; ileft; iexact Htok
  ihave #Haddr : grpcAddrAt (Gg := G) (π := π) (σ := σ) drvAddr (drvSvcG (Gg := G) γid) $$ []
  · unfold grpcAddrAt; iframe #
  imodintro
  let Pl : IProp netGF := iprop(inv (lisTokN drvAddr) (netLisTok (NG (Gg := G)) drvAddr) ∗
    grpcAddrAt (Gg := G) (π := π) (σ := σ) drvAddr (drvSvcG (Gg := G) γid))
  iexists fun i => if i = 0 then Pl else iprop(Pl ∗ ghostMapAuth (K := w64) (V := Unit) γid 1 ∅)
  isplitr
  · ipureintro
    intro i m hm hG hGG hctx hrb' hT
    obtain ⟨G', L⟩ := hG
    dsimp only at hGG hctx
    subst hGG hctx
    letI hG : HeapGS .hasLC netGF := ⟨G', L⟩
    have hTb : threadBound netGF ≤ 2 ^ 31 := by unfold grpcThreads at hT; omega
    match i, hm with
    | 0, hm =>
      cases hm
      dsimp only
      rw [if_pos rfl]
      iintro ⟨#Htok, #Haddr⟩ - Hgs -
      imodintro
      unfold boot_server boot
      ihave Hown := ownInitializing_of_empty
        (cmd.server.getIsPkgInit (GF := netGF)) $$ Hgs
      wp_apply cmd.server.wp_initialize' _ cmd.server.getIsPkgInit_wf $$ Hown as ⟨-, #Hpkg⟩
      try wp_auto
      ihave #Haddr' : grpcAddrAt (Gg := hG.goose_globalGS) (π := π) (σ := σ) drvAddr
          (drvSvc (GF := netGF) γid) $$ []
      · rw [drvSvc_eq_G]; iexact Haddr
      wp_apply (cmd.server.wp_main grpcdriver.wp_Server π σ γid) $$ []
      · iframe #
      try wp_auto
      itrivial
    | 1, hm =>
      cases hm
      dsimp only
      rw [if_neg (by decide)]
      iintro ⟨⟨#Htok, #Haddr⟩, Hids⟩ - Hgs Hth
      imodintro
      unfold boot_client boot
      ihave Hown := ownInitializing_of_empty
        (cmd.client.getIsPkgInit (GF := netGF)) $$ Hgs
      wp_apply cmd.client.wp_initialize' _ cmd.client.getIsPkgInit_wf $$ Hown as ⟨-, #Hpkg⟩
      try wp_auto
      ihave #Haddr' : grpcAddrAt (Gg := hG.goose_globalGS) (π := π) (σ := σ) drvAddr
          (drvSvc (GF := netGF) γid) $$ []
      · rw [drvSvc_eq_G]; iexact Haddr
      wp_apply (cmd.client.wp_main grpcdriver.wp_Client π σ γid) $$ [Hth Hids] as -
      · iframe #
        iframe
        ipureintro; exact hTb
      try wp_auto
      itrivial
  · simp only [system]
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · rw [if_pos rfl]; simp only [Pl]; iframe Htok Haddr
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hids]
    · rw [if_neg (by decide)]; simp only [Pl]; iframe Htok Haddr Hids
    iapply BigSepL.bigSepL_nil.2
    iempintro

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial

#print axioms Perennial.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.grpcdriver_robust
