/-
The QuePaxa kit's top-level result (`Spec/raxos/examples/quepaxanet/TopLevelRobustness.lean`),
proved (as paxos's): from the deployment's start (the protocol library's registry, the listed
addresses and the servers' wildcard listeners unset: `robust_of_distProtoLisRB`,
dsv-epaxos's `epaxosnet/Bridge.lean`, shared), the kit's start (`kit_start`, `Start.lean`:
QuePaxa's ghost state, the gRPC
world's registry from `GrpcWorldHyp`, every address's protocols, remote's map of operations and
pending library, and the machines' shares), and each machine's boot program from its share, with the
statement's per-heap hypotheses made instances on that machine's heap.
-/
module

public import Dsverify.Spec.raxos.examples.quepaxanet.TopLevelRobustness
public import Dsverify.Proof.raxos.examples.quepaxanet.Linked
public import Dsverify.Proof.raxos.examples.quepaxanet.Mains
public import Dsverify.Proof.raxos.examples.quepaxanet.Start
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.Bridge
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.orch.PkgTable
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.client0.PkgTable
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.client1.PkgTable
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.client2.PkgTable
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.client3.PkgTable
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.client4.PkgTable
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.client5.PkgTable
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.server1.PkgTable
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.server2.PkgTable
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.server3.PkgTable
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.server4.PkgTable
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.server5.PkgTable
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.orch.Init
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.client0.Init
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.client1.Init
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.client2.Init
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.client3.Init
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.client4.Init
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.client5.Init
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.server1.Init
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.server2.Init
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.server3.Init
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.server4.Init
public import Dsverify.Proof.raxos.examples.quepaxanet.cmd.server5.Init

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Robustness

namespace raxos.examples.quepaxanet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote raxos raxos.pure
open github_com.mit_pdos.etcd_grove.examples.lib.remote.counter (remoteGF)

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet
  GooseGlobalGS.gooseInvGS

section boot
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- A command's boot program, from its initializer's spec (with the program's package table
`getIs`) and a spec of its `main` with precondition `P` (paxos's `wp_boot`). -/
theorem wp_boot [hG : HeapGS .hasLC GF] [sem : go.Semantics]
    (init : val) (main pkg : GoString) [IsPkgInit (IProp GF) pkg] (getIs : GoString → IProp GF)
    (Hinit : {{ ownInitializing getIs }}
        (App (Val init) (Val #()))
      {{ RET #(); ownInitializing getIs ∗ isPkgInit (PROP := IProp GF) pkg }})
    (P : IProp GF)
    (Hf : {{ isPkgInit (PROP := IProp GF) pkg ∗ P }}
        (App (Val (@! main)) (Val #()))
      {{ RET #(); True }}) :
    ⊢ P -∗ ownGoState ∅ -∗ WP (boot init main) @ Stuckness.NotStuck; ⊤ {{ v, ⌜v = #()⌝ }} := by
  iintro HP Hgs
  unfold boot
  wp_apply Hinit $$ [Hgs] as ⟨-, #Hpkg⟩
  · rw [ownInitializing_unseal]
    unfold ownInitializingDef
    iexists ∅
    iframe Hgs
    iintro !>
    iapply BigSepM.bigSepM_empty.2
    iempintro
  wp_pures
  wp_apply Hf $$ [HP]
  · iframe
  ipureintro; rfl

end boot

/-- **The QuePaxa kit, closed** (see the statement's file). -/
theorem quepaxa_remote_robust : quepaxa_remote_robust.spec := by
  intro gctx lctx sem s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 bvi
    hyi hri hii hgi hgri hgci hmi qv hpb hrand hutc hsort hpr hgrpc hworld hmap σ g threads
  refine github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.robust_of_distProtoLisRB
    (GF := remoteGF) quepaxaKitAddrs kitLis (system σ) g threads
    (2 ^ 63) kitLis_pairwise kitLis_disj ?_
  intro G π hrb
  haveI : hyp.grpc.GrpcWorldHyp (Gg := G) qv.grpc := hworld G
  iintro #Hreg Hs Hl
  unfold quepaxaKitAddrs
  imod kit_start (Gg := G) $$ Hreg Hs Hl with ⟨%γ, %ρ, %γp, Ho, #Has, #Hmap, #Hpend, Hlib, Hbud, Hcs, Hss⟩
  rw [show List.range 6 = [0, 1, 2, 3, 4, 5] from rfl]
  icases BigSepL.bigSepL_cons.1 $$ Hcs with ⟨Hc0, Hcs⟩
  icases BigSepL.bigSepL_cons.1 $$ Hcs with ⟨Hc1, Hcs⟩
  icases BigSepL.bigSepL_cons.1 $$ Hcs with ⟨Hc2, Hcs⟩
  icases BigSepL.bigSepL_cons.1 $$ Hcs with ⟨Hc3, Hcs⟩
  icases BigSepL.bigSepL_cons.1 $$ Hcs with ⟨Hc4, Hcs⟩
  icases BigSepL.bigSepL_cons.1 $$ Hcs with ⟨Hc5, Hcs⟩
  icases BigSepL.bigSepL_cons.1 $$ Hss with ⟨Hs1, Hss⟩
  icases BigSepL.bigSepL_cons.1 $$ Hss with ⟨Hs2, Hss⟩
  icases BigSepL.bigSepL_cons.1 $$ Hss with ⟨Hs3, Hss⟩
  icases BigSepL.bigSepL_cons.1 $$ Hss with ⟨Hs4, Hss⟩
  icases BigSepL.bigSepL_cons.1 $$ Hss with ⟨Hs5, Hss⟩
  ihave #Hra0 : remoteAddr (Gg := G) (ρ := ρ) (qR γ) (clientAddrs.getD 0 []) $$ []
  · iapply BigSepL.bigSepL_lookup (i := 0) rfl $$ Has
  ihave #Hra1 : remoteAddr (Gg := G) (ρ := ρ) (qR γ) (clientAddrs.getD 1 []) $$ []
  · iapply BigSepL.bigSepL_lookup (i := 1) rfl $$ Has
  ihave #Hra2 : remoteAddr (Gg := G) (ρ := ρ) (qR γ) (clientAddrs.getD 2 []) $$ []
  · iapply BigSepL.bigSepL_lookup (i := 2) rfl $$ Has
  ihave #Hra3 : remoteAddr (Gg := G) (ρ := ρ) (qR γ) (clientAddrs.getD 3 []) $$ []
  · iapply BigSepL.bigSepL_lookup (i := 3) rfl $$ Has
  ihave #Hra4 : remoteAddr (Gg := G) (ρ := ρ) (qR γ) (clientAddrs.getD 4 []) $$ []
  · iapply BigSepL.bigSepL_lookup (i := 4) rfl $$ Has
  ihave #Hra5 : remoteAddr (Gg := G) (ρ := ρ) (qR γ) (clientAddrs.getD 5 []) $$ []
  · iapply BigSepL.bigSepL_lookup (i := 5) rfl $$ Has
  imodintro
  iexists fun i => if i = 0 then iprop(orchRes (Gg := G) γ ∗ ([∗list] a ∈ clientAddrs, remoteAddr (Gg := G) (ρ := ρ) (qR γ) a) ∗ mapCtx (Gg := G) (ρ := ρ) (I := QIn) ∗ pendCtx (Gg := G) (qR γ) (qS0 (GF := remoteGF)) γp ∗ pendLib (Gg := G) (qS0 (GF := remoteGF)) γp (qS0 (GF := remoteGF)).M.init ∗ [∗list] a ∈ clientAddrs, budUnits (Gg := G) (ρ := ρ) a 60)
      else if i = 1 then iprop(clientRes (Gg := G) γ 0 ∗ remoteAddr (Gg := G) (ρ := ρ) (qR γ) (clientAddrs.getD 0 []) ∗ mapCtx (Gg := G) (ρ := ρ) (I := QIn))
      else if i = 2 then iprop(clientRes (Gg := G) γ 1 ∗ remoteAddr (Gg := G) (ρ := ρ) (qR γ) (clientAddrs.getD 1 []) ∗ mapCtx (Gg := G) (ρ := ρ) (I := QIn))
      else if i = 3 then iprop(clientRes (Gg := G) γ 2 ∗ remoteAddr (Gg := G) (ρ := ρ) (qR γ) (clientAddrs.getD 2 []) ∗ mapCtx (Gg := G) (ρ := ρ) (I := QIn))
      else if i = 4 then iprop(clientRes (Gg := G) γ 3 ∗ remoteAddr (Gg := G) (ρ := ρ) (qR γ) (clientAddrs.getD 3 []) ∗ mapCtx (Gg := G) (ρ := ρ) (I := QIn))
      else if i = 5 then iprop(clientRes (Gg := G) γ 4 ∗ remoteAddr (Gg := G) (ρ := ρ) (qR γ) (clientAddrs.getD 4 []) ∗ mapCtx (Gg := G) (ρ := ρ) (I := QIn))
      else if i = 6 then iprop(clientRes (Gg := G) γ 5 ∗ remoteAddr (Gg := G) (ρ := ρ) (qR γ) (clientAddrs.getD 5 []) ∗ mapCtx (Gg := G) (ρ := ρ) (I := QIn))
      else if i = 7 then iprop(serverRes (Gg := G) γ 1)
      else if i = 8 then iprop(serverRes (Gg := G) γ 2)
      else if i = 9 then iprop(serverRes (Gg := G) γ 3)
      else if i = 10 then iprop(serverRes (Gg := G) γ 4)
      else if i = 11 then iprop(serverRes (Gg := G) γ 5)
      else iprop(True)
  isplitr
  · ipureintro
    intro i m hm hG hGG hctx
    obtain ⟨G', ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩ := hG
    dsimp only at hGG hctx
    subst hGG hctx
    letI hG : HeapGS .hasLC remoteGF := ⟨G', ⟨Lexts, Llctx, Lheap, Lgs, Lthr, Lcr⟩⟩
    haveI : gopkg_in.yaml_v2.InitHyp remoteGF := hyi G' hG.goose_localGS
    haveI : github_com.go_redis.redis.v8.InitHyp remoteGF := hri G' hG.goose_localGS
    haveI : io.ioutil.InitHyp remoteGF := hii G' hG.goose_localGS
    haveI : encoding.gob.InitHyp remoteGF := hgi G' hG.goose_localGS
    haveI : google_golang_org.grpc.InitHyp remoteGF := hgri G' hG.goose_localGS
    haveI : google_golang_org.grpc.codes.InitHyp remoteGF := hgci G' hG.goose_localGS
    haveI : math.rand.InitHyp remoteGF := hmi G' hG.goose_localGS
    haveI : hyp.PbHyp remoteGF := hpb G' hG.goose_localGS
    haveI : hyp.RandHyp remoteGF := hrand G' hG.goose_localGS
    haveI : hyp.UtcHyp remoteGF := hutc G' hG.goose_localGS
    haveI : hyp.SortHyp remoteGF := hsort G' hG.goose_localGS
    haveI : hyp.PrintlnHyp remoteGF := hpr G' hG.goose_localGS
    haveI : hyp.grpc.GrpcHyp (cd := hyp.qpCodec) qv.grpc := hgrpc G' hG.goose_localGS π
    haveI : hyp.sync.MapHyp qv.map := hmap G' hG.goose_localGS
    match i, hm with
    | 0, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro ⟨Ho0, #Has0, #Hmap0, #Hpend0, Hlib0, Hbud0⟩ Hgs
      iapply wp_boot cmd.orch.initialize' cmd.orch.main _ cmd.orch.getIsPkgInit
          (cmd.orch.wp_initialize' _ cmd.orch.getIsPkgInit_wf) _
          (cmd.orch.wp_main wp_Orch γ γp hrb) $$ [Ho0 Hlib0 Hbud0] Hgs
      iframe #
      iframe Ho0 Hlib0 Hbud0
    | 1, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro ⟨Hc0, #Hra0, #Hmap0⟩ Hgs
      iapply wp_boot cmd.client0.initialize' cmd.client0.main _ cmd.client0.getIsPkgInit
          (cmd.client0.wp_initialize' _ cmd.client0.getIsPkgInit_wf) _
          (cmd.client0.wp_main wp_Client γ) $$ [Hc0] Hgs
      iframe #
      iframe Hc0
    | 2, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro ⟨Hc0, #Hra0, #Hmap0⟩ Hgs
      iapply wp_boot cmd.client1.initialize' cmd.client1.main _ cmd.client1.getIsPkgInit
          (cmd.client1.wp_initialize' _ cmd.client1.getIsPkgInit_wf) _
          (cmd.client1.wp_main wp_Client γ) $$ [Hc0] Hgs
      iframe #
      iframe Hc0
    | 3, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro ⟨Hc0, #Hra0, #Hmap0⟩ Hgs
      iapply wp_boot cmd.client2.initialize' cmd.client2.main _ cmd.client2.getIsPkgInit
          (cmd.client2.wp_initialize' _ cmd.client2.getIsPkgInit_wf) _
          (cmd.client2.wp_main wp_Client γ) $$ [Hc0] Hgs
      iframe #
      iframe Hc0
    | 4, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro ⟨Hc0, #Hra0, #Hmap0⟩ Hgs
      iapply wp_boot cmd.client3.initialize' cmd.client3.main _ cmd.client3.getIsPkgInit
          (cmd.client3.wp_initialize' _ cmd.client3.getIsPkgInit_wf) _
          (cmd.client3.wp_main wp_Client γ) $$ [Hc0] Hgs
      iframe #
      iframe Hc0
    | 5, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro ⟨Hc0, #Hra0, #Hmap0⟩ Hgs
      iapply wp_boot cmd.client4.initialize' cmd.client4.main _ cmd.client4.getIsPkgInit
          (cmd.client4.wp_initialize' _ cmd.client4.getIsPkgInit_wf) _
          (cmd.client4.wp_main wp_Client γ) $$ [Hc0] Hgs
      iframe #
      iframe Hc0
    | 6, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro ⟨Hc0, #Hra0, #Hmap0⟩ Hgs
      iapply wp_boot cmd.client5.initialize' cmd.client5.main _ cmd.client5.getIsPkgInit
          (cmd.client5.wp_initialize' _ cmd.client5.getIsPkgInit_wf) _
          (cmd.client5.wp_main wp_Client γ) $$ [Hc0] Hgs
      iframe #
      iframe Hc0
    | 7, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro Hs0 Hgs
      iapply wp_boot cmd.server1.initialize' cmd.server1.main _ cmd.server1.getIsPkgInit
          (cmd.server1.wp_initialize' _ cmd.server1.getIsPkgInit_wf) _
          (cmd.server1.wp_main wp_Server γ) $$ [Hs0] Hgs
      iframe #
      iframe Hs0
    | 8, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro Hs0 Hgs
      iapply wp_boot cmd.server2.initialize' cmd.server2.main _ cmd.server2.getIsPkgInit
          (cmd.server2.wp_initialize' _ cmd.server2.getIsPkgInit_wf) _
          (cmd.server2.wp_main wp_Server γ) $$ [Hs0] Hgs
      iframe #
      iframe Hs0
    | 9, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro Hs0 Hgs
      iapply wp_boot cmd.server3.initialize' cmd.server3.main _ cmd.server3.getIsPkgInit
          (cmd.server3.wp_initialize' _ cmd.server3.getIsPkgInit_wf) _
          (cmd.server3.wp_main wp_Server γ) $$ [Hs0] Hgs
      iframe #
      iframe Hs0
    | 10, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro Hs0 Hgs
      iapply wp_boot cmd.server4.initialize' cmd.server4.main _ cmd.server4.getIsPkgInit
          (cmd.server4.wp_initialize' _ cmd.server4.getIsPkgInit_wf) _
          (cmd.server4.wp_main wp_Server γ) $$ [Hs0] Hgs
      iframe #
      iframe Hs0
    | 11, hm =>
      cases hm
      dsimp only
      simp only [Nat.reduceEqDiff, ↓reduceIte]
      iintro Hs0 Hgs
      iapply wp_boot cmd.server5.initialize' cmd.server5.main _ cmd.server5.getIsPkgInit
          (cmd.server5.wp_initialize' _ cmd.server5.getIsPkgInit_wf) _
          (cmd.server5.wp_main wp_Server γ) $$ [Hs0] Hgs
      iframe #
      iframe Hs0
  · simp only [system]
    iapply BigSepL.bigSepL_cons.2
    isplitl [Ho Hlib Hbud]
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iframe #
      iframe Ho Hlib Hbud
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hc0]
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iframe #
      iframe Hc0
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hc1]
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iframe #
      iframe Hc1
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hc2]
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iframe #
      iframe Hc2
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hc3]
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iframe #
      iframe Hc3
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hc4]
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iframe #
      iframe Hc4
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hc5]
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iframe #
      iframe Hc5
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hs1]
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iframe #
      iframe Hs1
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hs2]
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iframe #
      iframe Hs2
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hs3]
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iframe #
      iframe Hs3
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hs4]
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iframe #
      iframe Hs4
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hs5]
    · simp only [Nat.zero_add, Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte]
      iframe #
      iframe Hs5
    iapply BigSepL.bigSepL_nil.2
    iempintro

end raxos.examples.quepaxanet
end Perennial
