/-
**The kit's start** (the lab's `Kit/Start.lean`, re-based; notes/dsv-quepaxa.md, step 5b): from
the deployment's start resources as `robust_of_distProtoLisRB` gives them (dsv-epaxos's
`epaxosnet/Bridge.lean`: the protocol library's registry, the listed addresses `kitAddrs` unset,
the wildcards `kitLis` unset), allocate QuePaxa's ghost names (`StartGhost.lean`), the gRPC world's registry, the two
invariants, the slot map and the pending library of remote, and set every address's protocols
(`netProtos`, remote's on `clientAddrs`); give the orchestrator, each client machine and each
server machine its share: exactly the preconditions of `Orch.spec`, `Client.spec` and
`Server.spec` (`Kit.lean`) but the package's initialization (`kit_start`).

The gRPC world's registry comes from the hypothesis `GrpcWorldHyp` (over the global ghost state:
the start has no machine's heap).
-/
module

public import Dsverify.Proof.raxos.examples.quepaxanet.StartGhost
public import Dsverify.Proof.raxos.examples.quepaxanet.StartAddr

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.iris.style.nameCheck false

namespace Perennial

namespace raxos.examples.quepaxanet

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net BigSepM BigSepL
open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote
open raxos raxos.pure

theorem kitLis_ok : ∀ la ∈ kitLis, listenOk la = true := by
  rw [kitLis_lit]; decide

theorem proxyLis_ok (k : Nat) (hk : k ∈ ([1, 2, 3, 4, 5] : List Nat)) :
    listenOk (proxyLis k) = true :=
  kitLis_ok _ (List.mem_append_left _ (List.mem_map_of_mem hk))

theorem recLis_ok (r : Nat) (hr : r ∈ ([1, 2, 3, 4, 5] : List Nat)) :
    listenOk (recLis r) = true :=
  kitLis_ok _ (List.mem_append_right _ (List.mem_map_of_mem hr))

section start
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF]
variable [π : NetProtoGS] [qv : hyp.QpVocab GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- Set the protocols of the addresses `f c` (`c ∈ l`), `P c` and `Q c`. -/
theorem addrs_set_proto_map (E : CoPset) (f : Nat → GoString) (P Q : Nat → Proto GF) :
    ∀ l : List Nat,
    ⊢ regCtx (Gg := Gg) -∗ ([∗list] c ∈ l, addrUnset (Gg := Gg) (f c)) ={E}=∗
      [∗list] c ∈ l, addrProto (Gg := Gg) (f c) (P c) (Q c)
  | [] => by
    iintro - -
    imodintro
    iapply bigSepL_nil.2; iempintro
  | c :: l => by
    iintro #Hreg Hs
    icases bigSepL_cons.1 $$ Hs with ⟨Hu, Hs⟩
    imod addr_set_proto E (f c) (P c) (Q c) $$ Hreg Hu with #Hp
    imod addrs_set_proto_map E f P Q l $$ Hreg Hs with Hps
    imodintro
    iapply bigSepL_cons.2
    iframe Hp Hps

/-- Set the protocols of the listeners `f k` (`k ∈ l`), `P k` and `Q k`. -/
theorem lis_set_proto_map (E : CoPset) (f : Nat → GoString) (P Q : Nat → Proto GF) :
    ∀ l : List Nat, (∀ k ∈ l, listenOk (f k) = true) →
    ⊢ regCtx (Gg := Gg) -∗ ([∗list] k ∈ l, lisUnset (Gg := Gg) (f k)) ={E}=∗
      [∗list] k ∈ l, lisProto (Gg := Gg) (f k) (P k) (Q k)
  | [], _ => by
    iintro - -
    imodintro
    iapply bigSepL_nil.2; iempintro
  | k :: l, hok => by
    iintro #Hreg Hs
    icases bigSepL_cons.1 $$ Hs with ⟨Hu, Hs⟩
    imod lis_set_proto E (f k) (P k) (Q k) (hok k List.mem_cons_self) $$ Hreg Hu with #Hp
    imod lis_set_proto_map E f P Q l (fun k' h => hok k' (List.mem_cons_of_mem _ h)) $$ Hreg Hs
      with Hps
    imodintro
    iapply bigSepL_cons.2
    iframe Hp Hps

/-- The recorders' listeners, with the world's registry. -/
theorem recs_setup (E : CoPset) (W : hyp.grpc.GrpcWorld GF) : ∀ l : List Nat,
    (∀ r ∈ l, listenOk (recLis r) = true) →
    ⊢ regCtx (Gg := Gg) -∗ qv.grpc.worldOk W -∗ ([∗list] r ∈ l, lisUnset (Gg := Gg) (recLis r))
      ={E}=∗ [∗list] r ∈ l, recLisP qv.grpc W r
  | [], _ => by
    iintro - - -
    imodintro
    iapply bigSepL_nil.2; iempintro
  | r :: l, hok => by
    iintro #Hreg #Hw Hs
    icases bigSepL_cons.1 $$ Hs with ⟨Hu, Hs⟩
    imod lis_set_proto E (recLis r) (qv.grpc.reqProto W (recAddr r))
      (qv.grpc.respProto W (recAddr r)) (hok r List.mem_cons_self) $$ Hreg Hu with #Hp
    imod recs_setup E W l (fun k' h => hok k' (List.mem_cons_of_mem _ h)) $$ Hreg Hw Hs with Hps
    imodintro
    iapply bigSepL_cons.2
    iframe Hps
    unfold recLisP
    iframe Hp Hw

/-- Every protocol of `netProtos` from the listed addresses and the wildcards unset. -/
theorem net_setup (γ : QNames) :
    ⊢ regCtx (Gg := Gg) -∗ qv.grpc.worldOk (world γ) -∗
      addrUnset (Gg := Gg) orchAddr -∗ ([∗list] a ∈ unusedAddrs, addrUnset (Gg := Gg) a) -∗
      ([∗list] c ∈ List.range 6, addrUnset (Gg := Gg) (clientAddr c)) -∗
      ([∗list] c ∈ List.range 6, addrUnset (Gg := Gg) (cconfAddr c)) -∗
      ([∗list] k ∈ ([1, 2, 3, 4, 5] : List Nat), addrUnset (Gg := Gg) (confAddr k)) -∗
      ([∗list] k ∈ ([1, 2, 3, 4, 5] : List Nat), lisUnset (Gg := Gg) (proxyLis k)) -∗
      ([∗list] r ∈ ([1, 2, 3, 4, 5] : List Nat), lisUnset (Gg := Gg) (recLis r)) ={⊤}=∗
      netProtos γ := by
  iintro #Hreg #Hw Ho Hun Hcl Hcc Hcf Hpx Hrc
  imod addr_set_proto ⊤ orchAddr silentProto silentProto $$ Hreg Ho with #Hpo
  imod addrs_set_proto ⊤ (fun _ => silentProto) (fun _ => silentProto) unusedAddrs $$ Hreg Hun
    with #Hpu
  imod addrs_set_proto_map ⊤ clientAddr (clientInProto γ) (fun _ => silentProto) (List.range 6)
    $$ Hreg Hcl with #Hpc
  imod addrs_set_proto_map ⊤ cconfAddr (fun _ => confInProto γ) (fun _ => ackProto) (List.range 6)
    $$ Hreg Hcc with #Hpcc
  imod addrs_set_proto_map ⊤ confAddr (fun _ => confInProto γ) (fun _ => ackProto) [1, 2, 3, 4, 5]
    $$ Hreg Hcf with #Hpcf
  imod lis_set_proto_map ⊤ proxyLis (proxyInProto γ) (fun _ => silentProto) [1, 2, 3, 4, 5]
    proxyLis_ok $$ Hreg Hpx with #Hpp
  imod recs_setup ⊤ (world γ) [1, 2, 3, 4, 5] recLis_ok $$ Hreg Hw Hrc with #Hpr
  imodintro
  unfold netProtos
  iframe Hpo Hpu Hpc Hpcc Hpcf Hpp Hpr

instance spentLb_persistent (γ : QNames) (m : Int) : Persistent (spentLb (GF := GF) γ m) := by
  unfold spentLb; infer_instance

/-- The client machines' shares, from their parts. -/
theorem clients_dist (γ : QNames) : ∀ l : List Nat,
    ⊢ sharedRes γ -∗
      ([∗list] c ∈ l, ghostMapElem γ.cnt c (DFrac.own (1 : Qp).half) (0 : Nat)) -∗
      ([∗list] c ∈ l, [∗list] t ∈ ticketsOf c, ticketTok γ t) -∗
      [∗list] c ∈ l, clientRes γ c
  | [] => by
    iintro - - -
    iapply bigSepL_nil.2; iempintro
  | c :: l => by
    iintro #Hsh Hns Htks
    icases bigSepL_cons.1 $$ Hns with ⟨Hn, Hns⟩
    icases bigSepL_cons.1 $$ Htks with ⟨Htk, Htks⟩
    iapply bigSepL_cons.2
    isplitl [Hn Htk]
    · unfold clientRes; iframe Hn Htk Hsh
    iapply clients_dist γ l $$ Hsh Hns Htks

/-- The server machines' shares, from their parts. -/
theorem servers_dist (γ : QNames) : ∀ l : List Nat,
    ⊢ sharedRes γ -∗ ([∗list] k ∈ l, netTok γ k) -∗
      ([∗list] k ∈ l, recHalf (GF := GF) γ ((k : Nat) : Int) ∅) -∗
      ([∗list] k ∈ l, initFront (GF := GF) γ ((k : Nat) : Int) 1) -∗
      [∗list] k ∈ l, serverRes γ k
  | [] => by
    iintro - - - -
    iapply bigSepL_nil.2; iempintro
  | k :: l => by
    iintro #Hsh Hts Hrs Hfs
    icases bigSepL_cons.1 $$ Hts with ⟨Ht, Hts⟩
    icases bigSepL_cons.1 $$ Hrs with ⟨Hr, Hrs⟩
    icases bigSepL_cons.1 $$ Hfs with ⟨Hf, Hfs⟩
    iapply bigSepL_cons.2
    isplitl [Ht Hr Hf]
    · unfold serverRes; iframe Ht Hr Hf Hsh
    iapply servers_dist γ l $$ Hsh Hts Hrs Hfs

theorem serverIds_nat : serverIds = ([1, 2, 3, 4, 5] : List Nat).map (fun k : Nat => (k : Int)) :=
  rfl

theorem qR_init (γ : QNames) : (qR (Gg := Gg) γ).B.init = kvAbs [] := rfl

/-- **The kit's start** (see the file header): from the registry, the listed addresses unset and
the wildcards unset, QuePaxa's ghost state and every machine's share. -/
theorem kit_start [hyp.grpc.GrpcWorldHyp qv.grpc] :
    ⊢ regCtx (Gg := Gg) -∗ ([∗list] a ∈ kitAddrs, addrUnset (Gg := Gg) a) -∗
      ([∗list] la ∈ kitLis, lisUnset (Gg := Gg) la) ={⊤}=∗
      ∃ (γ : QNames) (ρ : RemoteGS) (γp : PendNames),
        orchRes γ ∗ ([∗list] a ∈ clientAddrs, remoteAddr (Gg := Gg) (ρ := ρ) (qR γ) a) ∗
        mapCtx (Gg := Gg) (ρ := ρ) (I := QIn) ∗
        pendCtx (Gg := Gg) (qR γ) (qS0 (GF := GF)) γp ∗
        pendLib (Gg := Gg) (qS0 (GF := GF)) γp (qS0 (GF := GF)).M.init ∗
        ([∗list] c ∈ List.range 6, clientRes γ c) ∗
        ([∗list] k ∈ ([1, 2, 3, 4, 5] : List Nat), serverRes γ k) := by
  iintro #Hreg Hs Hl
  unfold kitAddrs
  icases bigSepL_append.1 $$ Hs with ⟨Hs, Hca⟩
  icases bigSepL_append.1 $$ Hs with ⟨Hs, Hcf⟩
  icases bigSepL_append.1 $$ Hs with ⟨Hs, Hcc⟩
  icases bigSepL_append.1 $$ Hs with ⟨Hs, Hcl⟩
  icases bigSepL_append.1 $$ Hs with ⟨Ho, Hun⟩
  icases bigSepL_cons.1 $$ Ho with ⟨Ho, -⟩
  rw [bigSepL_map, bigSepL_map, bigSepL_map]
  unfold kitLis
  icases bigSepL_append.1 $$ Hl with ⟨Hpx, Hrc⟩
  rw [bigSepL_map, bigSepL_map]
  imod alloc_init (Gg := Gg) with ⟨%γ0, Hc, Hsm, Ho0⟩
  imod hyp.grpc.GrpcWorldHyp.world_alloc (V := qv.grpc) (consensusMS γ0) ⊤ with ⟨%g, #Hw⟩
  rw [show (⟨consensusMS γ0, g⟩ : hyp.grpc.GrpcWorld GF) = world { γ0 with grpc := g } from rfl]
  rw [show consRes (Gg := Gg) γ0 = consRes { γ0 with grpc := g } from rfl,
    show smrRes (Gg := Gg) γ0 = smrRes { γ0 with grpc := g } from rfl,
    show ownRes (Gg := Gg) γ0 = ownRes { γ0 with grpc := g } from rfl]
  generalize ({ γ0 with grpc := g } : QNames) = γ
  imod net_setup γ $$ Hreg Hw Ho Hun Hcl Hcc Hcf Hpx Hrc with #Hnet
  iunfold ownRes at Ho0
  icases Ho0 with ⟨Hconf, Hp, Hcnt, Htick, #Hnil, #Hspent, Hrecs, Hfronts, Hnets⟩
  imod inv_alloc consN ⊤ (consInv γ) $$ [Hc] with #Hci
  · inext; iapply consInv_init $$ Hc
  imod inv_alloc smrN ⊤ (smrInv γ) $$ [Hsm] with #Hsi
  · inext; iapply smrInv_init; iframe Hsm Hnil
  ihave #Hb : batchReg γ go!"nil" nilBatch $$ []
  · unfold batchReg; iexists RegEntry.nil; iframe Hnil; ipureintro
    exact ⟨rfl, fun _ => rfl, fun h => (by cases h), fun _ _ _ _ _ h => (by cases h)⟩
  ihave #Hsh : sharedRes γ $$ []
  · unfold sharedRes; iframe Hci Hsi Hnet Hb Hspent
  imod mapCtx_alloc (Gg := Gg) (I := QIn) ⊤ with ⟨%ρ, #Hmap⟩
  imod addrs_set_proto (Gg := Gg) ⊤ (fun _ => reqP (Gg := Gg) (RBase.svc (qR γ)))
    (fun _ => repP (Gg := Gg) (RBase.svc (qR γ))) clientAddrs $$ Hreg Hca with #Hpc
  ihave Hown : (qR (Gg := Gg) γ).sysState (qR (Gg := Gg) γ).B.init $$ [Hp]
  · rw [qR_init]
    unfold qR ownState
    dsimp only
    iexists []
    iframe Hp
    ipureintro; rfl
  imod pend_alloc (Gg := Gg) (qR γ) ⊤ (qS0 (GF := GF)) rfl $$ Hown with ⟨%γp, #Hpend, Hlib⟩
  rw [serverIds_nat, bigSepL_map, bigSepL_map]
  imodintro
  iexists γ, ρ, γp
  isplitl [Hconf]
  · unfold orchRes; iframe Hconf Hsh
  isplitr
  · unfold remoteAddr svcAddr; iexact Hpc
  iframe Hmap Hpend Hlib
  isplitl [Hcnt Htick]
  · iapply clients_dist γ (List.range 6) $$ Hsh Hcnt Htick
  · iapply servers_dist γ [1, 2, 3, 4, 5] $$ Hsh Hnets Hrecs Hfronts

end start

end raxos.examples.quepaxanet
end Perennial
