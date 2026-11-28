/-
The hraft kit's deployment start (notes/dsv-hraft.md, S5g; vr's `vsrnet/Start.lean`): from the protocol
library's registry and the deployment's addresses unset, the kit's ghost state and every machine's share:

* remote's slot map with the client addresses' call budgets `orchBud` (`mapCtx_alloc`), the clients'
  ghost state (`kit_start`: the model's halves, the escrow's map, the counters at 1, the ids' invariant),
  remote's pending library over the model's half (`pend_alloc`);
* the protocols of sizes 3 and 5 before their receipts (`gprot.alloc_names`, over the six servers, the
  first configuration `bootSrvs n`), the draw's map `γc`, the frontier's list `fr` (empty), the share
  tokens `sh` (keys 0..6: 0 the orchestrator's `drawTok`, `j` server `j`'s), the draw's invariant
  (undrawn);
* the rpc world `W` (raw net/rpc; the services `kitSSOf`: the drawn protocol's `RaftRPC` and `API` at
  each server address), its registry's invariant, a listener at each server address (`rpcLisP_set`,
  from the address unset: `addrUnset_lisUnset`), the configuration addresses' `confProto`, the client
  addresses' remote protocols of `regR K.g.st`;
* the shares: the orchestrator's `orchShare K γp`, client `c`'s `cliShare K c` (`Client.spec`'s
  precondition but its packages' facts and the codec), server `j`'s `srvShare K j`.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.OrchDefs
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.TopLevelDefs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.hashicorp.raft.examples.hraftnet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote
open github_com.hashicorp.raft github_com.hashicorp.raft.gprot github_com.hashicorp.raft.proto

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem serverAddrs_ok [GooseExts] : ∀ a ∈ serverAddrs, addrOk a = true ∧ listenOk a = true := by
  decide

/-- The clients' counters at the start: client `c < 5` at 1. -/
def seqs0 : GMap Nat Nat :=
  ((((((∅ : GMap Nat Nat).insert 4 1).insert 3 1).insert 2 1).insert 1 1).insert 0 1)


section lis
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF]

/-- At a valid address, the address unset is the listener at it unset (an exact listener; rpcdriver's,
for any `GF`). -/
theorem addrUnset_lisUnset' (a : GoString) (h : addrOk a = true) :
    addrUnset (Gg := G) a ⊢ lisUnset (Gg := G) a := by
  have hl : PartialMap.get? (addrSpace ()) a = some () := by
    rw [gmap_get?_eq]; exact addrSpace_lookup_ok () h
  unfold addrUnset lisUnset
  have key : ∀ {k : GoString} {v : Unit}, PartialMap.get? (Std.delete (addrSpace ()) a) k = some v →
      (iprop(□ True) : IProp GF) ⊢
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

/-- Raw net/rpc listeners at the addresses `l`, from their addresses unset. -/
theorem rpcLis_set_all [NetProtoGS] (W : net.rpc.RpcWorld GF) (hW : ∀ a, W.hs a = [] ∧ W.hsAns a = []) :
    ∀ l : List GoString, (∀ a ∈ l, addrOk a = true ∧ listenOk a = true) →
    ⊢ regCtx (Gg := G) -∗ inv net.rpc.regN' (net.rpc.regInv (Gg := G) W) -∗
      ([∗list] a ∈ l, addrUnset (Gg := G) a) ={⊤}=∗ [∗list] a ∈ l, net.rpc.rpcLisP (Gg := G) W a [] []
  | [], _ => by
    iintro - - -
    imodintro
    iapply BigSepL.bigSepL_nil.2; iempintro
  | a :: l, hl => by
    iintro #Hreg #Hrw Hs
    icases BigSepL.bigSepL_cons.1 $$ Hs with ⟨Ha, Hs⟩
    have ha := hl a List.mem_cons_self
    ihave Hla := addrUnset_lisUnset' a ha.1 $$ Ha
    imod net.rpc.rpcLisP_set ⊤ W a [] [] ha.2 (fun b _ => hW b) $$ Hreg Hrw Hla with #Hp
    imod rpcLis_set_all W hW l (fun b hb => hl b (List.mem_cons_of_mem _ hb)) $$ Hreg Hrw Hs with Hps
    imodintro
    iapply BigSepL.bigSepL_cons.2
    iframe Hp Hps

end lis

section start
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [package_sem : github_com.hashicorp.raft.Assumptions]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]


/-- **The world's services** at the server addresses, of the deployment's ghost names `K`: server
`j`'s address (`serverAddrs[j-1]`) offers the drawn protocol's `RaftRPC` of `j` and the `API`. -/
def kitSSOf (K : HK GF) (a svc : GoString) : Option (net.rpc.MethodSpec GF) :=
  if a ∈ serverAddrs then
    (if svc = rpctransport.svcName then some (raftSvcK K (serverAddrs.idxOf a + 1))
     else if svc = go!"API" then some (apiSvcK K) else none)
  else none

theorem serverAddrs_idx (j : Nat) (hj : 1 ≤ j ∧ j ≤ 6) :
    serverAddrs.getD (j - 1) go!"" ∈ serverAddrs ∧
      serverAddrs.idxOf (serverAddrs.getD (j - 1) go!"") + 1 = j := by
  have : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem kitSS_of (K : HK GF) (h : ∀ a svc, K.W.SS a svc = kitSSOf K a svc) : kitSS K := by
  intro j svc hj1 hj6
  rw [h]
  unfold kitSSOf
  obtain ⟨hm, hi⟩ := serverAddrs_idx j ⟨hj1, hj6⟩
  rw [if_pos hm, hi]

/-- Client machine `c`'s share of the start: `Client.spec`'s precondition but its packages' facts and
net/rpc's codec. -/
def cliShare [ρ : RemoteGS] (K : HK GF) (c : Nat) : IProp GF :=
  iprop(⌜kitSS K⌝ ∗ drawInv K ∗ idInv K.g ∗ seqOwn K.g c 1 ∗
    ([∗list] a ∈ serverAddrs, net.rpc.rpcAddr (Gg := hG.goose_globalGS) K.W a) ∗
    remoteAddr (Gg := hG.goose_globalGS) (regR K.g.st) (clientAddrs.getD c go!"") ∗
    ⌜ρ.bud (clientAddrs.getD c go!"") = some orchBud⌝)

theorem seqs0_split (g : KG) :
    ([∗map] c ↦ m ∈ seqs0, seqOwn (GF := GF) g c m) ⊢ [∗list] c ∈ List.range 5, seqOwn g c 1 := by
  unfold seqs0
  iintro H
  icases (BigSepM.bigSepM_insert (by rfl)).1 $$ H with ⟨H0, H⟩
  icases (BigSepM.bigSepM_insert (by rfl)).1 $$ H with ⟨H1, H⟩
  icases (BigSepM.bigSepM_insert (by rfl)).1 $$ H with ⟨H2, H⟩
  icases (BigSepM.bigSepM_insert (by rfl)).1 $$ H with ⟨H3, H⟩
  icases (BigSepM.bigSepM_insert (by rfl)).1 $$ H with ⟨H4, -⟩
  simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append]
  iframe H0 H1 H2 H3 H4
  iapply BigSepL.bigSepL_nil.2; iempintro


theorem drawInv_alloc (K : HK GF) :
    ghostMapAuth (GF := GF) (K := Nat) (V := Nat) K.γc 1 ∅ ⊢ |={⊤}=> drawInv K := by
  iintro H
  unfold drawInv
  imod inv_alloc drawN ⊤ iprop(∃ m : GMap Nat Nat, ghostMapAuth K.γc 1 m ∗
    (⌜m = ∅⌝ ∨ ∃ n : Nat, ⌜m = (∅ : GMap Nat Nat).insert 0 n⌝ ∗ drawTok K ∗
      service.frInv (K.γs n) (K.fcs n) ∗ [∗list] j ∈ List.range' 1 6, (srvPkg K n j ∨ shareTok K j)))
    $$ [H] with #Hi
  · inext
    iexists ∅
    iframe H
    ileft; ipureintro; rfl
  imodintro
  iexact Hi

/-- What every server's share holds but its token. -/
def srvPers (K : HK GF) : IProp GF :=
  iprop(confProtos K.γc ∗ ([∗list] a ∈ serverAddrs, net.rpc.rpcAddr (Gg := hG.goose_globalGS) K.W a) ∗
    ([∗list] a ∈ serverAddrs, net.rpc.rpcLisP (Gg := hG.goose_globalGS) K.W a [] []) ∗
    ⌜kitSS K ∧ γsOk K⌝ ∗ drawInv K)

instance srvPers_persistent (K : HK GF) : Persistent (srvPers K) := by
  unfold srvPers; infer_instance

theorem srvShare_of (K : HK GF) (j : Nat) (hj : 1 ≤ j ∧ j ≤ 6) :
    □ srvPers K ∗ shareTok K j ⊢ srvShare K j := by
  iintro ⟨#Hp, Ht⟩
  unfold srvPers
  icases Hp with ⟨#Hcp, #Hra, #Hl, %Hss, #Hdi⟩
  unfold srvShare
  iframe Hcp Hra Hdi Ht
  isplitr
  · iapply (BigSepL.bigSepL_lookup (Φ := fun _ a => net.rpc.rpcLisP (Gg := hG.goose_globalGS) K.W a [] [])
      (i := j - 1) ?_) $$ Hl
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [serverAddrs]; omega)]
    rfl
  ipureintro; exact Hss

theorem clientAddrs_getD (c : Nat) (hc : c < 5) :
    clientAddrs[c]? = some (clientAddrs.getD c go!"") := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa [clientAddrs] using hc)]
  rfl

/-- **The start**: the kit's ghost state, the addresses' protocols, remote's slot map and pending
library, and every machine's share. -/
theorem hraft_start :
    ⊢ regCtx (Gg := hG.goose_globalGS) -∗
      ([∗list] a ∈ hraftKitAddrs, addrUnset (Gg := hG.goose_globalGS) a) ={⊤}=∗
      ∃ (ρ : RemoteGS) (K : HK GF) (γp : PendNames), orchShare (ρ := ρ) K γp ∗
        ([∗list] c ∈ List.range 5, cliShare (ρ := ρ) K c) ∗
        ([∗list] j ∈ List.range' 1 6, srvShare K j) := by
  iintro #Hreg Hs
  unfold hraftKitAddrs
  icases BigSepL.bigSepL_append.1 $$ Hs with ⟨Hs, Hsc⟩
  icases BigSepL.bigSepL_append.1 $$ Hs with ⟨Hsv, Hscf⟩
  imod mapCtx_alloc (Gg := hG.goose_globalGS) (I := HIn) ⊤ clientAddrs orchBud (by decide)
    with ⟨%ρ, %Hρ, #Hmap, Hunits⟩
  imod kit_start (GF := GF) seqs0 with ⟨%g, Hkp, Hst, #Hid, Hseqs⟩
  have hv : ghostVar (GF := GF) (A := service.Reg) g.st (1 : Qp).half none ⊢
      (regR (GF := GF) (Gg := hG.goose_globalGS) g.st).sysState
        (regR (GF := GF) (Gg := hG.goose_globalGS) g.st).B.init := .rfl
  ihave Hst := hv $$ Hst
  haveI : ∀ st, Timeless ((regR (GF := GF) (Gg := hG.goose_globalGS) g.st).sysState st) :=
    fun st => by unfold regR; infer_instance
  imod pend_alloc (Gg := hG.goose_globalGS) (regR g.st) ⊤ (regS (GF := GF)) rfl $$ Hst
    with ⟨%γp, #Hpend, Hlib⟩
  imod alloc_names (GF := GF) ⊤ allSids (genesisOf (bootSrvs 3)) (cfgDec allSids) allSids_nodup rfl
    with ⟨%γ3, %h3, Hops3, Hpre3⟩
  imod alloc_names (GF := GF) ⊤ allSids (genesisOf (bootSrvs 5)) (cfgDec allSids) allSids_nodup rfl
    with ⟨%γ5, %h5, Hops5, Hpre5⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Nat) with ⟨%γc, Hc⟩
  imod mono_list_own_alloc (GF := GF) (A := proto.Entry) [] with ⟨%fr, Hfr, -⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Unit) with ⟨%sh, Hsh⟩
  imod ghost_map_insert (GF := GF) 0 () (by rfl) $$ Hsh with ⟨Hsh, Ht0⟩
  imod ghost_map_insert (GF := GF) 1 () (by rfl) $$ Hsh with ⟨Hsh, Ht1⟩
  imod ghost_map_insert (GF := GF) 2 () (by rfl) $$ Hsh with ⟨Hsh, Ht2⟩
  imod ghost_map_insert (GF := GF) 3 () (by rfl) $$ Hsh with ⟨Hsh, Ht3⟩
  imod ghost_map_insert (GF := GF) 4 () (by rfl) $$ Hsh with ⟨Hsh, Ht4⟩
  imod ghost_map_insert (GF := GF) 5 () (by rfl) $$ Hsh with ⟨Hsh, Ht5⟩
  imod ghost_map_insert (GF := GF) 6 () (by rfl) $$ Hsh with ⟨-, Ht6⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := net.rpc.RpcConnNames) with ⟨%γw, Hw⟩
  let K0 : HK GF := ⟨γc, fun n => if n = 3 then γ3 else γ5, g, fr,
    ⟨fun _ _ => none, γw, fun _ => [], fun _ => []⟩, sh⟩
  let K : HK GF := ⟨γc, fun n => if n = 3 then γ3 else γ5, g, fr,
    ⟨kitSSOf K0, γw, fun _ => [], fun _ => []⟩, sh⟩
  have hss : kitSS K := kitSS_of K (fun _ _ => rfl)
  have hγ : γsOk K := by
    intro n hn
    rcases hn with rfl | rfl
    · exact h3
    · exact h5
  imod inv_alloc net.rpc.regN' ⊤ (net.rpc.regInv (Gg := hG.goose_globalGS) K.W) $$ [Hw] with #HregW
  · inext
    unfold net.rpc.regInv
    iexists ∅
    isplitl [Hw]
    · iexact Hw
    iapply BigSepM.bigSepM_empty.2; iempintro
  imod rpcLis_set_all (G := hG.goose_globalGS) K.W (fun _ => ⟨rfl, rfl⟩) serverAddrs serverAddrs_ok
    $$ Hreg HregW Hsv with #Hlis
  ihave #Hra : [∗list] a ∈ serverAddrs, net.rpc.rpcAddr (Gg := hG.goose_globalGS) K.W a $$ []
  · iapply (BigSepL.bigSepL_mono (Φ := fun _ a => net.rpc.rpcLisP (Gg := hG.goose_globalGS) K.W a [] [])
      (Ψ := fun _ a => net.rpc.rpcAddr (Gg := hG.goose_globalGS) K.W a)
      (fun {k a} hk => net.rpc.rpcLisP_addrOk K.W a [] []
        (serverAddrs_ok a (List.mem_of_getElem? hk)).1)) $$ Hlis
  imod addrs_set_proto (Gg := hG.goose_globalGS) ⊤ (fun _ => confProto γc) (fun _ => ackProto) confAddrs
    $$ Hreg Hscf with #Hpcf
  imod addrs_set_proto (Gg := hG.goose_globalGS) ⊤
    (fun a => reqP (Gg := hG.goose_globalGS) (RBase.svc (regR (Gg := hG.goose_globalGS) g.st)) a)
    (fun _ => repP (Gg := hG.goose_globalGS) (RBase.svc (regR (Gg := hG.goose_globalGS) g.st))) clientAddrs
    $$ Hreg Hsc with #Hpc
  ihave #Hrem : [∗list] a ∈ clientAddrs, remoteAddr (Gg := hG.goose_globalGS) (regR K.g.st) a $$ [Hpc]
  · unfold remoteAddr svcAddr; iexact Hpc
  ihave #Hcp : confProtos (G := hG.goose_globalGS) K.γc $$ [Hpcf]
  · unfold confProtos; iexact Hpcf
  imod drawInv_alloc K $$ [Hc] with #Hdi
  · iexact Hc
  ihave Hseqs := seqs0_split g $$ Hseqs
  ihave #Hsp : srvPers K $$ []
  · unfold srvPers
    iframe Hcp Hra Hlis Hdi
    ipureintro; exact ⟨hss, hγ⟩
  imodintro
  iexists ρ, K, γp
  isplitl [Ht0 Hops3 Hpre3 Hops5 Hpre5 Hkp Hfr Hlib Hunits]
  · unfold orchShare
    iframe Hcp Hra Hdi Hrem Hmap Hpend Hlib Hunits
    isplitr
    · ipureintro; exact ⟨hss, hγ⟩
    isplitl [Ht0]
    · unfold drawTok; iexact Ht0
    unfold drawPre drawPre1
    simp only [K, ↓reduceIte, Nat.reduceEqDiff]
    iframe Hops3 Hpre3 Hops5 Hpre5 Hkp Hfr
  isplitl [Hseqs]
  · iapply (BigSepL.bigSepL_impl (Φ := fun _ c => seqOwn (GF := GF) g c 1)) $$ Hseqs
    imodintro
    iintro %k %c %hk Hn
    have hc : c < 5 := by
      have := List.mem_of_getElem? hk
      simpa using this
    unfold cliShare
    iframe Hdi Hid Hra Hn
    isplitr; · ipureintro; exact hss
    isplitr
    · iapply BigSepL.bigSepL_lookup (clientAddrs_getD c hc) $$ Hrem
    ipureintro
    rw [Hρ, if_pos (List.mem_of_getElem? (clientAddrs_getD c hc))]
  rw [show List.range' 1 6 = [1, 2, 3, 4, 5, 6] from rfl]
  iapply BigSepL.bigSepL_cons.2
  isplitl [Ht1]
  · iapply srvShare_of K 1 ⟨by omega, by omega⟩; iframe Hsp; unfold shareTok; iexact Ht1
  iapply BigSepL.bigSepL_cons.2
  isplitl [Ht2]
  · iapply srvShare_of K 2 ⟨by omega, by omega⟩; iframe Hsp; unfold shareTok; iexact Ht2
  iapply BigSepL.bigSepL_cons.2
  isplitl [Ht3]
  · iapply srvShare_of K 3 ⟨by omega, by omega⟩; iframe Hsp; unfold shareTok; iexact Ht3
  iapply BigSepL.bigSepL_cons.2
  isplitl [Ht4]
  · iapply srvShare_of K 4 ⟨by omega, by omega⟩; iframe Hsp; unfold shareTok; iexact Ht4
  iapply BigSepL.bigSepL_cons.2
  isplitl [Ht5]
  · iapply srvShare_of K 5 ⟨by omega, by omega⟩; iframe Hsp; unfold shareTok; iexact Ht5
  iapply BigSepL.bigSepL_cons.2
  isplitl [Ht6]
  · iapply srvShare_of K 6 ⟨by omega, by omega⟩; iframe Hsp; unfold shareTok; iexact Ht6
  iapply BigSepL.bigSepL_nil.2; iempintro

end start

end github_com.hashicorp.raft.examples.hraftnet
end Perennial
