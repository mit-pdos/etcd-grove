/-
**The deployment's start** (in place of the lab's `Proof/swiftnet/Start.lean`, `StartOk`, for the
kit over remote; dsv-epaxos's `ep_ghost_start`/`ep_start` are the pattern): from the start's
registry (`regCtx`), the deployment's exact addresses unset (`swStartAddrs`: the plain addresses
and the replicas' rpc ports) and its listeners unset (`swLas`: the master's wildcard `":7001"` and
the replicas' peer wildcards `replicaLis`), allocate

* the configuration's and the membership's mono lists (their writers' tokens to the orchestrator
  and the master), the slot's abstract key-value state `γ.lin` (half to `sp.alloc`, half to the
  link invariant), the SwiftPaxos names, invariant, client and replica shares and prediction
  tokens (`sp.alloc`);
* the net/rpc world: the raw world `W₀ = ⟨services γc γm, γw⟩`, the kit's world its HTTP form
  `RpcHttpAddr.httpW W₀` (Upamanyu's EPaxos review, 1), the latter's connection registry
  (`regInv`, at `W₀`'s name: `httpW_reg`);
* remote's store's ghost variable `γk` at the model's initial state (half `sysK γk`, which the
  top level hands to remote's pending library, half to the link invariant `linkInv γ γk`);

and set the protocols: the plain addresses' (`addrs_set_proto`, `protoP`/`protoQ`), the replicas'
peer listeners' (`lis_set_proto`, `sp.inP`/`sp.outQ`), and the rpc listeners' over HTTP
(`RpcHttpAddr.rpcLisP_set`, at `":7001"` and, as exact listeners, at the replicas' rpc ports;
the handshake premise from `httpW_hs`/`httpW_hsAns`). The result: `common γ` and each node's share
(`conf.writer γ`, `clientNodeShare γ c`, `serverShare γ i`), the link invariant and `sysK γk` at
the initial state.

The client machines' request addresses (`clientAddrs`) are remote's: the top level sets them.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ClientLin
public import GooseLang.Ext.Net.Decide

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-! ## The deployment's addresses and listeners -/

/-- The addresses the start takes, unset: the plain addresses and the replicas' rpc ports. -/
def swStartAddrs : List GoString := plainAddrs ++ replicaRpcAddrs

/-- The deployment's exact addresses (`DistDeploy`'s): the start's and the client machines'
request addresses (remote's). -/
def swAddrs : List GoString := swStartAddrs ++ clientAddrs

/-- The master's wildcard rpc listener (`master.Run`'s `net.Listen("tcp", ":7001")`). -/
def masterLis : GoString := go!":7001"

/-- The deployment's listeners: the master's and the replicas' peer wildcards. -/
def swLas : List GoString := masterLis :: replicaLis

theorem swStartAddrs_lit :
    swStartAddrs =
      [go!"127.0.0.1:6100", go!"127.0.0.1:6101", go!"127.0.0.1:6102", go!"127.0.0.1:6103",
       go!"127.0.0.1:6104", go!"127.0.0.1:6105", go!"127.0.0.1:6106",
       go!"127.0.0.1:8101", go!"127.0.0.1:8102", go!"127.0.0.1:8103", go!"127.0.0.1:8104",
       go!"127.0.0.1:8105", go!"127.0.0.1:8106",
       go!"127.0.0.1:9101", go!"127.0.0.1:9102", go!"127.0.0.1:9103", go!"127.0.0.1:9104",
       go!"127.0.0.1:9105", go!"127.0.0.1:9106",
       go!"127.0.0.1:9001", go!"127.0.0.1:9002", go!"127.0.0.1:9003", go!"127.0.0.1:9004",
       go!"127.0.0.1:9005", go!"127.0.0.1:9006",
       go!"127.0.0.1:8002", go!"127.0.0.1:8003", go!"127.0.0.1:8004", go!"127.0.0.1:8005",
       go!"127.0.0.1:8006"] := rfl

theorem swAddrs_nodup : swAddrs.Nodup := by
  rw [swAddrs, swStartAddrs_lit]; decide

theorem swAddrs_ok : ∀ a ∈ swAddrs, addrOk a = true := by
  rw [swAddrs, swStartAddrs_lit]; decide

/-- Two wildcard listeners at different ports take no address in common. -/
theorem wild_disj (l1 l2 : GoString)
    (h : (wildPort l1).isSome = true ∧ portOf l1 = wildPort l1 ∧ portOf l2 = wildPort l2 ∧
      wildPort l1 ≠ wildPort l2 ∧ l1 ≠ l2) :
    ∀ a, lisAccepts l1 a → ¬ lisAccepts l2 a := by
  obtain ⟨hs, hp1, hp2, hne, hl⟩ := h
  intro a ha hb
  unfold lisAccepts at ha hb
  rcases ha with rfl | ⟨q, hq, ha⟩
  · rcases hb with heq | ⟨r, hr, hb⟩
    · exact hl heq.symm
    · rw [hp1] at hb; rw [hb, hr] at hne; exact hne rfl
  · rcases hb with rfl | ⟨r, hr, hb⟩
    · rw [hp2, ← hq] at ha; rw [ha] at hne; exact hne rfl
    · rw [ha] at hb; cases hb; rw [hq, hr] at hne; exact hne rfl

theorem swLas_pairwise :
    swLas.Pairwise (fun l1 l2 => ∀ a, lisAccepts l1 a → ¬ lisAccepts l2 a) := by
  have hnd : swLas.Nodup := by decide
  have hc : ∀ l1 ∈ swLas, ∀ l2 ∈ swLas, l1 ≠ l2 →
      ((wildPort l1).isSome = true ∧ portOf l1 = wildPort l1 ∧ portOf l2 = wildPort l2 ∧
        wildPort l1 ≠ wildPort l2 ∧ l1 ≠ l2) := by decide
  exact hnd.imp_of_mem (fun h1 h2 hne => wild_disj _ _ (hc _ h1 _ h2 hne))

theorem masterLis_ok : listenOk masterLis = true := by decide

theorem replicaLis_ok : ∀ la ∈ replicaLis, listenOk la = true := by decide

theorem masterLis_master : lisAccepts masterLis masterAddr :=
  lisAcceptsB_iff.1 (by decide)

theorem replicaRpcAddrs_ok : ∀ a ∈ replicaRpcAddrs, addrOk a = true := by decide

theorem swLas_disj : ∀ a ∈ swAddrs, ∀ la ∈ swLas, ¬ lisAccepts la a := by
  have hb : ∀ a ∈ swAddrs, ∀ la ∈ swLas, lisAcceptsB la a = false := by
    rw [swAddrs, swStartAddrs_lit]; decide
  intro a ha la hla h
  rw [← lisAcceptsB_iff, hb a ha la hla] at h
  cases h

/-! ## The ghost start -/

/-- A list's addresses' tokens, from their validity (`addrTok` is pure). -/
theorem addrToks_of {GF : BundledGFunctors} (l : List GoString) (h : ∀ a ∈ l, addrOk a = true) :
    ⊢ ([∗list] a ∈ l, addrTok (GF := GF) a) := by
  induction l with
  | nil => iapply BigSepL.bigSepL_nil.2; iempintro
  | cons a l ih =>
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · unfold addrTok; ipureintro; exact h a (List.mem_cons_self ..)
    · iapply ih (fun x hx => h x (List.mem_cons_of_mem _ hx))

section ghost
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF] [SwiftNetPkgState netDistGF]

/-- At a valid address, the address unset is the listener at it unset (an exact listener;
dsv-epaxos's). -/
theorem addrUnset_lisUnset (a : GoString) (h : addrOk a = true) :
    addrUnset (GF := netDistGF) a ⊢ lisUnset a := by
  have hl : PartialMap.get? (addrSpace ()) a = some () := by
    rw [gmap_get?_eq]; exact addrSpace_lookup_ok () h
  unfold addrUnset lisUnset
  have key : ∀ {k : GoString} {v : Unit}, PartialMap.get? (Std.delete (addrSpace ()) a) k = some v →
      (iprop(□ True) : IProp netDistGF) ⊢
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

/-- **The ghost start** (see the file header). -/
theorem sw_start [RA : RpcHttpAddr netDistGF] :
    ⊢ regCtx (Gg := G) -∗ ([∗list] a ∈ swStartAddrs, addrUnset a) -∗
      ([∗list] la ∈ swLas, lisUnset la) ={⊤}=∗
      ∃ (γ : SwiftNames netDistGF) (γk : GName),
        common γ ∗ conf.writer γ ∗ cnode.linkInv γ γk ∗
        cnode.sysK γk (examples.swiftnet.swB.init) ∗
        ([∗list] c ∈ List.range 6, clientNodeShare γ c) ∗
        ([∗list] i ∈ List.range 6, serverShare γ i) := by
  iintro #Hreg Hs Hl
  -- the ghost names
  imod mono_list_own_alloc (GF := netDistGF) ([] : List Conf) with ⟨%γc, Hc, -⟩
  imod mono_list_own_alloc (GF := netDistGF) ([] : List (List GoString)) with ⟨%γm, Hm, -⟩
  imod ghostVar_alloc (GF := netDistGF) ([] : List (GoString × GoString)) with ⟨%γl, Hlv⟩
  icases (ghostVar_split_half γl 1 _).1 $$ Hlv with ⟨Hl1, Hl2⟩
  imod sp.alloc γc γm γl $$ Hl2 with ⟨%γsp, #Hinv, Hcl, Hreps, Hpt⟩
  imod ghostVar_alloc (GF := netDistGF) (cnode.kpair examples.swiftnet.swB.init) with ⟨%γk, Hkv⟩
  icases (ghostVar_split_half γk 1 _).1 $$ Hkv with ⟨Hk1, Hk2⟩
  imod ghost_map_alloc_empty (GF := netDistGF) (K := Nat) (V := net.rpc.RpcConnNames)
    with ⟨%γw, Hw⟩
  let W₀ : net.rpc.RpcWorld netDistGF := { SS := services γc γm, reg := γw }
  let W : net.rpc.RpcWorld netDistGF := RA.httpW W₀
  let γ : SwiftNames netDistGF := ⟨γc, γm, W, γsp, γl⟩
  have HW : W.SS = services γc γm := RA.httpW_SS W₀
  have hhs : ∀ a, RA.worldHs W a = connectReq defaultRPCPath ∧ RA.worldHsAns W a = connectAns :=
    fun a => ⟨RA.httpW_hs W₀ a, RA.httpW_hsAns W₀ a⟩
  -- the rpc world's connection registry
  imod inv_alloc net.rpc.regN' ⊤ (net.rpc.regInv W) $$ [Hw] with #HregW
  · inext
    unfold net.rpc.regInv
    rw [show W.reg = γw from RA.httpW_reg W₀]
    iexists ∅
    iframe Hw
    iapply BigSepM.bigSepM_empty.2; iempintro
  -- the link invariant
  imod inv_alloc cnode.linkN ⊤ (cnode.linkI γ γk) $$ [Hk2 Hl1] with #Hlink
  · inext
    unfold cnode.linkI
    iexists cnode.kpair examples.swiftnet.swB.init, []
    iframe Hk2 Hl1
    ipureintro
    constructor <;> rfl
  -- the protocols
  unfold swStartAddrs
  icases BigSepL.bigSepL_append.1 $$ Hs with ⟨Hp, Hr⟩
  imod addrs_set_proto ⊤ (protoP γ) (protoQ γ) plainAddrs $$ Hreg Hp with #Hpp
  unfold swLas masterLis
  icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Hml, Hrl⟩
  ihave Hrl : [∗list] la ∈ replicaLis,
      |={⊤}=> lisProto la (sp.inP γ.sp γ.conf γ.mem) (sp.outQ γ.sp γ.conf γ.mem) $$ [Hrl]
  · iapply BigSepL.bigSepL_impl $$ Hrl
    iintro !> %j %la %hla Hu
    iapply lis_set_proto ⊤ la _ _ (replicaLis_ok la (List.mem_of_getElem? hla)) $$ Hreg Hu
  imod BigSepL2.bigSepL_fupd ⊤ _ _ $$ Hrl with #Hrl
  imod RA.rpcLisP_set ⊤ γ.W go!":7001" _ _ masterLis_ok (fun a _ => hhs a) $$ Hreg HregW Hml
    with #Hml
  ihave Hr : [∗list] a ∈ replicaRpcAddrs,
      |={⊤}=> RA.rpcLisP γ.W a (connectReq defaultRPCPath) connectAns $$ [Hr]
  · iapply BigSepL.bigSepL_impl $$ Hr
    iintro !> %j %a %ha Hu
    have hok : addrOk a = true := replicaRpcAddrs_ok a (List.mem_of_getElem? ha)
    ihave Hu := addrUnset_lisUnset a hok $$ Hu
    iapply RA.rpcLisP_set ⊤ γ.W a _ _ (by simp [listenOk, hok]) (fun a _ => hhs a)
      $$ Hreg HregW Hu
  imod BigSepL2.bigSepL_fupd ⊤ _ _ $$ Hr with #Hr
  ihave #Hcommon : common γ $$ []
  · unfold common
    iframe Hpp Hrl Hinv
    isplitr
    · ipureintro; exact HW
    unfold rpcLis
    iapply BigSepL.bigSepL_cons.2
    isplitl []
    · iexact Hml
    iexact Hr
  -- the shares
  ihave Hcs := sp.clientsStart_split $$ Hcl
  unfold sp.allPNodes
  icases BigSepL.bigSepL_append.1 $$ Hpt with ⟨Hptc, Hptr⟩
  rw [BigSepL.bigSepL_map, BigSepL.bigSepL_map]
  imodintro
  iexists γ, γk
  unfold cnode.linkInv cnode.sysK
  iframe Hcommon Hlink Hk1
  isplitl [Hc]
  · unfold conf.writer; iexact Hc
  isplitl [Hcs Hptc]
  · ihave H := BigSepL.bigSepL_sep_eqv.2 $$ [Hcs Hptc]
    · iframe Hcs Hptc
    iapply BigSepL.bigSepL_impl $$ H
    iintro !> %j %c %hc ⟨H1, H2⟩
    have hc6 : c < 6 := List.mem_range.1 (List.mem_of_getElem? hc)
    unfold clientNodeShare
    iframe H1 H2 Hcommon
    have hok : ∀ x ∈ [clientNodeAddrs.getD c go!"", clientConfAddrs.getD c go!"",
        clientStartAddrs.getD c go!""], addrOk x = true := by
      match c, hc6 with
      | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ => decide
    have hok' := fun i h => hok _ (List.getElem_mem (l := [clientNodeAddrs.getD c go!"",
      clientConfAddrs.getD c go!"", clientStartAddrs.getD c go!""]) (n := i) h)
    unfold addrTok
    isplitr
    · ipureintro; exact hok' 0 (by simp)
    isplitr
    · ipureintro; exact hok' 1 (by simp)
    ipureintro; exact hok' 2 (by simp)
  · rw [show List.range 6 = 0 :: (List.range 5).map Nat.succ from rfl]
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hm]
    · unfold serverShare
      simp only [↓reduceIte]
      iframe Hcommon
      isplitr
      · iapply addrToks_of; decide
      unfold mem.writer; iexact Hm
    rw [BigSepL.bigSepL_map]
    ihave H := BigSepL.bigSepL_sep_eqv.2 $$ [Hreps Hptr]
    · iframe Hreps Hptr
    iapply BigSepL.bigSepL_impl $$ H
    iintro !> %j %k %hk ⟨H1, H2⟩
    have hk5 : k < 5 := List.mem_range.1 (List.mem_of_getElem? hk)
    unfold serverShare
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one]
    iframe H1 H2 Hcommon
    iapply addrToks_of
    match k, hk5 with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => decide

end ghost

end Perennial.github_com.imdea_software.swiftpaxos
