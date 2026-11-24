/-
**The deployment's start** (the lab's `Epaxos/Top/Start.lean` and `Proof/top/StartLemmas.lean`,
ported onto this port's vocabulary; notes/dsv-epaxos.md, "Next"): from the start's registry
(`regCtx`), the addresses unset (the replicas' peer addresses `127.0.0.1:7502..7506`, their rpc
addresses `127.0.0.1:8502..8506`) and the master's wildcard listener unset (`lisUnset ":7501"`,
`Bridge.lean`'s `robust_of_distProtoLisRB`), allocate the ghost state and the invariants (the
abstract key-value state's ghost variable, both halves; the fired outputs' map; the role registry
`roleInv` with the escrows' names; the registry of the registration exchange; the peer streams'
and the replicas' framework state; the protocol invariant `epInv`), the net/rpc world `W`
(`RpcHttpAddr.httpW W₀`, `W₀ = { SS := rpcSS γ, reg := γw, hs, hsAns }` with HTTP's
handshake, as models-rpc-http's start builds it: served over HTTP at every address, `W.SS = rpcSS γ`, its
connection registry `regInv W`), set the replica addresses' protocols
(`repDialP`/`repAccP`, `addrs_set_proto`) and the rpc listeners' (`RpcHttpAddr.rpcLisP_set` at
`":7501"` and at each `rpcAddrOf k`, an exact listener: `addrUnset_lisUnset`), and hand out each
machine's resources (`masterRes`, `replicaRes`, the client machines' `clientInvs`, the store's
`own_state`).

The client machines' addresses (`127.0.0.1:7511..7520`) are remote's (their protocols are the
client side's): `ep_start` does not take them; `epAddrs` lists them for the bridge.

The rpc part is over a machine heap (`RpcHttpHyp` is a class over `HeapGS`); `ep_ghost_start` is
the part over the global ghost state only.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.RpcHttpHyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.NetRpc.Methods
public import GooseLang.Ext.Net.Decide

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet

open github_com.imdea_software.swiftpaxos_epaxos github_com.imdea_software.swiftpaxos_epaxos.kvs
open github_com.imdea_software.swiftpaxos_epaxos.model

/-! ## Big separating conjunction plumbing (the lab's `StartLemmas.lean`) -/

section plumbing
variable {PROP : Type _} [BI PROP]

/-- A double big separating conjunction of a separating conjunction, split. -/
theorem bigSepL2d_sep {A B : Type _} (l : List A) (m : List B) (P Q : A → B → PROP) :
    ([∗list] x ∈ l, [∗list] y ∈ m, iprop(P x y ∗ Q x y)) ⊢
      ([∗list] x ∈ l, [∗list] y ∈ m, P x y) ∗ ([∗list] x ∈ l, [∗list] y ∈ m, Q x y) :=
  (BigSepL.bigSepL_mono fun _ => BigSepL.bigSepL_sep_eqv.1).trans BigSepL.bigSepL_sep_eqv.1

/-- The same, joined. -/
theorem bigSepL2d_sep_2 {A B : Type _} (l : List A) (m : List B) (P Q : A → B → PROP) :
    ([∗list] x ∈ l, [∗list] y ∈ m, P x y) ∗ ([∗list] x ∈ l, [∗list] y ∈ m, Q x y) ⊢
      ([∗list] x ∈ l, [∗list] y ∈ m, iprop(P x y ∗ Q x y)) :=
  BigSepL.bigSepL_sep_eqv.2.trans (BigSepL.bigSepL_mono fun _ => BigSepL.bigSepL_sep_eqv.2)

/-- A double big separating conjunction, transposed. -/
theorem bigSepL2d_comm {A B : Type _} (l : List A) (m : List B) (P : A → B → PROP) :
    ([∗list] x ∈ l, [∗list] y ∈ m, P x y) ⊢ ([∗list] y ∈ m, [∗list] x ∈ l, P x y) :=
  (BigSepL.bigSepL_comm (fun _ x _ y => P x y) l m).1

/-- A range's big separating conjunction gives its prefix's (the rest is dropped). -/
theorem bigSepL_range_le [BIAffine PROP] (P : Nat → PROP) (n m : Nat) (h : m ≤ n) :
    ([∗list] j ∈ List.range n, P j) ⊢ [∗list] j ∈ List.range m, P j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.range_add]
  exact BigSepL.bigSepL_append.1.trans sep_elim_left

end plumbing

/-! ## The deployment's addresses -/

/-- The client machines' addresses (`ClientAddrs()`, `kit.go`). -/
def epClientAddrs : List GoString :=
  [go!"127.0.0.1:7511", go!"127.0.0.1:7512", go!"127.0.0.1:7513", go!"127.0.0.1:7514",
   go!"127.0.0.1:7515", go!"127.0.0.1:7516", go!"127.0.0.1:7517", go!"127.0.0.1:7518",
   go!"127.0.0.1:7519", go!"127.0.0.1:7520"]

/-- The addresses the start takes (`ep_start`): the replicas' peer addresses and rpc addresses. -/
def epStartAddrs : List GoString := replicaAddrs ++ replicaRpcAddrs

/-- The deployment's exact addresses (`DistDeploy`'s, `robust_of_distProtoLisRB`'s `addrs`): the
start's and the client machines'. The master's `127.0.0.1:7501` is not one: its wildcard
listener `":7501"` takes it (`epLas`). -/
def epAddrs : List GoString := epStartAddrs ++ epClientAddrs

/-- The master's wildcard listener (`master.go`'s `net.Listen("tcp", ":7501")`). -/
def masterLis : GoString := go!":7501"

/-- The deployment's listeners (`robust_of_distProtoLisRB`'s `las`). -/
def epLas : List GoString := [masterLis]

/-- The replicas' rpc addresses, spelled out (`NetRpc/Methods.lean`'s `replicaRpcAddrs_lit`,
without its section's instances). -/
theorem rpcAddrs_lit :
    replicaRpcAddrs = [go!"127.0.0.1:8502", go!"127.0.0.1:8503", go!"127.0.0.1:8504",
      go!"127.0.0.1:8505", go!"127.0.0.1:8506"] := by
  simp [replicaRpcAddrs, replicaNodes, rpcAddrOf, replicaIp, fmt.decimal, fmt.decimalNat_of_ge,
    fmt.decimalNat_of_lt, fmt.digitByte]

theorem replicaRpcAddrs_ok : ∀ a ∈ replicaRpcAddrs, addrOk a = true := by
  rw [rpcAddrs_lit]; decide

theorem rpcAddrOf_mem' (k : Nat) (hk : k ∈ replicaNodes) : rpcAddrOf k ∈ replicaRpcAddrs :=
  List.mem_map_of_mem hk

theorem epStartAddrs_lit :
    epStartAddrs = [go!"127.0.0.1:7502", go!"127.0.0.1:7503", go!"127.0.0.1:7504",
      go!"127.0.0.1:7505", go!"127.0.0.1:7506", go!"127.0.0.1:8502", go!"127.0.0.1:8503",
      go!"127.0.0.1:8504", go!"127.0.0.1:8505", go!"127.0.0.1:8506"] := by
  rw [epStartAddrs, rpcAddrs_lit]; decide

theorem epAddrs_nodup : epAddrs.Nodup := by
  rw [epAddrs, epStartAddrs_lit]; decide

theorem epAddrs_ok : ∀ a ∈ epAddrs, addrOk a = true := by
  rw [epAddrs, epStartAddrs_lit]; decide

theorem epLas_pairwise :
    epLas.Pairwise (fun l1 l2 => ∀ a, lisAccepts l1 a → ¬ lisAccepts l2 a) := by
  simp [epLas]

theorem epLas_disj : ∀ a ∈ epAddrs, ∀ la ∈ epLas, ¬ lisAccepts la a := by
  intro a ha la hla h
  rw [← lisAcceptsB_iff] at h
  simp only [epLas, List.mem_singleton] at hla
  subst hla
  rw [epAddrs, epStartAddrs_lit] at ha
  revert h
  revert a
  decide

theorem masterLis_ok : listenOk masterLis = true := by decide

theorem masterLis_master : lisAccepts masterLis masterAddr :=
  lisAcceptsB_iff.1 (by decide)

theorem masterAddr_ok : addrOk masterAddr = true := by decide

/-! ## The ghost start -/

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- At a valid address, the address unset is the listener at it unset (an exact listener). -/
theorem addrUnset_lisUnset (a : GoString) (h : addrOk a = true) :
    addrUnset (GF := GF) a ⊢ lisUnset a := by
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

/-- One sent half per direction, as `epInv_init` takes them. -/
theorem sentHalves_ep (γ : EpNames) :
    ([∗list] x ∈ List.range nRep, [∗list] y ∈ List.range nRep, sentHalf (GF := GF) γ x y []) ⊢
      [∗list] fr ∈ List.range nR, [∗list] to ∈ List.range nR,
        if fr = to then iprop(True) else sentHalf γ fr to [] := by
  change _ ⊢ [∗list] fr ∈ List.range nRep, [∗list] to ∈ List.range nRep, _
  refine BigSepL.bigSepL_mono (fun _ => BigSepL.bigSepL_mono (fun _ => ?_))
  split
  · exact true_intro
  · exact .rfl

/-- Each replica's start resources (`repStart`), from the per-direction resources (one sent half
and the delivery right of each direction into it, the dial tokens), the protocol fragments and
the protocol invariant. -/
theorem repStarts (γ : EpNames) :
    ([∗list] x ∈ List.range nRep, [∗list] y ∈ List.range nRep,
        iprop(sentHalf (GF := GF) γ x y [] ∗ delivFrom γ x y 0)) -∗
      ([∗list] x ∈ List.range nRep, [∗list] y ∈ List.range nRep, dialTok γ x y) -∗
      ([∗list] i ∈ List.range nRep, iprop(repFrag γ i (RState.init i) ∗ repIdle γ i)) -∗
      ([∗list] i ∈ List.range nRep, iprop(ghostMapAuth (γ.rep.cwriters i) 1 (∅ : GMap Loc Nat) ∗
        ghostMapAuth (γ.rep.replies i) 1 (∅ : GMap Loc Unit))) -∗
      inv protoN (epInv γ) -∗
      [∗list] i ∈ List.range nRep, repStart γ i := by
  iintro Hfw Hdt Hfr Hcw #Hep
  ihave Hall := BigSepL.bigSepL_sep_eqv.2 $$ [Hfw Hdt]
  · iframe Hfw Hdt
  ihave Hall := BigSepL.bigSepL_sep_eqv.2 $$ [Hall Hfr]
  · iframe Hall Hfr
  ihave Hall := BigSepL.bigSepL_sep_eqv.2 $$ [Hall Hcw]
  · iframe Hall Hcw
  iapply BigSepL.bigSepL_impl $$ Hall
  iintro !> %k %i %hi ⟨⟨⟨Hfw, Hdt⟩, Hfr, Hidle⟩, Hcw1, Hcw2⟩
  have hi5 : i < nRep := by
    have := List.mem_range.1 (List.mem_of_getElem? hi); exact this
  unfold repStart repFwStart epRepStart
  iframe Hfr Hidle Hep Hcw1 Hcw2
  isplitl [Hfw]
  · iapply BigSepL.bigSepL_mono ?_ $$ Hfw
    intro _ j _
    split
    · exact true_intro
    · exact .rfl
  iapply bigSepL_range_le _ nRep (i + 1) hi5 $$ Hdt

/-- The replica addresses' protocols as `clientInvs` names them. -/
def repProtos (γ : EpNames) : IProp GF :=
  [∗list] a ∈ replicaAddrs, addrProto a (repDialP γ a) (repAccP γ a)

/-- **The ghost start** (over the global ghost state only): from the registry and the replicas'
peer addresses unset, the names `γ`, the rpc world `W₀ = { SS := rpcSS γ, reg := γw, hs := fun _ => connectReq defaultRPCPath,
hsAns := fun _ => connectAns }` (models-rpc-http's fields; dsv-gryff's start) with its services
(`rpcSS γ`) and the connection registry of the kit's world `RA.httpW W₀` (`W₀` served over HTTP
at every address; its registry is `W₀`'s, `httpW_reg`), the master's right to fix the node list, every replica node's token, the
registration exchange's invariant (each replica id with its start resources), `clientInvs γ`
(the replica addresses' protocols and the role registry), and the store's half of the initial
abstract state. -/
theorem ep_ghost_start [RA : RpcHttpAddr GF] :
    ⊢ regCtx (Gg := G) -∗ ([∗list] a ∈ replicaAddrs, addrUnset a) ={⊤}=∗
      ∃ (γ : EpNames) (W₀ : net.rpc.RpcWorld GF), ⌜W₀.SS = rpcSS γ⌝ ∗
        inv net.rpc.regN' (net.rpc.regInv (RA.httpW W₀)) ∗ listUnset γ ∗
        ([∗list] k ∈ replicaNodes, nodeTok γ k) ∗ inv regXN (regXInv γ (repStart γ)) ∗
        clientInvs γ ∗ own_state γ (kvScan w8).init := by
  iintro #Hreg Hs
  -- the ghost names
  imod ghostVar_alloc (GF := GF) (∅ : GMap w64 (List w8)) with ⟨%γkv, Hkv⟩
  icases (ghostVar_split_half γkv 1 _).1 $$ Hkv with ⟨Hkv1, Hkv2⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := KvO) with ⟨%γf, Hf⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := ConnRole) with ⟨%γr, Hr⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := EscNames) with ⟨%γe, He⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := net.rpc.RpcConnNames) with ⟨%γw, Hw⟩
  imod net_alloc (GF := GF) nRep with ⟨%sent, %deliv, %dials, Hnet⟩
  imod fw_alloc (GF := GF) nRep with ⟨%cw, %rp, Hfwm⟩
  imod registry_alloc (GF := GF) with ⟨%mn, %ids, Hrg⟩
  imod sys_alloc (GF := GF) with ⟨%pn, Hsys⟩
  let γ : EpNames := ⟨γkv, γf, γr, γe, mn, ⟨ids, sent, deliv, dials, cw, rp⟩, pn⟩
  let W₀ : net.rpc.RpcWorld GF :=
    { SS := rpcSS γ, reg := γw, hs := fun _ => net.rpc.connectReq net.rpc.defaultRPCPath,
      hsAns := fun _ => net.rpc.connectAns }
  let W : net.rpc.RpcWorld GF := RA.httpW W₀
  ihave Hnet := Hnet $$ %γ
    %(⟨rfl, rfl, rfl⟩ : γ.rep.sent = sent ∧ γ.rep.deliv = deliv ∧ γ.rep.dials = dials)
  ihave Hfwm := Hfwm $$ %γ %(⟨rfl, rfl⟩ : γ.rep.cwriters = cw ∧ γ.rep.replies = rp)
  ihave ⟨HlU, HnT, HiT⟩ := Hrg $$ %γ %(⟨rfl, rfl⟩ : γ.master = mn ∧ γ.rep.ids = ids)
  ihave ⟨Hauth, Hfr⟩ := Hsys $$ %γ %(rfl : γ.proto = pn)
  -- the per-direction resources: one sent half to the invariant, the other with the delivery
  -- rights and the dial tokens to each replica's start
  ihave ⟨Hs1, Hnet⟩ := bigSepL2d_sep _ _ _ _ $$ Hnet
  ihave ⟨Hs2, Hnet⟩ := bigSepL2d_sep _ _ _ _ $$ Hnet
  ihave ⟨Hdl, Hdt⟩ := bigSepL2d_sep _ _ _ _ $$ Hnet
  ihave Hdl := bigSepL2d_comm _ _ _ $$ Hdl
  ihave Hfw := bigSepL2d_sep_2 _ _ _ _ $$ [Hs2 Hdl]
  · iframe Hs2 Hdl
  -- the abstract state's halves
  have hkv0 : kvOf (∅ : GMap w64 (List w8)) = (kvScan w8).init := by
    funext k; rfl
  ihave Hkvc : own_state γ (kvScan w8).init $$ [Hkv1]
  · unfold own_state kvHalf; iexists ∅; iframe Hkv1; ipureintro; exact hkv0
  ihave Hkvr : kvHalf γ (kvScan w8).init $$ [Hkv2]
  · unfold kvHalf; iexists ∅; iframe Hkv2; ipureintro; exact hkv0
  -- the protocol invariant
  ihave Hep := epInv_init γ $$ Hauth Hkvr [Hf] [Hs1]
  · unfold firedAuth; iexact Hf
  · iapply sentHalves_ep $$ Hs1
  imod inv_alloc protoN ⊤ (epInv γ) $$ [Hep] with #Hep
  · inext; iexact Hep
  -- the role registry
  imod inv_alloc roleN ⊤ (roleInv γ) $$ [Hr He] with #Hrole
  · inext
    unfold roleInv
    iexists ∅, ∅
    iframe Hr He
    isplitr
    · ipureintro; intro cid; simp
    iapply BigSepM.bigSepM_empty.2; iempintro
  -- the rpc world's connection registry
  imod inv_alloc net.rpc.regN' ⊤ (net.rpc.regInv W) $$ [Hw] with #HregW
  · inext
    unfold net.rpc.regInv
    rw [show W.reg = γw from RA.httpW_reg W₀]
    iexists ∅
    iframe Hw
    iapply BigSepM.bigSepM_empty.2; iempintro
  -- each replica's start resources, in the registration exchange
  rw [show nR = nRep from rfl]
  ihave Hrs := repStarts γ $$ Hfw Hdt Hfr Hfwm Hep
  ihave Hrs := BigSepL.bigSepL_sep_eqv.2 $$ [HiT Hrs]
  · iframe HiT Hrs
  imod regXInv_alloc γ (repStart γ) ⊤ $$ Hrs with #Hrx
  -- the replica addresses' protocols
  imod addrs_set_proto ⊤ (repDialP γ) (repAccP γ) replicaAddrs $$ Hreg Hs with #Hps
  imodintro
  iexists γ, W₀
  iframe HregW HlU HnT Hrx Hkvc
  isplitr
  · ipureintro; rfl
  unfold clientInvs
  iframe Hps Hrole

end ghost

/-! ## The machines' resources and the start -/

section rpc
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF] [π : NetProtoGS]
variable [RA : RpcHttpAddr GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The net/rpc over HTTP handshake's two parts at `DefaultRPCPath`. -/
abbrev hsReq : List w8 := connectReq defaultRPCPath
abbrev hsAns : List w8 := connectAns

/-- The master's machine (server 1): the right to fix the node list, its wildcard listener's rpc
protocols (`":7501"`), every replica's rpc address (it dials them), the rpc world's registry. -/
def masterRes (γ : EpNames) (W : net.rpc.RpcWorld GF) : IProp GF :=
  iprop(listUnset γ ∗ RA.rpcLisP W masterLis hsReq hsAns ∗
    ([∗list] k ∈ replicaNodes, RA.rpcAddrP W (rpcAddrOf k) hsReq hsAns) ∗
    inv net.rpc.regN' (net.rpc.regInv W))

/-- Replica node `k`'s machine (server `k`, 2..6): its node token, the registration exchange's
invariant, `clientInvs` (the replica addresses' protocols, the role registry), the master's rpc
address (it registers there), its own rpc listener's protocols (`rpcAddrOf k`), the rpc world's
registry. -/
def replicaRes (γ : EpNames) (W : net.rpc.RpcWorld GF) (k : Nat) : IProp GF :=
  iprop(nodeTok γ k ∗ inv regXN (regXInv γ (repStart γ)) ∗ clientInvs γ ∗
    RA.rpcAddrP W masterAddr hsReq hsAns ∗ RA.rpcLisP W (rpcAddrOf k) hsReq hsAns ∗
    inv net.rpc.regN' (net.rpc.regInv W))

/-- **The start**: from the registry, the replicas' peer and rpc addresses unset
(`epStartAddrs`) and the master's wildcard listener unset, the names `γ` and the rpc world `W`
(`W.SS = rpcSS γ`), the store's half of the initial abstract state (remote's
`RBase.sysState`), the master's machine's resources, each replica node's, and `clientInvs γ`
(persistent: each client machine's). -/
theorem ep_start :
    ⊢ regCtx (Gg := G) -∗ ([∗list] a ∈ epStartAddrs, addrUnset a) -∗
      lisUnset masterLis ={⊤}=∗
      ∃ (γ : EpNames) (W : net.rpc.RpcWorld GF), ⌜W.SS = rpcSS γ⌝ ∗
        own_state γ (kvScan w8).init ∗ masterRes γ W ∗
        ([∗list] k ∈ replicaNodes, replicaRes γ W k) ∗ □ clientInvs γ := by
  iintro #Hreg Hs Hml
  unfold epStartAddrs
  icases BigSepL.bigSepL_append.1 $$ Hs with ⟨Hp, Hr⟩
  imod ep_ghost_start $$ Hreg Hp with ⟨%γ, %W₀, %HW₀, #HregW, HlU, HnT, #Hrx, #Hci, Hown⟩
  -- the kit's world: `W₀` served over HTTP at `DefaultRPCPath` at every address
  have HW : (RA.httpW W₀).SS = rpcSS γ := (RA.httpW_SS W₀).trans HW₀
  have hhs : ∀ a, RA.worldHs (RA.httpW W₀) a = hsReq ∧ RA.worldHsAns (RA.httpW W₀) a = hsAns :=
    fun a => ⟨RA.httpW_hs W₀ a, RA.httpW_hsAns W₀ a⟩
  -- the master's wildcard listener
  imod RA.rpcLisP_set ⊤ (RA.httpW W₀) masterLis hsReq hsAns masterLis_ok (fun a _ => hhs a)
    $$ Hreg HregW Hml with #Hml
  ihave #Hma := RA.rpcLisP_addr (RA.httpW W₀) masterLis hsReq hsAns masterAddr masterAddr_ok
    masterLis_master $$ Hml
  -- each replica's rpc listener (an exact one)
  unfold replicaRpcAddrs
  rw [BigSepL.bigSepL_map]
  ihave Hr : [∗list] k ∈ replicaNodes,
      |={⊤}=> RA.rpcLisP (RA.httpW W₀) (rpcAddrOf k) hsReq hsAns $$ [Hr]
  · iapply BigSepL.bigSepL_impl $$ Hr
    iintro !> %j %k %hk Hu
    have hok : addrOk (rpcAddrOf k) = true :=
      replicaRpcAddrs_ok _ (rpcAddrOf_mem' k (List.mem_of_getElem? hk))
    ihave Hu := addrUnset_lisUnset (rpcAddrOf k) hok $$ Hu
    iapply RA.rpcLisP_set ⊤ (RA.httpW W₀) (rpcAddrOf k) hsReq hsAns (by simp [listenOk, hok])
      (fun a _ => hhs a) $$ Hreg HregW Hu
  imod BigSepL2.bigSepL_fupd ⊤ _ _ $$ Hr with #Hrl
  imodintro
  iexists γ, RA.httpW W₀
  isplitr
  · ipureintro; exact HW
  iframe Hown
  isplitl [HlU]
  · unfold masterRes
    iframe HlU Hml HregW
    iapply BigSepL.bigSepL_impl $$ Hrl
    iintro !> %j %k %hk #H
    have hok : addrOk (rpcAddrOf k) = true :=
      replicaRpcAddrs_ok _ (rpcAddrOf_mem' k (List.mem_of_getElem? hk))
    iapply RA.rpcLisP_addr (RA.httpW W₀) (rpcAddrOf k) hsReq hsAns (rpcAddrOf k) hok (Or.inl rfl) $$ H
  isplitl [HnT]
  · ihave Hall := BigSepL.bigSepL_sep_eqv.2 $$ [HnT Hrl]
    · iframe HnT Hrl
    iapply BigSepL.bigSepL_impl $$ Hall
    iintro !> %j %k %hk ⟨Hn, #H⟩
    unfold replicaRes
    iframe Hn Hrx Hci Hma H HregW
  · iexact Hci

end rpc

end github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet
end Perennial
