/-
# The gryff kit's servers (`kit.go`'s `Server`, `serve`)

`Server(id)` runs `serve(id, ServerAddrs())`: server id 1 is the master (`masterlib.NewMaster`,
then `Serve`), ids 2..4 the replicas (`serverlib.RegisterWithMaster`, `gryff.NewReplica`,
`rpc.Register`, `serverlib.Serve` on the port 1000 above). `Server.spec`'s precondition is what a
server machine's boot hands its `main`: its share of the start (`serverShare`), the packages
initialized, net/http's and net/rpc's per-machine boot resources (`serverBoot`, from their first
initializations, through `cmd/server*/Boot.lean`), the bounds, the main thread's token (on which
net/http's `Serve` runs), and for a replica the gryff package's owned variables and
trace prophecy (`gryffGlobals ∗ bootProph`, `cmd/server{2,3,4}/Boot.lean`'s `wp_initialize'_own`).
Its postcondition is `True`: the master's and a replica's `Serve` return on a listener error.
The pieces are `Server/SpecsReq.lean`'s (`NewMaster.wp_req`, `Master.Serve.wp_req`,
`RegisterWithMaster.wp_req`, `Serve.wp_req`), `B/NewReplica.lean`'s `NewReplica_core`,
`B/Register.lean`'s `wp_Register_replica`, `Server/MasterBoot.lean`'s `wp_kit_Register`, and the
boot's D13 steps (`node_proph_intro`, `replica_ready_intro`). Net's and the codec's specs are
premises (linked at the top).
-/
module

public import Dsverify.Proof.gryff.B.NewReplica
public import Dsverify.Proof.gryff.B.Register
public import Dsverify.Proof.gryff.Server.SpecsReq
public import Dsverify.Proof.gryff.Server.RpcEnv
public import Dsverify.Proof.gryff.Client.Defs
public import Dsverify.Proof.gryff.examples.gryffnet.ServerSpec

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace gryff.examples.gryffnet

open Perennial.gryff Perennial.gryff.unitB
open gryff.boot (gryffGlobals bootProph)

/-! ## `atoi` -/

/-- The decimal value of a string of digits. -/
def decVal (s : List w8) : Nat := s.foldl (fun n c => n * 10 + (uint.nat c - 48)) 0

/-- A decimal digit's byte. -/
def isDigit (c : w8) : Prop := 48 ≤ uint.nat c ∧ uint.nat c ≤ 57

theorem decVal_snoc (s : List w8) (c : w8) :
    decVal (s ++ [c]) = decVal s * 10 + (uint.nat c - 48) := by
  unfold decVal; simp [List.foldl_append]

theorem foldl_dec_lt (s : List w8) (h : ∀ c ∈ s, isDigit c) (a : Nat) :
    s.foldl (fun n c => n * 10 + (uint.nat c - 48)) a < (a + 1) * 10 ^ s.length := by
  induction s generalizing a with
  | nil => simp
  | cons c s ih =>
    simp only [List.foldl_cons, List.length_cons]
    have hc := h c (by simp)
    unfold isDigit at hc
    have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) (a * 10 + (uint.nat c - 48))
    calc _ < (a * 10 + (uint.nat c - 48) + 1) * 10 ^ s.length := this
      _ ≤ (a + 1) * 10 * 10 ^ s.length := Nat.mul_le_mul_right _ (by omega)
      _ = (a + 1) * 10 ^ (s.length + 1) := by rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 10]

theorem decVal_lt (s : List w8) (h : ∀ c ∈ s, isDigit c) : decVal s < 10 ^ s.length := by
  have := foldl_dec_lt s h 0
  unfold decVal; simpa using this

section atoi
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : gryff.examples.gryffnet.Assumptions]

set_option goose.wp.extras true

/-- `atoi(s)` on a string of at most 4 digits: its decimal value. -/
theorem wp_atoi (s : GoString) (hd : ∀ c ∈ s, isDigit c) (hl : s.length ≤ 4) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet }}
      (App (Val (@! gryff.examples.gryffnet.atoi)) (Val #s))
    {{ RET #(W64 (decVal s)); True }} := by
  wp_start as -
  wp_auto
  ihave IH : iprop(∃ j : Nat, "i" ∷ i_ptr ↦ W64 j ∗ "n" ∷ n_ptr ↦ W64 (decVal (s.take j)) ∗
      ⌜j ≤ s.length⌝) $$ [i n]
  · iexists 0; iframe; ipureintro; simp
  wp_for IH
  icases IH with %Hj
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
  have hjs : (j : Int) < 2 ^ 63 := by omega
  by_cases hlt : j < s.length
  · have hlt' : sint.Z (W64 (j : Int)) < sint.Z (W64 (s.length : Int)) := by word
    simp only [hlt', decide_true, ↓reduceIte]
    try wp_auto
    have hjn : sint.nat (W64 (j : Int)) = j := by word
    rw [if_pos (by word), hjn, List.getElem?_eq_getElem hlt]
    try wp_auto
    have hc := hd s[j] (List.getElem_mem hlt)
    unfold isDigit at hc
    have hc8 := s[j].isLt
    have h0 : sint.Z (W64 0) ≤ sint.Z (W64 (uint.Z s[j]) - W64 48) := by
      simp only [uint.nat] at hc; word
    have h9 : sint.Z (W64 (uint.Z s[j]) - W64 48) ≤ sint.Z (W64 9) := by
      simp only [uint.nat] at hc; word
    simp only [h0, h9, decide_true, ↓reduceIte]
    try wp_auto
    simp only [h9, decide_true, ↓reduceIte]
    try wp_auto
    wp_for_post
    iframe
    iexists j + 1
    have htk : List.take (j + 1) s = List.take j s ++ [s[j]] := by
      rw [List.take_succ, List.getElem?_eq_getElem hlt]; rfl
    have hdl := decVal_lt (List.take j s) (fun c hc' => hd c (List.mem_of_mem_take hc'))
    have hlj : (List.take j s).length = j := by simp; omega
    rw [hlj] at hdl
    have hp : 10 ^ j ≤ 10 ^ 4 := Nat.pow_le_pow_right (by decide) (by omega)
    have hv : W64 (↑(decVal (List.take j s))) * W64 10 + (W64 (uint.Z s[j]) - W64 48) =
        W64 (↑(decVal (List.take (j + 1) s))) := by
      rw [htk, decVal_snoc]
      simp only [uint.nat] at hc ⊢
      have : (10 : Nat) ^ 4 = 10000 := by decide
      word
    rw [hv, show W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) by word]
    iframe
    ipureintro; omega
  · have hge : ¬ sint.Z (W64 (j : Int)) < sint.Z (W64 (s.length : Int)) := by word
    have hj : j = s.length := by omega
    subst hj
    have hft : (#false : val) ≠ #true := fun h => Bool.noConfusion (go.intoVal_inj h)
    simp only [hge, decide_false, hft, decide_true, Bool.false_eq_true, ↓reduceIte]
    try wp_auto
    rw [List.take_length]
    iapply HΦ; itrivial

end atoi

/-! ## `serve` -/

/-- Replica node `k`'s port as a string. -/
def portStr (k : Nat) : GoString := [go!"7502", go!"7503", go!"7504"].getD k go!""

theorem serve_addr_facts (k : Nat) (hk : k < 3) :
    serverAddrs[k + 1]? = some (portAddr k) ∧
    strings.split (portAddr k) go!":" = [ipOf k, portStr k] ∧
    (∀ c ∈ portStr k, isDigit c) ∧ (portStr k).length ≤ 4 ∧ decVal (portStr k) = 7502 + k := by
  rcases k with _ | _ | _ | k
  all_goals first
    | omega
    | (refine ⟨rfl, ?_, ?_, by decide, by decide⟩
       · simp [strings.split, strings.splitAux, portAddr, ipOf, portStr]
       · intro c hc; simp [portStr] at hc
         rcases hc with rfl | rfl | rfl | rfl <;> (unfold isDigit; decide))

theorem master_addr_facts :
    serverAddrs[0]? = some go!"127.0.0.1:7501" ∧
    strings.split go!"127.0.0.1:7501" go!":" = [go!"127.0.0.1", go!"7501"] ∧
    (∀ c ∈ go!"7501", isDigit c) ∧ (go!"7501").length ≤ 4 ∧ decVal go!"7501" = 7501 := by
  refine ⟨rfl, ?_, ?_, by decide, by decide⟩
  · simp [strings.split, strings.splitAux]
  · intro c hc; simp at hc
    rcases hc with rfl | rfl | rfl | rfl <;> (unfold isDigit; decide)

section serve
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [binA : wire.BinaryVarintHyps GF]
variable [strconvA : strconv.Assumptions]
variable [io.Assumptions] [net.Assumptions] [netN.NetSpecs GF]
variable [strA : netN.StringsIndexHyp GF] [mathA : lib.MathPowHyp GF]
variable [net.rpc.Assumptions] [RA : RpcHttpAddr GF] [net.http.Assumptions] [randA : lib.RandSeedHyp GF]
variable [mA : gryff.src.masterlib.Assumptions] [sA : gryff.src.serverlib.Assumptions]
variable (wp_rfl : lib.io.ReadFull.specLt (GF := GF) (hG := hG))
variable (L : CodecLaws (GF := GF)) (RL : RcvLaws (GF := GF))
variable (wp_Call : net.rpc.Client.Call.spec (GF := GF) (hG := hG))
variable (wp_DialHTTP : net.rpc.DialHTTP.spec (GF := GF) (hG := hG))
variable (wp_SetCodec : net.rpc.SetCodec.spec (GF := GF) (hG := hG))
variable (wp_run : unitB.Replica.run.spec (GF := GF) (hG := hG))
variable (wp_Register : net.rpc.Register.spec_fresh (GF := GF) (hG := hG))
variable (wp_NewServer : net.rpc.NewServer.spec_owned (GF := GF) (hG := hG))
variable (wp_SRegister : net.rpc.Server.Register.spec_fresh (GF := GF) (hG := hG))
variable (wp_SHandleHTTP : net.rpc.Server.HandleHTTP.spec (GF := GF) (hG := hG))
variable (wp_HandleHTTP : net.rpc.HandleHTTP.spec (GF := GF) (hG := hG))
variable (wp_Serve : net.http.Serve.spec_rpc (GF := GF) (hG := hG))

set_option goose.wp.extras true

/-- What every server machine's `serve` starts from, besides its share: the packages, net/rpc's
boot resource, the bounds, `ServerAddrs()`'s slice. -/
def serveEnv (addrs : GoSlice) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗
    serverBoot (GF := GF) ∗
    ⌜threadBound GF ≤ 2 ^ 31 ∧ receiptBound GF ≤ 2 ^ 64⌝ ∗ addrs ↦* serverAddrs)

include wp_rfl L RL wp_Call wp_DialHTTP wp_SetCodec wp_run wp_Register wp_HandleHTTP wp_Serve in
/-- `serve(k + 2, addrs)`: replica node `k`. -/
theorem wp_serve_replica (γ : GryffNames GF) (k : Nat) (hk : k < 3) (addrs : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet ∗ serveEnv addrs ∗
        serverShare γ (k + 1) ∗ gryffGlobals ∗ bootProph ∗ threadTok }}
      (App (App (Val (@! gryff.examples.gryffnet.serve)) (Val #(W64 ((k + 2 : Nat) : Int))))
        (Val #addrs))
    {{ RET #(); True }} := by
  wp_start as ⟨Henv, Hsh, Hglob, Hbp, Htok⟩
  iunfold serveEnv at Henv
  icases Henv with ⟨#Hrpc, #Hhttp, Hboot, %Hb, Haddrs⟩
  unfold serverBoot httpInitRes rpcInitRes
  icases Hboot with ⟨⟨Hmux, #Hhe⟩, ⟨Hboot, ⟨%γs, %γf, #Hds, Hsown⟩, #Hce, #Hcon⟩⟩
  unfold rpcBootRes
  icases Hboot with ⟨#Hsync, #Hmu, Hun, #Hinvreq⟩
  ihave #Hde : dialEnv (GF := GF) $$ []
  · ihave #Hhe0 := Hhe
    iunfold net.http.httpSrvEnv at Hhe0
    icases Hhe0 with ⟨#Hhe1, -⟩
    unfold dialEnv; iframe #; ipureintro; exact Hb.2
  wp_auto
  wp_apply (wp_kit_Register wp_SetCodec) $$ [Hun] as #Hcs
  · unfold rpcBootRes
    iframe; iframe #
  try wp_auto
  obtain ⟨hA, hS, hD, hL, hV⟩ := serve_addr_facts k hk
  ihave %Hal := ownSlice_len _ _ _ $$ Haddrs
  have hidx : sint.Z (W64 ((k + 2 : Nat) : Int) - W64 1) = ((k + 1 : Nat) : Int) := by word
  have hlen : sint.Z addrs.len = 4 := by
    have : serverAddrs.length = 4 := rfl
    rw [this] at Hal; word
  rw [hidx, if_pos (by rw [hlen]; omega)]
  icases ownSlice_elem_acc ((k + 1 : Nat) : Int) _ _ _ _ (by omega) (by simpa using hA) $$ Haddrs
    with ⟨He, Hback⟩
  wp_auto
  wp_apply strings.wp_Split _ _ (by decide) as %spl ⟨Hspl, -⟩
  rw [hS]
  ihave Haddrs := Hback $$ %_ He
  have hset : serverAddrs.set (((k + 1 : Nat) : Int)).toNat (portAddr k) = serverAddrs := by
    rcases k with _ | _ | _ | k <;> first | rfl | omega
  rw [hset]
  ihave %Hsl := ownSlice_len _ _ _ $$ Hspl
  have hslen : sint.Z spl.len = 2 := by simp at Hsl; word
  rw [if_pos (by rw [hslen]; decide)]
  icases ownSlice_elem_acc (sint.Z (W64 1)) (portStr k) _ _ _ (by decide) (by rfl) $$ Hspl
    with ⟨He1, Hback1⟩
  wp_auto
  wp_apply (wp_atoi (portStr k) hD hL)
  ihave Hspl := Hback1 $$ %_ He1
  rw [hV]
  have hsp : [ipOf k, portStr k].set (sint.Z (W64 1)).toNat (portStr k) = [ipOf k, portStr k] := rfl
  rw [hsp]
  have hid1 : W64 ((k + 2 : Nat) : Int) ≠ W64 1 := by word
  simp only [hid1, decide_false]
  try wp_auto
  -- the node's prediction (D13), then `RegisterWithMaster`
  unfold serverShare
  simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
  icases Hsh with ⟨#Hns, #Hinvs, Hstart, Hbres⟩
  unfold replicaBootRes
  icases Hbres with ⟨Hpt, Hclaim⟩
  ihave #Hpi := sharedInvs_proto γ $$ Hinvs
  iunfold protoInvs at Hpi
  icases Hpi with ⟨#Hg, -⟩
  unfold bootProph
  icases Hbp with ⟨%p, %pvs, Htp, Hpr⟩
  iapply fupd_wp
  imod node_proph_intro γ k p pvs $$ [Hpt Htp Hpr] with ⟨Hnp, %ws, #Hws⟩
  · iframe; iframe #
  imodintro
  unfold replicaStartRes deployRegResDef
  icases Hstart with ⟨#Hdep, %Hw⟩
  icases ownSlice_elem_acc (sint.Z (W64 0)) (ipOf k) _ _ _ (by decide) (by rfl) $$ Hspl
    with ⟨Hh0, -⟩
  icases ownSlice_elem_acc (sint.Z (W64 0)) go!"127.0.0.1:7501" _ _ _ (by decide) (by rfl) $$ Haddrs
    with ⟨Ha0, -⟩
  rw [if_pos (by rw [hslen]; decide)]
  wp_auto
  ihave #Hsrv : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.serverlib $$ []
  · iPkgInit
  rw [if_pos (by rw [hlen]; decide)]
  wp_auto
  have hpn : W64 (((7502 + k : Nat)) : Int) = portNum k := by unfold portNum; congr 1
  have hma : (go!"127.0.0.1:7501" : GoString) = masterRpcAddr := rfl
  rw [hpn, hma]
  ihave Hrr : replicaRegRes γ k $$ []
  · unfold replicaRegRes deployRegResDef; iframe #; ipureintro; exact Hw
  wp_apply (RegisterWithMaster.wp_req L wp_Call wp_DialHTTP γ k ws hk) $$ [Hrr]
    as %id %nsl %nodes ⟨Hnsl, #Hras⟩
  · iframe; iframe #
  iapply fupd_wp
  imod replica_ready_intro γ k id nodes $$ [Hclaim Hnp] with Hready
  · iframe; iframe #
  imodintro
  ihave #Hgry : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff $$ []
  · iPkgInit
  ihave #Hrl : □ ([∗list] j ∈ [0, 1, 2], replicaLis γ j) $$ []
  · unfold netShare; icases Hns with ⟨#H, -⟩; imodintro; iexact H
  wp_apply (NewReplica_core wp_rfl wp_run L RL γ k id nsl nodes hk) $$ [Hnsl Hready Hglob]
    as %rep ⟨Hrok, %ρ, %kr, %Hkr, Hisr⟩
  · iframe; iframe #
  wp_apply (wp_Register_replica wp_Register γ γs γf rep) $$ [Hrok Hsown] as %err Hr
  · iframe; iframe #
  icases Hr with (⟨%He, #Hsreg⟩ | %He)
  · subst He
    wp_auto
    ihave #Hse : net.rpc.srvEnv (GF := GF) $$ []
    · unfold net.rpc.srvEnv; iframe #
    ihave Hrr2 : replicaRegRes γ k $$ []
    · unfold replicaRegRes deployRegResDef; iframe #; ipureintro; exact Hw
    have hport : sint.Z (portNum k + W64 1000) = 8502 + k := by unfold portNum; word
    ihave #Hdsa := net.rpc.defaultServerO_any γs γf $$ Hds
    wp_apply (Serve.wp_req wp_HandleHTTP wp_Serve γ k (portNum k + W64 1000) γs hk hport)
        $$ [Hmux Hrr2 Htok]
    · iframe; iframe #
      ipureintro; exact Hb.1
    iapply HΦ; itrivial
  · rcases err with _ | _
    · wp_auto
      iapply HΦ; itrivial
    · exact absurd rfl He

include L RL wp_Call wp_DialHTTP wp_SetCodec wp_NewServer wp_SRegister wp_SHandleHTTP wp_Serve in
/-- `serve(1, addrs)`: the master. -/
theorem wp_serve_master (γ : GryffNames GF) (addrs : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet ∗ serveEnv addrs ∗
        serverShare γ 0 ∗ threadTok }}
      (App (App (Val (@! gryff.examples.gryffnet.serve)) (Val #(W64 1))) (Val #addrs))
    {{ RET #(); True }} := by
  wp_start as ⟨Henv, Hsh, Htok⟩
  iunfold serveEnv at Henv
  icases Henv with ⟨#Hrpc, #Hhttp, Hboot, %Hb, Haddrs⟩
  unfold serverBoot httpInitRes rpcInitRes
  icases Hboot with ⟨⟨Hmux, #Hhe⟩, ⟨Hboot, -, #Hce, #Hcon⟩⟩
  unfold rpcBootRes
  icases Hboot with ⟨#Hsync, #Hmu, Hun, #Hinvreq⟩
  ihave #Hde : dialEnv (GF := GF) $$ []
  · ihave #Hhe0 := Hhe
    iunfold net.http.httpSrvEnv at Hhe0
    icases Hhe0 with ⟨#Hhe1, -⟩
    unfold dialEnv; iframe #; ipureintro; exact Hb.2
  wp_auto
  wp_apply (wp_kit_Register wp_SetCodec) $$ [Hun] as #Hcs
  · unfold rpcBootRes
    iframe; iframe #
  try wp_auto
  obtain ⟨hA, hS, hD, hL, hV⟩ := master_addr_facts
  ihave %Hal := ownSlice_len _ _ _ $$ Haddrs
  have hlen : sint.Z addrs.len = 4 := by
    have : serverAddrs.length = 4 := rfl
    rw [this] at Hal; word
  rw [if_pos (by rw [hlen]; decide)]
  icases ownSlice_elem_acc (sint.Z (W64 1 - W64 1)) _ _ _ _ (by decide) hA $$ Haddrs
    with ⟨He, -⟩
  wp_auto
  wp_apply strings.wp_Split _ _ (by decide) as %spl ⟨Hspl, -⟩
  rw [hS]
  ihave %Hsl := ownSlice_len _ _ _ $$ Hspl
  have hslen : sint.Z spl.len = 2 := by simp at Hsl; word
  rw [if_pos (by rw [hslen]; decide)]
  icases ownSlice_elem_acc (sint.Z (W64 1)) go!"7501" _ _ _ (by decide) (by rfl) $$ Hspl
    with ⟨He1, -⟩
  wp_auto
  wp_apply (wp_atoi go!"7501" hD hL)
  rw [hV]
  rw [show ((7501 : Nat) : Int) = 7501 from rfl]
  unfold serverShare
  simp only [↓reduceIte]
  icases Hsh with ⟨#Hns, #Hinvs, Hstart⟩
  ihave #Hse : net.rpc.srvEnv (GF := GF) $$ []
  · unfold net.rpc.srvEnv; iframe #
  ihave #Hml : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.masterlib $$ []
  · iPkgInit
  wp_apply (NewMaster.wp_req L RL wp_Call wp_DialHTTP wp_NewServer wp_SRegister wp_SHandleHTTP γ)
      $$ [Hstart Hmux] as %m Hm
  · iframe; iframe #
    ipureintro; exact Hb.1
  try wp_auto
  wp_apply (Master.Serve.wp_req wp_Serve γ m) $$ [Hm Htok]
  · iframe
  try wp_auto
  iapply HΦ; itrivial

/-- `ServerAddrs()` returns a new slice of the server machines' addresses (`KitProof`'s
`wp_ServerAddrs`, without its remote section variables). -/
theorem wp_ServerAddrs' :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet }}
      (App (Val (@! gryff.examples.gryffnet.ServerAddrs)) (Val #()))
    {{ (sl : GoSlice), RET #sl; sl ↦* serverAddrs }} := by
  wp_start as -
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.string))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoString) (t := go.string) serverAddrs
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  iapply HΦ
  iexact Hsl

include wp_rfl L RL wp_Call wp_DialHTTP wp_SetCodec wp_run wp_Register wp_NewServer wp_SRegister
  wp_SHandleHTTP wp_HandleHTTP wp_Serve in
theorem Server.wp_proof : Server.spec (GF := GF) (hG := hG) := by
  intro γ i hi
  wp_start as ⟨Hboot, %Hb, Hsh, Hx, Htok⟩
  wp_auto
  wp_apply wp_ServerAddrs' as %sl Hsl
  rcases i with _ | k
  · wp_apply (wp_serve_master L RL wp_Call wp_DialHTTP wp_SetCodec wp_NewServer wp_SRegister
        wp_SHandleHTTP wp_Serve γ sl) $$ [Hboot Hsl Hsh Htok]
    · unfold serveEnv; iframe; iframe Hpkg2 Hpkg3; ipureintro; exact Hb
    try wp_auto
    iapply HΦ; itrivial
  · simp only [Nat.add_one_ne_zero, ↓reduceIte]
    icases Hx with ⟨Hglob, Hbp⟩
    wp_apply (wp_serve_replica wp_rfl L RL wp_Call wp_DialHTTP wp_SetCodec wp_run wp_Register
        wp_HandleHTTP wp_Serve γ k (by omega) sl) $$ [Hboot Hsl Hsh Hglob Hbp Htok]
    · unfold serveEnv; iframe; iframe Hpkg2 Hpkg3; ipureintro; exact Hb
    try wp_auto
    iapply HΦ; itrivial

end serve

end gryff.examples.gryffnet

end Perennial
