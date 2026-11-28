/-
The hraft kit's server machines' share of the deployment (notes/dsv-hraft.md, S5d; coordinator-E, #48
7233410712: the protocol per first-configuration size, the orchestrator's draw).

* `HK GF`: the deployment's ghost names: the draw `γc` (`Choice.lean`), raft's protocol `γs n` and
  the FSMs' frontier `fcs n` per size `n` (3 or 5), the rpc world `W`, and the servers' share
  tokens `sh`.
* `kitSS K`: the world's service specs at the servers' addresses: `RaftRPC` is the drawn protocol's
  `raftSvc` of the address's raft server (wrapped, `svcK`), `API` the drawn protocol's `apiSvc`
  (wrapped so a caller that does not know the draw can call: `svcKE`, coordinator-E's (e1)); nothing
  else.
* `srvPkg K n j`: what server `j` runs raft with in the protocol of size `n`: the protocol's
  invariant and `j`'s share of it (`gprot.alloc_init`'s), the frontier's invariant and its clients'
  law.
* `drawInv K`: the draw, once (`chosen γc n`), with every server's package of the drawn protocol,
  until the server takes it (its `shareTok`).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.ConfDefs
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.ApiSvc
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Trans
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.ServerDefs
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.service.FsmDefs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.hashicorp.raft.examples.hraftnet

open github_com.hashicorp.raft github_com.hashicorp.raft.gprot github_com.hashicorp.raft.proto
open rpctransport service

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The deployment's ghost names, for the server machines. -/
structure HK (GF : BundledGFunctors) where
  γc : GName
  γs : Nat → GNames
  fcs : Nat → FCtx GF
  W : net.rpc.RpcWorld GF
  sh : GName

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [package_sem : github_com.hashicorp.raft.Assumptions]

/-- The API's methods' argument bytes are encodings of their argument structs. -/
def apiArgsOk (M : GoString) (bs : List w8) : Prop :=
  (M = go!"Apply" → ∃ v, bs = encApplyArgs v) ∧ (M = go!"Read" → ∃ v, bs = encReadArgs v) ∧
  (M ∈ [go!"AddNonvoter", go!"AddVoter", go!"DemoteVoter", go!"LeadershipTransfer",
      go!"RemoveServer", go!"Snapshot", go!"Status"] → ∃ v, bs = encAdminArgs v)

/-- The API's service spec at the servers' addresses (`svcKE`: the drawn protocol's `apiSvc`). -/
def apiSvcK (K : HK GF) : net.rpc.MethodSpec GF :=
  svcKE K.γc apiArgsOk (fun n => apiSvc (K.γs n) (K.fcs n))

/-- The transport's service spec at server `j`'s address (`svcK`: the drawn protocol's `raftSvc`
of `j`'s raft address). -/
def raftSvcK (K : HK GF) (j : Nat) : net.rpc.MethodSpec GF :=
  svcK K.γc (fun n => raftSvc (K.γs n) (snapP (K.γs n) (K.fcs n)) (sidOf (W64 (j : Int))))

/-- **The world's services at the servers' addresses** (`ServerAddrs()[j-1]` is server `j`'s):
`RaftRPC` and `API`, nothing else; raw net/rpc (no handshake). -/
def kitSS (K : HK GF) : Prop :=
  ∀ (j : Nat) (svc : GoString), 1 ≤ j → j ≤ 6 →
    K.W.SS (serverAddrs.getD (j - 1) go!"") svc =
      (if svc = rpctransport.svcName then some (raftSvcK K j)
       else if svc = go!"API" then some (apiSvcK K) else none)

/-- The protocol of size `n`: the six servers, the first configuration `bootSrvs n`. -/
def γsOk (K : HK GF) : Prop :=
  ∀ n, N0Ok n → (K.γs n).srvs = allSids ∧ (K.γs n).g = genesisOf (bootSrvs n) ∧
    (K.γs n).cv = cfgDec allSids

/-- Server `j`'s share of the protocol `γ` (`gprot.alloc_init`'s). -/
def srvBundle (γ : GNames) (i : SID) : IProp GF :=
  iprop(isSrv γ i ∗ srvOwn γ i (initSrv γ.cv γ.g i) ∗ durView γ i (1 : Qp).half 0 ∗
    termCouple γ i (initSrv γ.cv γ.g i).term ∗ logCouple γ i (initSrv γ.cv γ.g i).log ∗
    cidxCouple γ i 0)

/-- What server `j` runs raft with in the protocol of size `n`. -/
def srvPkg (K : HK GF) (n j : Nat) : IProp GF :=
  iprop(Inv (K.γs n) ∗ srvBundle (K.γs n) (sidOf (W64 (j : Int))) ∗ frInv (K.γs n) (K.fcs n) ∗
    linStep (K.γs n) (K.fcs n))

/-- Server `j`'s right to take its package (exclusive; the start gives it to server `j`). -/
def shareTok (K : HK GF) (j : Nat) : IProp GF := ghostMapElem (K := Nat) (V := Unit) K.sh j (DFrac.own 1) ()

/-- The orchestrator's right to draw (exclusive; the start gives it to the orchestrator). -/
def drawTok (K : HK GF) : IProp GF := ghostMapElem (K := Nat) (V := Unit) K.sh 0 (DFrac.own 1) ()

def drawN : Namespace := nroot.@"hraft.draw"

/-- **The draw's invariant**: no draw yet, or the draw `n` (for good) with the orchestrator's token
and, per server, its package or its token (it took the package). -/
def drawInv (K : HK GF) : IProp GF :=
  inv drawN iprop(∃ m : GMap Nat Nat, ghostMapAuth K.γc 1 m ∗
    (⌜m = ∅⌝ ∨ ∃ n : Nat, ⌜m = (∅ : GMap Nat Nat).insert 0 n⌝ ∗ drawTok K ∗
      [∗list] j ∈ List.range' 1 6, (srvPkg K n j ∨ shareTok K j)))

instance drawInv_persistent (K : HK GF) : Persistent (drawInv K) := by
  unfold drawInv; infer_instance

/-- **Server `j`'s share of the deployment**: the configuration addresses' protocols, the world's
addresses and services, the draw's invariant and `j`'s token. -/
def srvShare (K : HK GF) (j : Nat) : IProp GF :=
  iprop(confProtos K.γc ∗ ([∗list] a ∈ serverAddrs, net.rpc.rpcAddr (Gg := hG.goose_globalGS) K.W a) ∗
    net.rpc.rpcLisP (Gg := hG.goose_globalGS) K.W (serverAddrs.getD (j - 1) go!"") [] [] ∗
    ⌜kitSS K ∧ γsOk K⌝ ∗ drawInv K ∗ shareTok K j)


/-- What net/rpc's first initialization leaves on a server machine: the codec unregistered
(`Register`'s premise), the server's package variables, `log`'s initialization (`Accept`'s). -/
def srvBoot : IProp GF :=
  iprop(sync.isMutex (globalAddr net.rpc.codecMu) (net.rpc.codecInv (GF := GF)) ∗ net.rpc.codecUnset ∗
    net.rpc.srvEnv ∗ isPkgInit (PROP := IProp GF) pkg_id.log)


/-! ## The world's specs accept the server's error answers (`errOk`, `Server.Accept`'s `srvServes`) -/

theorem answers_err (ok : List w8 → IProp GF) (Φ : List w8 → GoString → IProp GF) (msg : GoString)
    (h : msg ≠ []) : answers ok Φ ⊢ Φ [] msg := by
  unfold answers
  iintro ⟨-, H⟩
  iapply H $$ %msg
  ipureintro; exact h

theorem raftSvc_errOk (γ : GNames) (snapP : Nat → List w8 → IProp GF) (j : SID) :
    ⊢ net.rpc.errOk (raftSvc (GF := GF) γ snapP j) := by
  unfold net.rpc.errOk
  iintro !> %m %args %Φ %msg %Hmsg HS
  have hne := net.rpc.srvErrMsg_ne msg Hmsg
  unfold raftSvc
  by_cases h1 : m = go!"AppendEntries"
  · rw [if_pos h1]
    icases HS with ⟨%v, %snd, %T, %prev, %pt, %ents, %lci, %ss, -, -, HA⟩
    imodintro; iapply answers_err _ _ msg hne $$ HA
  rw [if_neg h1]
  by_cases h2 : m = go!"RequestVote"
  · rw [if_pos h2]
    icases HS with ⟨%v, %c, %T, %li, %lt, -, -, HA⟩
    imodintro; iapply answers_err _ _ msg hne $$ HA
  rw [if_neg h2]
  by_cases h3 : m = go!"RequestPreVote"
  · rw [if_pos h3]
    icases HS with ⟨%v, %c, %T, -, HA⟩
    imodintro; iapply answers_err _ _ msg hne $$ HA
  rw [if_neg h3]
  by_cases h4 : m = go!"InstallSnapshot"
  · rw [if_pos h4]
    icases HS with ⟨%v, %snd, %T, %s, %st, -, -, HA⟩
    imodintro; iapply answers_err _ _ msg hne $$ HA
  rw [if_neg h4]
  by_cases h5 : m = go!"TimeoutNow"
  · rw [if_pos h5]
    icases HS with ⟨%h, %c, -, HA⟩
    imodintro; iapply answers_err _ _ msg hne $$ HA
  rw [if_neg h5]
  icases HS with %HF
  exact HF.elim

theorem adminDep_err (W : AdminArgsV → IProp GF) (bs : List w8) (Φ : List w8 → GoString → IProp GF)
    (msg : GoString) (h : msg ≠ []) : adminDep W bs Φ ⊢ Φ [] msg := by
  unfold adminDep
  iintro ⟨%v, -, -, HA⟩
  iapply answers_err _ _ msg h $$ HA

theorem apiSvc_errOk (γ : GNames) (fc : FCtx GF) : ⊢ net.rpc.errOk (apiSvc (GF := GF) γ fc) := by
  unfold net.rpc.errOk
  iintro !> %m %args %Φ %msg %Hmsg HS
  have hne := net.rpc.srvErrMsg_ne msg Hmsg
  unfold apiSvc
  by_cases g0 : m = go!"Apply"
  · rw [if_pos g0]
    icases HS with ⟨%v, %n, -, -, HA⟩
    imodintro; iapply answers_err _ _ msg hne $$ HA
  rw [if_neg g0]
  by_cases g1 : m = go!"Read"
  · rw [if_pos g1]
    icases HS with ⟨%v, -, HA⟩
    imodintro; iapply answers_err _ _ msg hne $$ HA
  rw [if_neg g1]
  by_cases g2 : m = go!"AddVoter"
  · rw [if_pos g2]
    imodintro; iapply adminDep_err _ _ _ msg hne $$ HS
  rw [if_neg g2]
  by_cases g3 : m = go!"AddNonvoter"
  · rw [if_pos g3]
    imodintro; iapply adminDep_err _ _ _ msg hne $$ HS
  rw [if_neg g3]
  by_cases g4 : m = go!"DemoteVoter"
  · rw [if_pos g4]
    imodintro; iapply adminDep_err _ _ _ msg hne $$ HS
  rw [if_neg g4]
  by_cases g5 : m = go!"RemoveServer"
  · rw [if_pos g5]
    imodintro; iapply adminDep_err _ _ _ msg hne $$ HS
  rw [if_neg g5]
  by_cases g6 : m = go!"LeadershipTransfer"
  · rw [if_pos g6]
    imodintro; iapply adminDep_err _ _ _ msg hne $$ HS
  rw [if_neg g6]
  by_cases g7 : m = go!"Snapshot"
  · rw [if_pos g7]
    imodintro; iapply adminDep_err _ _ _ msg hne $$ HS
  rw [if_neg g7]
  by_cases g8 : m = go!"Status"
  · rw [if_pos g8]
    icases HS with ⟨%v, -, HA⟩
    imodintro; iapply answers_err _ _ msg hne $$ HA
  rw [if_neg g8]
  icases HS with %HF
  exact HF.elim

/-- The wrapped specs accept error answers, to who knows the draw. -/
theorem svcK_errOk (γc : GName) (Sn : Nat → net.rpc.MethodSpec GF) :
    □ (∀ m, net.rpc.errOk (Sn m)) ⊢ net.rpc.errOk (svcK γc Sn) := by
  iintro #H
  unfold net.rpc.errOk
  iintro !> %M %args %Φ %msg %Hmsg HS
  unfold svcK
  icases HS with ⟨%m, -, HS⟩
  ihave #Hm := H $$ %m
  iapply Hm $$ %M %args %Φ %msg %Hmsg HS

theorem svcKE_errOk (γc : GName) (ok : GoString → List w8 → Prop) (Sn : Nat → net.rpc.MethodSpec GF)
    (n : Nat) : chosen γc n ∗ net.rpc.errOk (Sn n) ⊢ net.rpc.errOk (svcKE γc ok Sn) := by
  iintro ⟨#Hc, #H⟩
  unfold net.rpc.errOk
  iintro !> %M %args %Φ %msg %Hmsg HS
  imod svcKE_elim γc ok Sn n M args Φ $$ [Hc HS] with HS
  · iframe Hc HS
  iapply H $$ %M %args %Φ %msg %Hmsg HS


/-! ## A server takes its package -/

theorem range6_get (j : Nat) (hj : 1 ≤ j ∧ j ≤ 6) : (List.range' 1 6)[j - 1]? = some j := by
  have : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem range6_set (j : Nat) (hj : 1 ≤ j ∧ j ≤ 6) : (List.range' 1 6).set (j - 1) j = List.range' 1 6 := by
  have : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- **Server `j`, knowing the draw `n`, takes its package of the drawn protocol** (a later credit:
the package is under the invariant's later). -/
theorem claim_pkg (K : HK GF) (n j : Nat) (hj : 1 ≤ j ∧ j ≤ 6) :
    £ 1 ∗ drawInv K ∗ chosen K.γc n ∗ shareTok K j ⊢ |={⊤}=> srvPkg K n j := by
  iintro ⟨Hlc, #Hinv, #Hc, Htok⟩
  unfold drawInv
  iinv Hinv with ⟨%m, >Ha, Hcase⟩ Hclose
  imod lc_fupd_elim_later $$ Hlc Hcase with Hcase
  unfold chosen
  ihave %Hl := ghost_map_lookup $$ Ha Hc
  icases Hcase with (%Hm | ⟨%n', %Hm, Hd, Hlist⟩)
  · subst Hm
    exfalso
    simp at Hl
  subst Hm
  have hn : n' = n := by
    have := Hl
    rw [show ((∅ : GMap Nat Nat).insert 0 n').lookup 0 = some n' from lookup_insert _ _ _] at this
    exact Option.some.inj this
  subst hn
  ihave ⟨Hj, Hrest⟩ := (BigSepL.bigSepL_lookup_acc (range6_get j hj)).1 $$ Hlist
  icases Hj with (Hp | Ht)
  · imod Hclose $$ [Ha Hd Hrest Htok] with -
    · inext
      iexists _
      iframe Ha
      iright
      iexists n'
      iframe Hd
      isplitr; · ipureintro; rfl
      ihave H := Hrest $$ %j [Htok]
      · iright; iexact Htok
      rw [range6_set j hj]
      iexact H
    imodintro
    iexact Hp
  · unfold shareTok
    ihave %hv := ghostMapElem_valid_2 _ _ _ _ _ _ $$ Ht Htok
    exfalso
    have := DFrac.valid_op_own hv.1
    simp at this

end defs

end github_com.hashicorp.raft.examples.hraftnet

end Perennial
