/-
The craq kit's specs (kit.go's `Client`, `Orch`, `Server`, and the `awaitConf`/`configure` specs
their proofs take), the vocabulary they share (`cfgKit`, the machine's fresh codec registry
`codecFresh`, the store's inputs' and outputs' `Pos.Countable`), and `Register()`'s proof
(`wp_Register`). A defs module: `ClientProof.lean` and `ServerProof.lean` prove the specs,
`Mains.lean` and the top level use them.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.KitDefs
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.ConfProof
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Specs
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Netrpc.New
public import Net.Spec.net.rpc.SetCodec
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Netrpc.Bindings
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.Check
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.ServeClient
public import Perennial.Golang.Theory.Chan.Idioms.Bag

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

namespace github_com.despreston.go_craq.examples.craqnet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote
open github_com.despreston.go_craq github_com.despreston.go_craq.netrpcP

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- An input's code. -/
def kinCode (i : KIn) : Bool × GoString × GoString :=
  match i with
  | ⟨.get k, _⟩ => (false, k, [])
  | ⟨.put k x, _⟩ => (true, k, x)

/-- The store's inputs' `Pos.Countable` (remote's slots keep them in ghost state). -/
instance KIn_countable : Pos.Countable KIn :=
  .ofInjective (fun i => Pos.Countable.encode (kinCode i)) (fun a b h => by
    have h := Pos.encode_inj h
    obtain ⟨a | ⟨a1, a2⟩, ha⟩ := a <;> obtain ⟨b | ⟨b1, b2⟩, hb⟩ := b <;>
      simp only [kinCode, Prod.mk.injEq] at h
    · obtain ⟨-, rfl, -⟩ := h; rfl
    · exact absurd h.1 (by decide)
    · exact absurd h.1 (by decide)
    · obtain ⟨-, rfl, rfl⟩ := h; rfl)

/-- An output's code. -/
def koutCode : KOut → Option (Option GoString)
  | .got v => some (v.map Subtype.val)
  | .bad => none

/-- The store's outputs' `Pos.Countable`. -/
instance KOut_countable : Pos.Countable KOut :=
  .ofInjective (fun o => Pos.Countable.encode (koutCode o)) (fun a b h => by
    have h := Pos.encode_inj h
    rcases a with (_ | ⟨a, ha⟩) | _ <;> rcases b with (_ | ⟨b, hb⟩) | _ <;>
      simp_all [koutCode])

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.despreston.go_craq.examples.craqnet.Assumptions]
variable [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions]
variable [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [ra : RpcHttpAddr GF] [bvi : go.BasicIntoValInj]

local notation "kpkg" => pkg_id.github_com.despreston.go_craq.examples.craqnet

set_option goose.wp.extras true


/-- The run's configuration as the kit deploys it: the coordinator at `ServerAddrs()[0]`, the chain
all of the others. -/
def cfgKit (cfg : Cfg GF) : Prop := cfg.cAddr = serverAddrs.headD [] ∧ cfg.chain = serverAddrs.tail


/-- Chain machines' addresses: `ServerAddrs()[j]`, `1 ≤ j ≤ 5`, is in the chain. -/
theorem serverAddrs_chain (j : Nat) (h1 : 1 ≤ j) (h5 : j ≤ 5) :
    ∃ a, serverAddrs[j]? = some a ∧ a ∈ serverAddrs.tail := by
  have hj : j < serverAddrs.length := by simp only [serverAddrs, List.length_cons, List.length_nil]; omega
  refine ⟨serverAddrs[j], List.getElem?_eq_getElem hj, ?_⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have := List.getElem_mem (l := serverAddrs.tail) (n := j')
    (by simp [serverAddrs]; omega)
  simpa [List.getElem_tail] using this

/-- A machine's codec registry at its initial state (net/rpc's initialization's; open point). -/
def codecFresh : IProp GF :=
  iprop(sync.isMutex (globalAddr net.rpc.codecMu) net.rpc.codecInv ∗ net.rpc.codecUnset)

/-- `Register()`: the kit's codec registered. -/
theorem wp_Register (wp_SetCodec : net.rpc.SetCodec.spec (GF := GF) (hG := hG)) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ codecFresh }}
      (App (Val (@! github_com.despreston.go_craq.examples.craqnet.Register)) (Val #()))
    {{ RET #(); net.rpc.codecSet craqCodec }} := by
  unfold codecFresh
  wp_start as ⟨#Hmu, Hun⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ «$a0»
  ipersist «$a0»
  wp_apply wp_SetCodec craqCodec _ $$ [Hun]
  · isplitr
    · iexact Hmu
    isplitl [Hun]
    · iexact Hun
    isplitr
    · unfold net.rpc.codecIs
      iexists _
      iframe «$a0»
      isplitr
      · iapply craqCodec_encOk
      isplitr
      · iapply craqCodec_decOk
      · iapply craqCodec_rcvOk
    · ipureintro; exact Hnn
  iintro #Hcs
  wp_auto
  iapply HΦ
  iexact Hcs

/-- `awaitConf(a, ch)`'s spec (ConfProof.lean's `wp_awaitConf`, there from the net specs). -/
abbrev awaitConf.spec : Prop :=
  ∀ (a : GoString) (γch : ChanNames) (ch : Loc),
    {{ isPkgInit (PROP := IProp GF) kpkg ∗
        addrProto (Gg := hG.goose_globalGS) a confProto confProto ∗
        isChanBag γch ch (V := msg) (msgOk (hG := hG)) }}
      (App (App (Val (@! github_com.despreston.go_craq.examples.craqnet.awaitConf)) (Val #a))
        (Val #ch))
    {{ RET #(); False }}


/-- `configure(conf, rs)`'s spec (ConfProof.lean's `wp_configure`, there from the net specs). -/
abbrev configure.spec : Prop :=
  ∀ (conf : Conf) (rs : GoSlice) (rl : List removal) (dq : DFrac),
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ rs ↦*{dq} rl ∗ ⌜confOk conf ∧ rl.length ≤ 2⌝ ∗
        [∗list] a ∈ confAddrs, addrProto (Gg := hG.goose_globalGS) a confProto confProto }}
      (App (App (Val (@! github_com.despreston.go_craq.examples.craqnet.configure)) (Val #conf))
        (Val #rs))
    {{ RET #(); rs ↦*{dq} rl }}


/-- `Client(c)`: client machine `c` (`cfgKit`: the coordinator at `ServerAddrs()[0]`, the chain
the others); it never returns. Its machine's codec registry is fresh (`codecFresh`). -/
abbrev Client.spec [RemoteGS] : Prop :=
  ∀ (cfg : Cfg GF) (c : w64), cfgKit cfg → uint.nat c < 5 →
  {{ isPkgInit (PROP := IProp GF) kpkg ∗ craqCtx cfg ∗ codecFresh ∗
      addrProto (Gg := hG.goose_globalGS) (confAddrs.getD (uint.nat c) []) confProto confProto ∗
      remoteAddr (Gg := hG.goose_globalGS) (kvR cfg.γ) (clientAddrs.getD (uint.nat c) []) ∗
      mapCtx (Gg := hG.goose_globalGS) (I := KIn) }}
    (App (Val (@! github_com.despreston.go_craq.examples.craqnet.Client)) (Val #c))
  {{ RET #(); False }}


/-- `Orch()`: the orchestrator; it returns (porcupine accepts the history). -/
abbrev Orch.spec [RemoteGS] : Prop :=
  ∀ (γ : CraqNames) (γp : PendNames), receiptBound GF ≤ 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) kpkg ∗
      ([∗list] a ∈ clientAddrs, remoteAddr (Gg := hG.goose_globalGS) (kvR γ) a) ∗
      mapCtx (Gg := hG.goose_globalGS) (I := KIn) ∗
      pendCtx (Gg := hG.goose_globalGS) (kvR γ) (kvS0 (GF := GF)) γp ∗
      pendLib (Gg := hG.goose_globalGS) (kvS0 (GF := GF)) γp (kvS0 (GF := GF)).M.init ∗
      ([∗list] a ∈ confAddrs, addrProto (Gg := hG.goose_globalGS) a confProto confProto) ∗
      [∗list] a ∈ clientAddrs, budUnits (Gg := hG.goose_globalGS) a 18 }}
    (App (Val (@! github_com.despreston.go_craq.examples.craqnet.Orch)) (Val #()))
  {{ RET #(); True }}


/-- Server machine `id`'s resources: the coordinator's (`id = 1`), or chain machine `id`'s (at
`ServerAddrs()[id-1]`: its node's resources and join ticket, and its configuration address
`ConfAddrs()[NC+id-1]`'s protocol). -/
def serverRes (cfg : Cfg GF) (id : Nat) : IProp GF :=
  if id = 1 then coordRes cfg
  else iprop(nodeRes cfg (serverAddrs.getD (id - 1) []) ∗
    joinTicket cfg.γ (serverAddrs.getD (id - 1) []) ∗
    addrProto (Gg := hG.goose_globalGS) (confAddrs.getD (5 + id - 1) []) confProto confProto)

/-- `Server(id)`: server machine `id` (`1 ≤ id ≤ 6`): the coordinator (`id = 1`) or a chain
machine. Its machine's codec registry (`codecFresh`), mux (`muxOwner []`) and net/rpc's server
variables (`srvEnv`) are at their initial states (from its initialization: findings F2, H4). -/
abbrev Server.spec [RpcHttpServe GF] : Prop :=
  ∀ (cfg : Cfg GF) (id : w64), cfgKit cfg → 1 ≤ uint.nat id → uint.nat id ≤ 6 →
  {{ isPkgInit (PROP := IProp GF) kpkg ∗ codecFresh ∗ RpcHttpServe.muxOwner [] ∗
      net.rpc.srvEnv ∗ craqCtx cfg ∗ serverRes cfg (uint.nat id) }}
    (App (Val (@! github_com.despreston.go_craq.examples.craqnet.Server)) (Val #id))
  {{ RET #(); True }}

/-- RemoveNode's method obligation (finding F1: a premise until Net's `callRet` admits `errAny`). -/
abbrev removeNodeOk.spec (cfg : Cfg GF) : Prop :=
  ∀ (b : Loc) (svc : GoInterface), coordB cfg b svc ⊢
    newArgOk craqCodec (ptrIface transport.netrpc.CoordinatorBinding.ty b)
      (coordSpec cfg.γ cfg.chain go!"RemoveNode")
      (mOf examples.craqnet.rpcNewArg_r1_RemoveNode examples.craqnet.rpcNewReply_r1_RemoveNode
        examples.craqnet.rpcCall_r1_RemoveNode)

/-- **Finding F2's premise, in the shape Net will give** (#24: net/rpc's initialization returns a
per-machine resource once, like gryff's replicas' `wp_initialize'_own`): a machine's boot
resources, made by its program's initialization: the codec registry at its initial state
(`codecFresh`), net/rpc's package variables as its server and clients read them (`srvEnv`:
`cliEnv`'s and `invalidRequest`; the part's net/rpc package fact is `True`,
`Dsverify/Proof/net/rpc/Init.lean`, so they come with the boot, as dsv-epaxos's), and
`DefaultServeMux` with nothing registered (`muxOwner []`, net/http's; H4). -/
def rpcBootRes [RpcHttpServe GF] : IProp GF :=
  iprop(codecFresh ∗ net.rpc.srvEnv ∗ RpcHttpServe.muxOwner [])

/-- **F2's premise**: command `pkg`'s initializer `init`, run once from the machine's empty
package state (only the deployment's boot holds `ownGoState ∅`, once per machine), initializes
the program (any package table `getIs` consistent with `pkg`'s) and returns the machine's boot resources. -/
def RpcBoot [RpcHttpServe GF] (init : val) (pkg : GoString) [IsPkgInit (IProp GF) pkg]
    [GetIsPkgInitWf (IProp GF) pkg] : Prop :=
  ∀ getIs : GoString → IProp GF, GetIsPkgInitProp pkg getIs →
  {{ ownGoState (hG := hG.goose_localGS.goose_go_stateGS) ∅ }}
    (App (Val init) (Val #()))
  {{ RET #(); ownInitializing getIs ∗ isPkgInit (PROP := IProp GF) pkg ∗ rpcBootRes }}

end proof

end github_com.despreston.go_craq.examples.craqnet
end Perennial
