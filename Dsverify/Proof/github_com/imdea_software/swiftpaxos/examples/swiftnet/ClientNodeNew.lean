/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/ClientNodeNew.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`NewClient(c)` (`kit.go`) on client node `c`: `newClient(Addrs(), c)`: it waits for the
configuration on the node's configuration port (`awaitConf` over a one-slot channel, a future
whose contract `msgC` carries the configuration fact, the node's leader changes and the node's
claimed ghost, which `awaitConf` registered before its first acknowledgment), registers the rpc
codec, builds the `Sys` (read-only `addrs`, `conf`; `b` nil; `mu` over `done`) and starts the
node's leader changes. The result: `isSys` and the token at operation 0 (the protocol's sequence
number 0 of the client id `c + 1`, from the share's `clientStart`).

`awaitConf` is group C's `wp_awaitConf_client` (with `client.claimGhost.spec`, L2's, as its
registration step: a hypothesis); `Addrs`, `at` are used through their specs (hypotheses).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ClientNodeShare
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ClientLeaders
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.AwaitConf

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp netShaExts_has netShaExts_hasSha256

namespace cnode

/-- A valid change of a valid configuration is at a replica's server node (2..6). -/
theorem changes_node (cf : Conf) (cs : List Change) (hv : cf.valid) (hcs : cf.changesOk cs) :
    ∀ ch ∈ cs.map goChange, 2 ≤ uint.nat ch.Node' ∧ uint.nat ch.Node' ≤ 6 := by
  intro ch hch
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hch
  have h := hcs.2 x hx
  unfold Change.valid at h
  have hn : cf.n ≤ 5 := by rcases hv.1 with h | h <;> omega
  simp only [goChange]
  have : uint.nat (W64 (x.node : Int)) = x.node := by
    have : x.node < 2 ^ 64 := by omega
    word
  omega

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]

/-- What `awaitConf` hands to client node `c`'s `newClient` over the channel (group C's
`confMsg`, ServersDefs.lean): the configuration (its fact), the node's changes (`decode`'s
slice, owned) and the node's claimed ghost. -/
abbrev msgC (γ : SwiftNames netDistGF) (c : Nat) : examples.swiftnet.msg → IProp netDistGF :=
  confMsg γ (fun _ _ => True) (client.nodeGhostOk γ.sp (sp.PNode.cl c))

end defs

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]

local notation "swiftnetPkg" => pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet

/-- `Addrs()`: a new slice of the nodes' first addresses (group C's `Addrs.spec`). -/
abbrev AddrsC.spec : Prop :=
  {{ isPkgInit (PROP := IProp netDistGF) swiftnetPkg }}
    (App (Val (@! examples.swiftnet.Addrs)) (Val #()))
  {{ (sl : GoSlice), RET #sl; sl ↦* addrs }}

/-- `at(addrs, 1+c, ConfOff)`: client node `c`'s configuration port (an instance of the
adapter's `at` spec). -/
abbrev atConf.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (c : Nat), c < 6 →
  {{ isPkgInit (PROP := IProp netDistGF) swiftnetPkg ∗ sl ↦*{dq} addrs }}
    (App (App (App (Val (@! examples.swiftnet.«at»)) (Val #sl)) (Val #(W64 1 + W64 (c : Int))))
      (Val #(W64 2000)))
  {{ RET #(confAddrC c); sl ↦*{dq} addrs }}

end specs

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [examples.swiftnet.Assumptions] [net.model.Assumptions] [io.ExtraAssumptions]
variable [C : net.rpc.RpcCodec netDistGF] [KitLike C]

set_option goose.wp.extras true

/-- The client node's own address token takes the node's fresh ghost from the client
package's state (`client.ghostFresh_take` at the run's package states; decision D90, R-E1). -/
abbrev freshTake.spec (c : Nat) : Prop :=
  ⊢ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client -∗
    addrTokG netDistGS (clientNodeAddrs.getD c go!"") ={⊤}=∗ client.ghostFresh

theorem newClient.wp_proof (γ : SwiftNames netDistGF) (c : Nat) (hc : c < 6)
    (wp_at : atConf.spec) (wp_claim : client.claimGhost.spec) (wp_fresh : freshTake.spec c)
    (wp_registerRPC : registerRPC.spec (GF := netDistGF))
    (wp_changeLeaders : Sys.changeLeaders.spec γ c)
    (hcodec : ⊢ net.rpc.kitCodecOk (GF := netDistGF)) (asl : GoSlice) :
    {{ isPkgInit (PROP := IProp netDistGF)
          pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet ∗
        asl ↦* addrs ∗ clientNodeShare γ c }}
      (App (App (Val (@! examples.swiftnet.newClient)) (Val #asl)) (Val #(W64 (c : Int))))
    {{ (s : Loc), RET #s; isSysL γ c s ∗ clSt γ s c 0 }} := by
  wp_start as ⟨Hasl, Hsh⟩
  ihave ⟨Hkey, Hct, #Hcp, Hseq, Hpt, #Hm, #Hrpcs, %HSS, #Hreps, #Hinv⟩ :=
    clientNodeShare_split γ c hc $$ Hsh
  ihave #Hcpkg : isPkgInit (PROP := IProp netDistGF)
      pkg_id.github_com.imdea_software.swiftpaxos.client $$ []
  · iPkgInit
  iapply fupd_wp
  imod wp_fresh $$ Hcpkg Hkey with Hfr
  imodintro
  ihave #HcodecOk := hcodec
  wp_auto
  wp_apply (chan.wp_make2 (V := examples.swiftnet.msg) (W64 1)) as %chl %γch ⟨#Hch, %Hcap, Hoc⟩
  · ipureintro; decide
  imod start_future (V := examples.swiftnet.msg) chl γch _ (Or.inr rfl) $$ Hch Hoc
    with ⟨%γf, #Hfut, Haw⟩
  imod future_alloc_promise γf chl (msgC γ c) [] $$ Hfut Haw with ⟨Hful, Haw⟩
  wp_apply wp_at asl (DFrac.own 1) c hc $$ [$Hasl] as Hasl
  wp_apply wp_fork $$ [Hct Hful Hpt Hfr]
  · wp_apply wp_awaitConf_client wp_claim γ c (confAddrC c) chl γf
      $$ [$Hct $Hcp $Hfut $Hful $Hinv $Hpt $Hfr]
    iintro %Hf; exact Hf.elim
  wp_apply (wp_future_await (t := examples.swiftnet.msg.ty) γf chl _) $$ [$Hfut $Haw]
    as %v %P %pre %post ⟨%Hpend, HP, -⟩
  have hP : P = msgC γ c := by
    rcases pre with _ | ⟨_, _ | _⟩ <;> simp_all
  subst hP
  iunfold msgC at HP
  iunfold confMsg at HP
  icases HP with ⟨%cf, %cs, #Hcf, %Hv, Hcs, #Hgok⟩
  obtain ⟨hcv, hcs, -, hvc⟩ := Hv
  rw [show goConf cf = confV cf from rfl] at hvc
  wp_apply wp_registerRPC as ⟨#HcodecSet, -⟩
  ihave H := typedPointsto_split _ _ _ $$ «$r0»
  simp only [TypedPointsto.typedPointstoDef]
  icases H with ⟨Haddrs, Hconf, Hb, Hmu, Hdone, -⟩
  rw [hvc]
  imod (typedPointsto_dfractional _ _).dfractional_persist $$ Haddrs with #Haddrs
  imod (typedPointsto_dfractional _ _).dfractional_persist $$ Hconf with #Hconf
  imod ownSlice_persist $$ Hasl with #Hasl
  imod ownSlice_persist $$ Hcs with #Hcs
  imod sync.init_Mutex iprop(∃ d : w64, «$r0_ptr».[examples.swiftnet.Sys, go!"done"] ↦ d) ⊤
    _ $$ Hmu [Hdone] with #Hmutex
  · inext; iexists _; iexact Hdone
  ihave #HsysL : isSysL γ c «$r0_ptr» $$ []
  · iunfold isSysL
    iexists cf, asl
    iframe Haddrs Hasl Hconf Hcf Hmutex Hgok
    iunfold nodeEnv
    iframe Hm Hrpcs HcodecSet HcodecOk Hreps Hinv
    ipureintro; exact HSS
  wp_apply wp_fork $$ []
  · wp_apply wp_changeLeaders «$r0_ptr» v.cs' (cs.map goChange) (changes_node cf cs hcv hcs) $$ []
    · iframe HsysL Hcs
    itrivial
  iapply HΦ
  iframe HsysL
  iunfold clSt
  ileft
  iframe Hb
  unfold cidOf
  iexact Hseq

theorem NewClient.wp_proof (γ : SwiftNames netDistGF) (c : Nat) (hc : c < 6)
    (wp_Addrs : AddrsC.spec)
    (wp_at : atConf.spec) (wp_claim : client.claimGhost.spec) (wp_fresh : freshTake.spec c)
    (wp_registerRPC : registerRPC.spec (GF := netDistGF))
    (wp_changeLeaders : Sys.changeLeaders.spec γ c)
    (hcodec : ⊢ net.rpc.kitCodecOk (GF := netDistGF)) :
    {{ isPkgInit (PROP := IProp netDistGF)
          pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet ∗ clientNodeShare γ c }}
      (App (Val (@! examples.swiftnet.NewClient)) (Val #(W64 (c : Int))))
    {{ (sys : GoInterface), RET #sys; isSys γ c sys ∗ clientTok γ c sys 0 }} := by
  wp_start as Hsh
  wp_auto
  wp_apply wp_Addrs as %asl Hasl
  wp_apply newClient.wp_proof γ c hc wp_at wp_claim wp_fresh wp_registerRPC wp_changeLeaders hcodec asl
    $$ [$Hasl $Hsh] as %s ⟨#Hs, Hst⟩
  iapply HΦ
  isplitl []
  · iunfold isSys
    iexists s
    iframe Hs
    ipureintro; rfl
  · iunfold clientTok
    iexists s
    iframe Hst
    ipureintro; rfl

end proof

end cnode

end Perennial.github_com.imdea_software.swiftpaxos
