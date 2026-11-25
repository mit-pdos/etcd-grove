/-
The specs and lemmas the kit's machine proofs share (CLAUDE.md, "Import tiers": a proof file sees
its callees through their specs only): the address functions' and `attempt`'s specs, the three
machines' (`Client.spec`, `Orch.spec`, `Server.spec`, out of their proof files, for `Mains`), the
network callees of the configuration protocol (`KitNetDeps`, linked in `Linked.lean`), and the
lemmas `ClientProof` and `ServerProof` share with `ConfProof`.
-/
module

public import Dsverify.Proof.rabia.examples.rabianet.Kit
public import Dsverify.Proof.rabia.examples.rabianet.KitModel
public import Dsverify.Proof.rabia.examples.rabianet.ConnRead
public import Dsverify.Proof.rabia.roles.server.Spec
public import Dsverify.Proof.rabia.internal.config.Spec
public import Dsverify.Proof.math.rand.Spec
public import Perennial.Spec.log.Println
public import Net.Spec.net.Dial
public import Net.Spec.net.Listen
public import Net.Spec.net.Listener__Accept
public import Net.Spec.net.Conn__Read
public import Net.Spec.net.Conn__Write
public import Net.Spec.net.Conn__Close
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.ServeClient
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.Check

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.rabia.examples.rabianet

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode model Net rabia.internal.message
  rabia.internal.config rabia.internal.tcp rabia

theorem range_map_get {A : Type} (f : Nat → A) (n i : Nat) (h : i < n) :
    ((List.range n).map f)[i]? = some (f i) := by
  simp [List.getElem?_range h]

theorem take_peers (cf : RCfg) (h : cf.n ≤ maxS) :
    ((List.range maxS).map netAddr).take cf.n = peerStrs cf := by
  unfold peerStrs
  rw [← List.map_take, List.take_range, Nat.min_eq_left h]

section conf
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable [package_sem : rabia.examples.rabianet.Assumptions]
variable [math.rand.Hyps GF]
variable [_root_.Perennial.io.Assumptions] [net.Assumptions] [go.BasicIntoValInj]

/-- `ProxyAddrs()`. -/
abbrev ProxyAddrs.spec : Prop :=
    {{ (True : IProp GF) }}
      (App (Val (@! rabia.examples.rabianet.ProxyAddrs)) (Val #()))
    {{ (sl : GoSlice), RET #sl; ∃ L, sl ↦* L ∗ ⌜L = (List.range maxS).map proxyAddr⌝ }}

/-- `NetAddrs()`. -/
abbrev NetAddrs.spec : Prop :=
    {{ (True : IProp GF) }}
      (App (Val (@! rabia.examples.rabianet.NetAddrs)) (Val #()))
    {{ (sl : GoSlice), RET #sl; ∃ L, sl ↦* L ∗ ⌜L = (List.range maxS).map netAddr⌝ }}

/-- `ServerConfAddrs()`. -/
abbrev ServerConfAddrs.spec : Prop :=
    {{ (True : IProp GF) }}
      (App (Val (@! rabia.examples.rabianet.ServerConfAddrs)) (Val #()))
    {{ (sl : GoSlice), RET #sl; ∃ L, sl ↦* L ∗ ⌜L = (List.range maxS).map cfgAddr⌝ }}

/-- `ClientAddrs()`. -/
abbrev ClientAddrs.spec : Prop :=
    {{ (True : IProp GF) }}
      (App (Val (@! rabia.examples.rabianet.ClientAddrs)) (Val #()))
    {{ (sl : GoSlice), RET #sl; ∃ L, sl ↦* L ∗ ⌜L = (List.range nC).map cliAddr⌝ }}

/-- `ClientConfAddrs()`. -/
abbrev ClientConfAddrs.spec : Prop :=
    {{ (True : IProp GF) }}
      (App (Val (@! rabia.examples.rabianet.ClientConfAddrs)) (Val #()))
    {{ (sl : GoSlice), RET #sl; ∃ L, sl ↦* L ∗ ⌜L = (List.range nC).map cliCfgAddr⌝ }}

/-- `attempt()`: some duration. -/
abbrev attempt.spec : Prop :=
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.examples.rabianet }}
      (App (Val (@! rabia.examples.rabianet.attempt)) (Val #()))
    {{ (d : w64), RET #d; True }}

/-- The network callees of the configuration protocol (`sendConf`, `awaitConf`) and
`Config.CalcConstants` (`configure`): hypotheses of `ConfProof`'s proofs, linked in `Linked.lean`. -/
structure KitNetDeps : Prop where
  dial : net.Dial.spec (GF := GF) (hG := hG)
  listen : net.Listen.spec (GF := GF) (hG := hG)
  accept : net.Listener.Accept.spec (GF := GF) (hG := hG)
  read : net.Conn.Read.spec (GF := GF) (hG := hG)
  write : net.Conn.Write.spec (GF := GF) (hG := hG)
  close : net.Conn.Close.spec (GF := GF) (hG := hG)
  readFullLt : io.ReadFull.specLt (GF := GF) (hG := hG)
  calcConstants : Config.CalcConstants.spec (GF := GF)
  println : log.Println.spec (GF := GF) (hG := hG)

theorem cfgIs_ok' (γ : RabiaNames) (cf : RCfg) : cfgIs (GF := GF) γ cf ⊢ ⌜cf.Ok⌝ := by
  unfold cfgIs; iintro ⟨-, %h⟩; ipureintro; exact h

end conf

section client
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable [package_sem : rabia.examples.rabianet.Assumptions]
variable [math.rand.Hyps GF]
variable [_root_.Perennial.io.Assumptions] [net.Assumptions] [go.BasicIntoValInj]
variable [sync.Assumptions] [_root_.Perennial.bufio.Assumptions]
variable [tcp_sem : rabia.internal.tcp.Assumptions] [msg_sem : rabia.internal.message.Assumptions]

/-- `Conf`'s points-to, claimed with the machine's package state (`confClaim`). -/
theorem conf_claim (σ : GMap GoString Bool) (E : CoPset) (hE : ↑confN ⊆ E) :
    isPkgInit (PROP := IProp GF) pkg_id.rabia.examples.rabianet ∗
      ownGoState (hG := hG.goose_localGS.goose_go_stateGS) σ ⊢
      |={E}=> (globalAddr rabia.internal.config.Conf ↦ (zeroValDef : rabia.internal.config.Config)) := by
  iintro ⟨#Hpkg, Hσ⟩
  ihave #Hcfg : isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.config $$ []
  · iPkgInit
  ihave #Hcinv : inv confN (confInv (GF := GF) (hG := hG)) $$ []
  · have hcfg : (isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.config : IProp GF) ⊢
        inv confN (confInv (GF := GF) (hG := hG)) := by
      with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.rabia.internal.config
    iapply hcfg $$ Hcfg
  iapply confClaim E hE σ $$ [$Hcinv $Hσ]

variable [ρ : _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.lib.remote.RemoteGS]

open github_com.mit_pdos.etcd_grove.examples.lib.remote in
/-- `Client(c)`: client machine `c`, from its share, its package state (with which it claims
`Conf`), its address's remote protocols and remote's map; it never returns. -/
abbrev Client.spec : Prop :=
  ∀ (γ : Names) (c : Nat) (σ : GMap GoString Bool), c < nC →
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.examples.rabianet ∗ cliCore γ c ∗
        ownGoState (hG := hG.goose_localGS.goose_go_stateGS) σ ∗
        remoteAddr (Gg := hG.goose_globalGS) (kvR γ) (cliAddr c) ∗
        mapCtx (Gg := hG.goose_globalGS) (I := KIn) }}
      (App (Val (@! rabia.examples.rabianet.Client)) (Val #(W64 c)))
    {{ RET #(); False }}

end client

section orch
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory
open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote

variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable [package_sem : rabia.examples.rabianet.Assumptions]
variable [math.rand.Hyps GF]
variable [_root_.Perennial.io.Assumptions] [net.Assumptions] [go.BasicIntoValInj]
variable [ρ : RemoteGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- `Orch()`: the orchestrator, from its share and remote's: the client machines' addresses'
protocols, the map of operations, the pending library over the key-value map, and the client
addresses' call units (`K` operations of `readTries` attempts each); it returns
(porcupine accepts the history). -/
abbrev Orch.spec : Prop :=
  ∀ (γ : Names) (γp : PendNames), receiptBound GF ≤ 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.examples.rabianet ∗ orchCore γ ∗
      ([∗list] a ∈ (List.range nC).map cliAddr, remoteAddr (Gg := hG.goose_globalGS) (kvR γ) a) ∗
      mapCtx (Gg := hG.goose_globalGS) (I := KIn) ∗
      pendCtx (Gg := hG.goose_globalGS) (kvR γ) (kvS0 (GF := GF)) γp ∗
      pendLib (Gg := hG.goose_globalGS) (kvS0 (GF := GF)) γp (kvS0 (GF := GF)).M.init ∗
      [∗list] a ∈ (List.range nC).map cliAddr, budUnits (Gg := hG.goose_globalGS) a 24 }}
    (App (Val (@! rabia.examples.rabianet.Orch)) (Val #()))
  {{ RET #(); True }}

end orch

section server
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable [package_sem : rabia.examples.rabianet.Assumptions]
variable [srv_sem : rabia.roles.server.Assumptions]
variable [math.rand.Hyps GF]
variable [_root_.Perennial.io.Assumptions] [net.Assumptions] [go.BasicIntoValInj]

/-- `Server(id)`: server machine `id = k + 1` (`k < maxS`), from its share and its package state
(with which it claims `Conf` if it serves); it never returns. -/
abbrev Server.spec : Prop :=
  ∀ (γ : Names) (k : Nat) (σ : GMap GoString Bool), k < maxS →
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.examples.rabianet ∗ serverShare γ k ∗
        ownGoState (hG := hG.goose_localGS.goose_go_stateGS) σ }}
      (App (Val (@! rabia.examples.rabianet.Server)) (Val #(W64 ((k + 1 : Nat) : Int))))
    {{ RET #(); False }}

end server

end Perennial.rabia.examples.rabianet
