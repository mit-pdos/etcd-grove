/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/Servers.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`ServersOk` (Spec/swiftnet/Interface.lean): each server node's boot program (the test
package's initialization, then `Server(id)`), from its share, over the specs of the callees in
other packages (taken as hypotheses: `ServersHyps`). Linked in `ServersLink.lean`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.Serve
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.Addr
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.Register
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.PkgState

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

-- The codec of the linked results (decision D6, HUB-REQUEST 2, Proof/swiftnet/KitLike.lean):
-- `kitCodecC`, whose `kitCodecOk` holds (`kitCodecOkC_holds`).
attribute [local instance 2000] examples.swiftnet.kitCodecC

local notation "swiftnetPkg" => pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [SwiftNetPkgState netDistGF] [examples.swiftnet.Assumptions]

/-- The test package's initialization (it initializes every package of the run): no frozen
spec covers it; the server proof takes it as a hypothesis (the packages' initializers are
their own proofs). The driver's form (`DriverClientSpec.wp_initialize'`). -/
abbrev swiftnetInit.spec : Prop :=
  ∀ (g : GoString → IProp netDistGF), GetIsPkgInitProp swiftnetPkg g →
  {{ ownInitializing g }}
    (App (Val examples.swiftnet.initialize') (Val #()))
  {{ RET #(); ownInitializing g ∗ isPkgInit (PROP := IProp netDistGF) swiftnetPkg }}

/-- `offIn L p`: the package `p` is one of `L`. -/
def offIn : List GoString → GoString → Bool
  | [], _ => false
  | q :: L, p => if p = q then true else offIn L p

/-- The boot program's `get_is_pkg_init` (the one `servers_ok_of` uses). -/
def gBoot : GoString → IProp netDistGF := get_is_pkg_init_of% swiftnetPkg

/-- `gBoot` with the packages `L` mapped to `False`: `ownInitializing (gSrv L)` says that the
packages `L` are not initialized yet (decision D9: their first initialization hands out the
mutable globals, `wp_package_init_first`, Proof/swiftnet/InitFirst.lean). -/
def gSrv (L : List GoString) : GoString → IProp netDistGF :=
  fun p => if offIn L p then iprop(False) else gBoot p

/-- The server-side initialization (change log C14, decision D9): from a fresh node (the test
package, `swift` and `concurrent-map` not initialized yet), the test package's initialization
ends with `ownInitializing gBoot`, the test package's `isPkgInit`, and on a replica node the
mutable globals (`swift.mutGlobals`: `MaxDescRoutines`, `useFastAckPool`, `cmap.SHARD_COUNT`),
which the package states leave out there: the first initialization of `swift` and of
`concurrent-map` returns them, up the test package's initialization; and on a replica node the
node's fresh ghost (`client.freshAt`, decision D90 R-E1), which the first initialization of
`client` returns. -/
abbrev swiftnetInitSrv.spec : Prop :=
  {{ ownInitializing (gSrv [swiftnetPkg, pkg_id.github_com.imdea_software.swiftpaxos.swift,
        pkg_id.github_com.imdea_software.swiftpaxos.client,
        pkg_id.github_com.orcaman.concurrent_map]) }}
    (App (Val examples.swiftnet.initialize') (Val #()))
  {{ RET #(); ownInitializing gBoot ∗ isPkgInit (PROP := IProp netDistGF) swiftnetPkg ∗
      swift.mutGlobalsAt (netIp (L := hG.goose_localGS) (GF := netDistGF)) ∗
      client.freshAt (netIp (L := hG.goose_localGS) (GF := netDistGF)) }}

end specs

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [SwiftNetPkgState netDistGF] [examples.swiftnet.Assumptions] [net.model.Assumptions]
  [io.ExtraAssumptions]

set_option goose.wp.extras true

/-- `Server(id)` on server node `id = i + 1` (node `7 + i`). -/
theorem wp_Server (wp_claim : client.claimGhost.spec) (γ : SwiftNames netDistGF) (i : Nat)
    (hi : i < 6)
    (hreg : registerRPC.spec (GF := netDistGF))
    (hMNew : master.New.spec) (hMRun : master.Master.Run.spec')
    (hmax : setMaxDesc.spec (GF := netDistGF)) (hSNew : swift.New.spec)
    (hcodec : ⊢ net.rpc.kitCodecOk (GF := netDistGF)) :
    {{ isPkgInit (PROP := IProp netDistGF) swiftnetPkg ∗ serverShare γ i ∗
        nodeIp (nodeHost (7 + i)) ∗ net.http.muxOwner [] ∗
        swift.mutGlobalsAt (nodeHost (7 + i)) ∗ client.freshAt (nodeHost (7 + i)) }}
      (App (Val (@! examples.swiftnet.Server)) (Val #(W64 (i + 1))))
    {{ RET #(); False }} := by
  wp_start as ⟨Hsh, #Hip, Hmux, Hglob, Hfr⟩
  wp_auto
  wp_apply wp_Addrs_servers as %sl Hsl
  wp_apply wp_serve wp_claim γ i hi sl wp_at wp_port wp_host wp_nodeConfig hreg hMNew hMRun wp_register
    hmax hSNew hcodec $$ [$Hsl $Hsh $Hip $Hmux $Hglob $Hfr] as %Hf
  exact Hf.elim

end proof

/-! ## The server nodes -/

/-- Server node `i + 1` runs `Server(i + 1)`. -/
theorem serverNodes_get [GoGlobalContext] (i : Nat) (nd : Node) (h : serverNodes[i]? = some nd) :
    i < 6 ∧ nd = Node.mk (fun [_] [_] => nodeAssumptions) examples.swiftnet.initialize'
      examples.swiftnet.Server [ #(W64 ((i + 1 : Nat) : Int)) ] := by
  match i, h with
  | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h =>
    simp only [serverNodes, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.some.injEq] at h
    subst h; exact ⟨by omega, rfl⟩
  | _ + 6, h => simp [serverNodes] at h

/-- Server node `i + 1`'s IP is `nodeHost (7 + i)`. -/
theorem serverIp_spell [GoGlobalContext] (i : Nat) (ip : IPv4)
    (h : swiftNetCfg.ips[1 + clientNodes.length + i]? = some ip) (hi : i < 6) :
    ip.spell = nodeHost (7 + i) := by
  rw [show 1 + clientNodes.length + i = 7 + i from by simp [clientNodes]] at h
  match i, h, hi with
  | 0, h, _ | 1, h, _ | 2, h, _ | 3, h, _ | 4, h, _ | 5, h, _ =>
    simp only [swiftNetCfg, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq] at h
    subst h
    decide

/-- The specs of the server nodes' callees in other packages (the frozen cross-package specs,
the codec's laws) and the hypotheses with no frozen statement (the test package's
initialization; the store to `swift.MaxDescRoutines`, HUB-REQUEST 2; the claim of a predicted
node's ghost, `client.claimGhost.spec`, L2's), at every node's local
ghost state and Go context, for the run's package states (`pkgStates`). -/
def ServersHyps [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF] : Prop :=
  ∀ (hG : HeapGS .hasLC netDistGF) (s : go.Semantics), hG.goose_globalGS = G →
    ∀ [examples.swiftnet.Assumptions] [net.model.Assumptions] [io.ExtraAssumptions],
    letI := @pkgStates _ netDistGF hG s
    swiftnetInitSrv.spec ∧ client.claimGhost.spec ∧ registerRPC.spec (GF := netDistGF) ∧
      master.New.spec ∧
      master.Master.Run.spec' ∧ setMaxDesc.spec (GF := netDistGF) ∧ swift.New.spec ∧
      (⊢ net.rpc.kitCodecOk (GF := netDistGF))

set_option goose.wp.extras true in
/-- **`ServersOk`**, from the callees' specs. -/
theorem servers_ok_of [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF]
    (H : ServersHyps) : ServersOk := by
  intro γ i nd ip hnd hip hG s hGG hA
  obtain ⟨hi, rfl⟩ := serverNodes_get i nd hnd
  obtain ⟨hA1, hA2, hA3⟩ := hA
  letI := @pkgStates _ netDistGF hG s
  obtain ⟨hinit, hclaim, hreg, hMNew, hMRun, hmax, hSNew, hcodec⟩ := H hG s hGG
  rw [serverIp_spell i ip hip hi]
  subst hGG
  iintro Hsh #Hip Hgs
  unfold Node.boot callArgs
  simp only [List.foldl_cons, List.foldl_nil]
  wp_bind (App (Val examples.swiftnet.initialize') (Val #()))
  wp_apply hinit $$ [Hgs]
    as ⟨Hown, #Hpkg, Hglob, Hfr⟩
  · rw [ownInitializing_unseal]
    unfold ownInitializingDef
    iexists ∅
    iframe Hgs
    iintro !>
    iapply BigSepM.bigSepM_empty.2
    iempintro
  ihave #Hhttp : isPkgInit (PROP := IProp netDistGF) pkg_id.net.http $$ []
  · iPkgInit
  imod net.http.muxOwner_claim_init _ $$ Hhttp Hown with Hmux
  wp_pures
  have e : ((i + 1 : Nat) : Int) = (i : Int) + 1 := by omega
  rw [e]
  icases Hip with %Hipe
  rw [Hipe]
  wp_apply wp_Server hclaim γ i hi hreg hMNew hMRun hmax hSNew hcodec $$ [$Hpkg $Hsh $Hmux Hglob Hfr]
    as %Hf
  · iframe
    ipureintro; exact Hipe
  exact Hf.elim

end Perennial.github_com.imdea_software.swiftpaxos
