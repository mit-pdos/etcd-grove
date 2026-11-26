/-
The kit's server machine (`kit.go`): `serveAt` (claim and configure `Conf`, `ServerInit`,
`Prologue`, `ServerMain`, which never returns) and `Server(id)` (wait for the configuration at
server `id`'s configuration address; if `id ≤ n`, `serveAt`; then sleep forever). The server
package's specs (`roles/server/Spec.lean`) are hypotheses here, linked in `Linked.lean`.
-/
module

public import Dsverify.Proof.rabia.examples.rabianet.KitSpecs
public import Dsverify.Proof.rabia.roles.server.Spec
public import Perennial.Proof.time

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.rabia.examples.rabianet

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode model Net rabia.internal.message
  rabia.internal.config rabia.internal.tcp rabia

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable [package_sem : rabia.examples.rabianet.Assumptions]
variable [srv_sem : rabia.roles.server.Assumptions]
variable [math.rand.Hyps GF]
variable [_root_.Perennial.io.Assumptions] [net.Assumptions] [go.BasicIntoValInj]

set_option goose.wp.extras true

theorem w32_pred (k : Nat) (hk : k < 5) :
    (W32 (uint.Z (W64 ((k + 1 : Nat) : Int) - W64 1))).toNat = k := by word

theorem w64_pred (k : Nat) (hk : k < 5) : sint.Z (W64 ((k + 1 : Nat) : Int) - W64 1) = (k : Int) := by
  word

/-- `serveAt(k + 1, proxyAddr k, ps, conf)` (`k < n`, `ps` the first `n` network addresses):
`configure` with `Conf` claimed, then server `k`'s `ServerInit`, `Prologue`, `ServerMain`; it never
returns. -/
theorem serveAt.wp_proof
    (wp_ServerInit : rabia.roles.server.ServerInit.spec (GF := GF))
    (wp_Prologue : rabia.roles.server.Server.Prologue.spec (GF := GF))
    (wp_ServerMain : rabia.roles.server.Server.ServerMain.spec (GF := GF))
    (wp_configure : configure.spec (GF := GF)) (wp_ProxyAddrs : ProxyAddrs.spec (GF := GF))
    (wp_NetAddrs : NetAddrs.spec (GF := GF))
    (γ : Names) (cf : RCfg) (k : Nat) (ps : GoSlice) (σ : GMap GoString Bool) (hk : k < cf.n) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.examples.rabianet ∗ cfgIs γ.rab cf ∗
        serverCore γ k ∗ ps ↦*□ peerStrs cf ∗
        ownGoState (hG := hG.goose_localGS.goose_go_stateGS) σ }}
      (App (App (App (App (Val (@! rabia.examples.rabianet.serveAt))
        (Val #(W64 ((k + 1 : Nat) : Int)))) (Val #(proxyAddr k))) (Val #ps)) (Val #(confV cf)))
    {{ RET #(); False }} := by
  wp_start as ⟨#Hcfg, Hcore, #Hps, Hσ⟩
  ihave %Hok := cfgIs_ok' γ.rab cf $$ Hcfg
  have hn5 : cf.n ≤ maxS := by have := Hok; unfold RCfg.Ok at this; unfold maxS; omega
  have hk5 : k < 5 := by unfold maxS at hn5; omega
  ihave #Hsh : shared γ $$ [Hcore]
  · unfold serverCore; icases Hcore with ⟨#H, -⟩; iexact H
  ihave #Hsrv : isPkgInit (PROP := IProp GF) pkg_id.rabia.roles.server $$ []
  · iPkgInit
  wp_auto
  iapply fupd_wp
  imod conf_claim σ ⊤ (by simp) $$ [$Hpkg $Hσ] with HC
  imodintro
  wp_apply wp_configure _ cf $$ [$Hpkg $HC $Hps] as #Hconf
  · ipureintro; exact Hok
  ihave %Hpl := ownSlice_len _ _ _ $$ Hps
  have hpl : sint.Z ps.len = (cf.n : Int) := by
    obtain ⟨h1, h2⟩ := Hpl
    unfold peerStrs at h1
    rw [List.length_map, List.length_range] at h1
    rw [h1]; exact (Int.toNat_of_nonneg h2).symm
  have hkz := w64_pred k hk5
  rw [ite_eq_left (by rw [hkz, hpl]; omega)]
  wp_apply wp_load_slice_index ps _ _ _ (netAddr k) (by omega) $$ [$Hps] as -
  · ipureintro; rw [hkz]; simp only [Int.toNat_natCast]
    unfold peerStrs; exact range_map_get _ _ _ hk
  have hk32 := w32_pred k hk5
  wp_apply (wp_ServerInit γ cf k _ hk32 hk) $$ [$Hsrv $Hconf $Hcfg $Hcore] as %s Hb
  try wp_auto
  wp_apply (wp_Prologue γ cf k s) $$ [$Hsrv $Hconf $Hsh $Hcfg $Hb] as Hr
  wp_apply (wp_ServerMain γ cf k s) $$ [$Hsrv $Hconf $Hsh $Hcfg $Hr] as Hf
  iexfalso; iexact Hf

/-- `Server(id)` (`Server.spec`). -/
theorem Server.wp_proof
    (wp_ServerInit : rabia.roles.server.ServerInit.spec (GF := GF))
    (wp_Prologue : rabia.roles.server.Server.Prologue.spec (GF := GF))
    (wp_ServerMain : rabia.roles.server.Server.ServerMain.spec (GF := GF))
    (wp_configure : configure.spec (GF := GF)) (wp_ProxyAddrs : ProxyAddrs.spec (GF := GF))
    (wp_NetAddrs : NetAddrs.spec (GF := GF)) (wp_ServerConfAddrs : ServerConfAddrs.spec (GF := GF))
    (wp_waitConf : waitConf.spec (GF := GF)) :
    Server.spec (GF := GF) := by
  intro γ k σ hk
  have hk5 : k < 5 := hk
  wp_start as ⟨Hshare, Hσ⟩
  unfold serverShare
  icases Hshare with ⟨Hcore, -⟩
  ihave #Hsh : shared γ $$ [Hcore]
  · unfold serverCore; icases Hcore with ⟨#H, -⟩; iexact H
  ihave #Hproto := shared_cfgProto γ k hk $$ Hsh
  wp_auto
  wp_apply wp_ServerConfAddrs as %sl ⟨%L, Hsl, %HL⟩
  subst HL
  ihave %Hsl0 := ownSlice_len _ _ _ $$ Hsl
  have hkz := w64_pred k hk5
  have hsl : sint.Z sl.len = (maxS : Int) := by
    obtain ⟨h1, h2⟩ := Hsl0
    rw [List.length_map, List.length_range] at h1
    rw [h1]; exact (Int.toNat_of_nonneg h2).symm
  rw [ite_eq_left (by rw [hkz, hsl]; omega)]
  wp_apply wp_load_slice_index sl _ _ _ (cfgAddr k) (by omega) $$ [$Hsl] as -
  · ipureintro; rw [hkz]; simp only [Int.toNat_natCast]; exact range_map_get _ _ _ hk
  wp_apply wp_waitConf γ (cfgAddr k) $$ [] as %v ⟨%cf, %Hv, #Hcfg⟩
  · iframe #
  subst Hv
  ihave %Hok := cfgIs_ok' γ.rab cf $$ Hcfg
  have hn5 : cf.n ≤ maxS := by have := Hok; unfold RCfg.Ok at this; unfold maxS; omega
  wp_auto
  wp_if_destruct
  · -- server `k` of the configuration's `n`
    have hkn : k < cf.n := by
      unfold maxS at hn5 hk
      word
    wp_apply wp_ProxyAddrs as %ps2 ⟨%L, Hps2, %HL⟩
    subst HL
    ihave %Hps20 := ownSlice_len _ _ _ $$ Hps2
    have hps2 : sint.Z ps2.len = (maxS : Int) := by
      obtain ⟨h1, h2⟩ := Hps20
      rw [List.length_map, List.length_range] at h1
      rw [h1]; exact (Int.toNat_of_nonneg h2).symm
    rw [ite_eq_left (by rw [hkz, hps2]; omega)]
    wp_apply wp_load_slice_index ps2 _ _ _ (proxyAddr k) (by omega) $$ [$Hps2] as -
    · ipureintro; rw [hkz]; simp only [Int.toNat_natCast]; exact range_map_get _ _ _ hk
    wp_apply wp_NetAddrs as %ns ⟨%L, Hns, %HL⟩
    subst HL
    ihave %Hns0 := ownSlice_len _ _ _ $$ Hns
    ihave %Hnwf := ownSlice_wf _ _ _ $$ Hns
    have hnsl : sint.Z ns.len = (maxS : Int) := by
      obtain ⟨h1, h2⟩ := Hns0
      rw [List.length_map, List.length_range] at h1
      rw [h1]; exact (Int.toNat_of_nonneg h2).symm
    have hnz : sint.Z (W64 (cf.n : Int)) = (cf.n : Int) := by unfold maxS at hn5; word
    simp only [confV]
    rw [ite_eq_left (by rw [hnz, show sint.Z (W64 0) = 0 from rfl]; have := Hnwf; omega)]
    ihave ⟨Hps, -⟩ := (ownSlice_split_all (W64 (cf.n : Int)) ns _ _
      ⟨by rw [hnz]; omega, by omega⟩).1 $$ Hns
    rw [show sint.nat (W64 (cf.n : Int)) = cf.n by unfold maxS at hn5; word, take_peers cf hn5]
    iapply fupd_wp
    imod ownSlice_persist _ _ _ $$ Hps with #Hps
    imodintro
    try wp_auto
    rw [show (⟨W64 cf.n, W64 cf.f, W64 cf.batch, W64 cf.bms, W64 cf.blocks⟩ :
      _root_.Perennial.rabia.examples.rabianet.Conf) = confV cf from rfl]
    wp_apply (serveAt.wp_proof wp_ServerInit wp_Prologue wp_ServerMain wp_configure wp_ProxyAddrs wp_NetAddrs γ cf k _ σ hkn)
      $$ [$Hpkg $Hcfg $Hcore $Hps $Hσ] as Hf
    iexfalso; iexact Hf
  · -- not a server of the configuration: sleep forever
    try wp_auto
    ihave HI : (True : IProp GF) $$ []
    · itrivial
    wp_for HI
    try wp_auto
    wp_apply time.wp_Sleep
    wp_for_post
    iframe

end proof

end Perennial.rabia.examples.rabianet
