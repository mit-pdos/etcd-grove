/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/Main.lean` (stage 6g of
`notes/k8s-etcd3-plan.md`). Lean-first (no Rocq counterpart).

As `linkvtxn/Main.lean` to the client (the shared start, `etcdstart.StartServer` and `etcdstart.Serve`,
at `k8setcd3`'s configuration), then: `kubernetes.New` (a write sent at most once: the member is refusal-free, D29), the seeding (`seedInv` over etcd's
start state, `seed`, cancelled at the seeded state), the store's history at the seeded state
(`histAuth_seed`), `newStore` (the seed, the features, `etcd3.New` with the driver's contract), the
instance's invariant at the seeded state (`kInv_seed`), (stage E of 7f-6) the member's watch
registration at its address (`etcdstart.kvWatch_served` at `Serve`), the client's watcher over its KV
(`clientWatchOk_of_regs` at the one member), so the store's watch fields, and
`Check(s, st0, h0, clients, ops, watchers, wops, 0)`, which returns `Ok` (`timeout = 0`), so the
panic on `Illegal` is not taken. Every step's error ends `Main` with `Unknown`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Check
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.newStore
public import Spec.go_etcd_io.etcd.client.v3.kubernetes.New
public import Spec.context.ErrAny
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.WatchQ
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.WatchEnvN
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Boot
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Contract
public import Spec.go_uber_org.zap.NewNop
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartServer
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Serve
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Alloc
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Served
public import Spec.go_etcd_io.etcd.client.v3.New
public import Perennial.Spec.context.Background
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NewServerAlloc
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BuildGap
public import Proof.go_etcd_io.etcd.client.v3.ServeFromStart
public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet
public import Proof.go_etcd_io.etcd.client.v3.InvServerKV
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.WatchServedLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.SeedRun

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

set_option maxHeartbeats 3200000 in
theorem Main.wp_proof
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_StartServer : etcdstart.StartServer.spec (GF := GF) (hG := hG))
    (wp_Serve : etcdstart.Serve.spec (GF := GF) (hG := hG))
    (wp_kNew : kubernetes.New.spec (GF := GF) (hG := hG))
    (wp_newStore : newStore.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_Check : Check.spec (GF := GF) (hG := hG))
    (hne : mvcc.api.names_nonempty.law)
    (Hp : mvcc.api.persistent.law (GF := GF)) (Hr : mvcc.api.mvccState_reachable.law (GF := GF))
    -- (premises to axioms, 2026-11-24: until then the premise `bootMarshal`) `proto.Marshal`'s spec at a boot conf change
    (wp_MarshalBoot : proto.MarshalBootConfChange.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  intro CS EK RT SC ST VA CR CE N id ctxs boot clients ops watchers wops Hbf Htb HLv Hrb48 HrbN HwbN Haf
    Hbuq Hrf Hdbo Hms hAs hse Hty H0 Hw0 H31 Hops Hwops Hmul
  wp_start as ⟨Hstart, Htok, #Hprem⟩
  -- (hub step 7) the client address's listen right, out of the member's start bundle (to `Serve`)
  icases etcdstart.memberStartRes_client _ _ _ rfl $$ Hstart with ⟨Haddr, Hstart⟩
  iunfold premises at Hprem
  iunfold etcdstart.premises at Hprem
  icases Hprem with #Hboot
  -- (premises to axioms, 2026-11-24: until then the premise `bootMarshal`) `proto.Marshal`'s bytes at the
  -- bootstrap log's conf changes, from its trust-boundary spec and the log's bytes (`Hbf.wire`)
  ihave #Hpp : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto $$ []
  · iPkgInit
  ihave #Hmarsh := bootMarshal_of_spec wp_MarshalBoot _ _ _ Hbf.wire $$ Hpp
  -- `Main`'s premises in the shared start's form
  ihave #Hb := etcdstart.bootPremise_of N [id] (LogEntry.toEntries boot 0) ctxs (k8setcd3Dir id) go!"k8setcd3" go!"k8setcd3"
      (etcdstart.urls1 go!"k8setcd3" go!"127.0.0.1:23906" go!"127.0.0.1:23896") id cfgOk urlsOk
      (fun _ h => h)
      (fun _ h => h) $$ Hboot
  -- `context`'s `closedchan`, from its package's fact
  ihave #Hcci : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  -- the imports' package facts
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  ihave #Pv3 : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc $$ []
  · iPkgInit
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_NewNop as %lg #Hlgz
  ihave %Hlg := zapLoggerOk_ne_null lg $$ Hlgz
  (try wp_auto)
  -- the ghost state `NewServer` takes (`alloc1`)
  have hblen0 : boot.length = 1 := by rw [Hbf.boot.1]; rfl
  imod (etcdstart.alloc1_false hne id ctxs boot Hbf (k8setcd3Dir id) (dirOne_member id _)
      (by omega) (by omega)) $$ Hmarsh
    with ⟨%γ, %ρ, %E₀, %Φs, %γn, %Hal, Hmb, #Hnet, Hetcd⟩
  obtain ⟨hvs, hrule, hboot, hγn1, hγn2, hlog, -⟩ := Hal
  have hblen : (LogEntry.toEntries boot 0).length ≤ 2 ^ 60 := by
    simp [LogEntry.toEntries, hblen0]
  -- `StartServer("k8setcd3", "127.0.0.1:23906", clientAddr, lg)`
  -- (2026-10-24, rafthttp stage 6d) the one-member directory is well formed
  have Hdirok : netDirOk (k8setcd3Dir id) :=
    dirOne_ok id _ (by intro h; apply Hbf.idLow; rw [h]; decide) (by decide)
  -- (hub step 7) no peer address: the start bundle is the fresh bundle at the network `γn`
  ihave Hfresh := etcdstart.memberStartRes_fresh _ _ γn rfl $$ Hstart
  wp_apply (wp_StartServer N go!"k8setcd3" go!"127.0.0.1:23906" go!"127.0.0.1:23896" lg (LogEntry.toEntries boot 0) ctxs
      (k8setcd3Dir id) id γ ρ E₀ Φs γn .none Htb Hrb48 HrbN HwbN hvs
      hrule hboot hblen hγn1 hγn2 Hdirok
      (by simp [k8setcd3Dir, etcdstart.dir1, dirOne]) (rafthttp.bootCfg_dirOne id _) (by decide) (by decide) (by decide) (by decide) Haf Hbuq Hdbo) $$ [Htok Hmb Hfresh]
    as %srv %err Hr
  · iframe; iframe #
  icases Hr with (⟨%Herr, -⟩ | ⟨%Herr, Hup, -⟩)
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    simp only [github_com.anishathalye.porcupine.Unknown]
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  subst Herr
  wp_auto
  icases etcdstart.memberUp_served _ _ _ _ _ _ _ $$ Hup with ⟨%E, %cfg, %γw, %HEc, #Hreq, #Hrd,
    #Hsf, Hgo, Hlg3, Hbemu, #Hwb, Hstk, -, -⟩
  obtain ⟨HEa, HEo, HElg, HEtr, HEw⟩ := HEc
  -- `Serve(s, clientAddr)`: (D29) the member never refuses (authentication off, a voter, the
  -- members' axiom), and etcd's KV calls registered at the address
  haveI := Hms
  ihave ⟨%HsvOff, #HreqM, #HrdM, #Hlb⟩ := etcdstart.serveViews_off srv E { ρ with wait := γw } ρ.rd
    $$ []
  · iframe #
  ihave #HzlgC : zapLoggerOk cfg.Logger' $$ []
  · rw [HElg]; iexact Hlgz
  wp_apply (wp_Serve srv go!"127.0.0.1:23896" E { ρ with wait := γw } ρ.rd cfg
      (fun cid mid R => iprop(etcdstart.etcdKVAt go!"127.0.0.1:23896" E { ρ with wait := γw } ρ.rd cid mid ∗
        etcdstart.watchRegAt go!"127.0.0.1:23896" srv E ρ.rd R ∗
        ⌜noRefusalAt go!"127.0.0.1:23896"⌝)))
    $$ [Haddr Hlg3 Hbemu Hgo Hstk] as %serr Hs
  · iframe; iframe #
    isplitr
    · ipureintro; exact ⟨HEtr, HEw, Hms, Hbuq, HsvOff.2, Htb⟩
    iintro %gs %lis %cid %mid %R Hg
    rw [HsvOff.1]
    ihave Hg := etcdstart.grpcUpM_false _ _ _ _ _ _ _ _ _ _ $$ Hg
    imod (etcdstart.kvWatch_served Hp Hr srv E { ρ with wait := γw } ρ.rd cfg gs lis
      go!"127.0.0.1:23896" cid mid R Hrb48 Hrf rfl HLv Hms
      (by rw [sync.rwmutex.actualMaxReaders_unseal]; omega)) $$ [Hg Hstk] with ⟨Hserv, #Hkv, #Hksa, #Hwr⟩
    · iframe; iframe #
    -- (D29) the member never refuses: the server now at its address is etcd's, authentication off
    ihave %Hnr := EtcdGrove.etcd_noRefusal_srv go!"127.0.0.1:23896" srv E { ρ with wait := γw } HEo $$ [Hksa]
    · iframe #
    imodintro
    iframe Hserv Hkv Hwr
    ipureintro; exact Hnr
  icases Hs with (%Hserr | ⟨%Hserr, %cid, %mid, %R, #Hkv, #Hwr, %Hnr⟩)
  · cases serr with
    | nil => exact absurd rfl Hserr
    | ok ei => ?_
    simp only [github_com.anishathalye.porcupine.Unknown]
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  subst Hserr
  wp_auto
  iunfold etcdstart.etcdKVAt at Hkv
  icases Hkv with ⟨#HPut, #HRange, #HDel, #HTxn, #HCmp⟩
  -- `kubernetes.New(Config{Endpoints: {clientAddr}, Logger: lg, MaxUnaryRetries: 1})`
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %eps ⟨Heps, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  imod ownSlice_persist _ _ _ $$ Heps with #Heps
  ihave #Pkc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.kubernetes $$ []
  · iPkgInit
  -- the one member, as the client reaches it, and its watch environment (stage E)
  let x : client.SrvAt GF := ⟨go!"127.0.0.1:23896", E, ρ.rd, cid, mid⟩
  let m0 : etcdstart.WMem GF := (go!"127.0.0.1:23896", R, etcdstart.srvWOf E ρ.rd false)
  let V : client.WEnv GF := etcdstart.watchEnvL m0 (k8s_etcd3N.wmemsOf [x] [(srv, R)]) ρ.rd
    k8s_etcd3N.wpfx
  haveI : ThreadBoundLe GF (2 ^ 28) := ⟨Htb⟩
  wp_apply (wp_kNew _ [go!"127.0.0.1:23896"] V (fun _ => iprop(True))) $$ [] as %kc %cerr Hcl
  · iframe #
    iunfold clientCfgOk
    simp only
    iframe #
    isplitr
    · isplitr
      · iexists 0; iapply noProxyOptsAt_nil
      ipureintro
      refine ⟨?_, ?_⟩
      · exact plainEndpoints_singleton _ (by unfold plainEndpoint; decide)
      · simp [Hlg]
    iapply clientAuthPre_anon; rfl
  icases Hcl with (⟨%Hcerr, %cl, #Hkc, #Hnc, -⟩ | %Hcfail)
  rotate_left
  · cases cerr with
    | nil => exact absurd rfl Hcfail
    | ok ei => ?_
    simp only [github_com.anishathalye.porcupine.Unknown]
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  subst Hcerr
  wp_auto
  -- (D29) a write sent at most once: the member is refusal-free
  ihave #Hone' : client.clientWriteOnce (GF := GF) cl [go!"127.0.0.1:23896"] $$ []
  · iunfold client.clientWriteOnce; ipureintro
    intro a ha; simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at ha
    subst ha; exact Hnr
  -- the one member's KV specs
  ihave #Hreg1 : client.kvRegsAt x $$ []
  · iunfold client.kvRegsAt
    iframe #
  -- the seeding, from the server's start state (`σb`: no key, revision `1`)
  have hboot0 : kvModelSt ρ.rd.kv (bootEntries (LogEntry.toEntries boot 0)) = σb := by
    have h : kvModel ρ.rd.kv (bootEntries (LogEntry.toEntries boot 0)) = [[], []] := by
      unfold kvModel
      rw [linkv.kvRaftOf_boot _ _ _ (fun _ _ => True) [id] (LogEntry.toEntries boot 0) (srvBootLogOk_of_BootLog _ _ _ Hbf.boot), hlog]
    rw [kvModelSt_boot _ (fun _ _ => True) _ (LogEntry.toEntries boot 0) (srvBootLogOk_of_BootLog _ _ _ Hbf.boot), h]; rfl
  imod (seedInv_alloc ρ.rd.kv σb ⊤) $$ [Hetcd] with ⟨%γs, #Hsi, Hs⟩
  · rw [← hboot0]; iexact Hetcd
  ihave #Hkc' := Hkc
  iStructNamed Hkc'
  (try wp_auto)
  ihave #Hregs1 : ([∗list] y ∈ [x], client.kvRegsAt y) $$ []
  · iapply BigSepL.bigSepL_singleton.2; iexact Hreg1
  ihave #Hsi1 : ([∗list] y ∈ [x], seedInv γs y.γr.kv) $$ []
  · iapply BigSepL.bigSepL_singleton.2; iexact Hsi
  imod (histAuth_seed (GF := GF)) with ⟨%γh, Hhist, #Hsr⟩
  -- `newStore(kc)`: the seed, the features, `etcd3.New`
  wp_apply (wp_newStore kc cl [x] V γs γh hAs (by simp) (by omega)) $$ [Hs] as %s %st0 %h0 %ok Hns
  · simp only [List.map_cons, List.map_nil]
    iframe #
    iframe Hs
  icases Hns with (%Hok | ⟨%Hok, Hs, Hst0, ⟨%hs, #Hh0, Hhs⟩, #Hrs, #Hwl, %sp, %mt, %lt, %Hsp,
    #Hstore, #Hsw⟩)
  · subst Hok
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  subst Hok Hsp
  wp_auto
  iclear Hregs1 Hsi1
  imod (seedInv_cancel γs ρ.rd.kv σs2) $$ [Hs] with Hetcd
  · iframe #
    iframe Hs
  -- the driver's invariant at the seeded state
  imod (kInv_seed ρ.rd.kv (storeCfgD kc cl [x] V mt lt γh) rfl rfl ⊤) $$ [Hetcd Hhist] with
    ⟨%γ, #Hinv, Hks⟩
  · simp only [storeCfgD]
    iframe
    iexact Hsr
  -- (stage E) the client's watcher over the member's KV, so the store's watch fields
  ihave #Hone1 := one_read_au γ (storeCfgD kc cl [x] V mt lt γh) g0s ρ.rd.kv $$ Hinv
  ihave #Pio : isPkgInit (PROP := IProp GF) pkg_id.io $$ []
  · iPkgInit
  ihave #Heo : client.eofOk (GF := GF) $$ []
  · iapply (client.eofOk_of_init hAs) $$ Pio
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Hwregs : ([∗list] sv; w ∈ [x]; [(srv, R)], etcdstart.watchRegAt sv.addr w.1 sv.E sv.γr w.2 ∗
      isServerRead w.1 sv.E sv.γr) $$ []
  · iapply BigSepL2.bigSepL2_singleton.2
    iframe #
  have hmem1 : ∀ sv ∈ [x], v3rpc.memberOf ρ.rd.raft ρ.rd.kv sv.γr := by
    intro sv hsv
    rw [List.mem_singleton] at hsv
    subst hsv
    exact v3rpc.memberOf_of_eq _ _ _ rfl rfl rfl rfl
  have hsame1 : ∀ sv ∈ [x], kvSame sv.γr.kv ρ.rd.kv := by
    intro sv hsv
    rw [List.mem_singleton] at hsv
    subst hsv
    exact kvSame_refl _
  ihave #Hcw := k8s_etcd3N.clientWatchOk_of_regs wp_ErrAny hAs cl V [x] [(srv, R)] ρ.rd m0 ρ.rd.kv
    rfl (by simp) (by simp) hmem1 hsame1 (kvSame_refl _) hlog (by omega)
    $$ [Pcli Ppb Pctx Heo Hnc Hwregs Hone1]
  · simp only [List.map_cons, List.map_nil]
    iframe #
  ihave #Hswk := Hsw $$ Hcw
  -- `Check(s, st0, h0, clients, ops, watchers, wops, 0)`
  ihave Hst0 : storeOwn st0 g0s.st $$ [Hst0]
  · iExactEq Hst0; rfl
  ihave Hhs : [∗list] x;g ∈ hs;g0s.hist, storeOwn x g $$ [Hhs]
  · iExactEq Hhs; rfl
  ihave #Pst : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 $$ []
  · iPkgInit
  ihave #Hpd : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 $$ []
  · iPkgInit
  wp_apply (wp_Check γ sp (storeCfgD kc cl [x] V mt lt γh) g0s ρ.rd.kv st0 h0 hs clients ops watchers
      wops (W64 0) rfl rfl rfl rfl rfl hAs hse (by omega)
      (by intro y hy; simp only [storeCfgD, List.mem_cons, List.not_mem_nil, _root_.or_false] at hy
          subst hy; exact Hnr)
      (by simp [storeCfgD]) (by omega) H0 Hw0 H31 Hops Hwops Hmul
      (by rw [g0s_len, σs2_rev]; show st3.items.length + 3 < _; rw [st3_items]; simp)
      (by simp [g0s, st3]) runOk_g0s)
    $$ [Hks Hst0 Hhs] as %r %hr
  · rw [show (storeCfgD kc cl [x] V mt lt γh).ms = [x] from rfl]
    iframe #
    iframe Hks Hst0 Hhs
    iapply BigSepL.bigSepL_nil.2; itrivial
  have hok : r = go!"Ok" := hr.2 (by decide)
  subst hok
  wp_auto
  iapply HΦ; ipureintro; left; rfl

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
