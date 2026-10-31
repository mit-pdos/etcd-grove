/-
**`putgetc`** (M2, 2026-10-27, `notes/m2-plan.md`): putget's file, for putget with the
auto-compactor on (`common.StartCompactingServer`, revision mode, retention 1); putget's history
below is the original's.

Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/putgetc/Main.lean` (item 9, stage 2,
2026-10-18; over the examples' shared start since 2026-10-22, D33). Lean-first (no Rocq
counterpart).

The steps: `Main`'s premises in the shared start's form (`common.bootPremise_of`,
`commonPremises`); the ghost state `NewServer` takes (`common.alloc1`); `common.StartCompactingServer` (the member's configuration with the auto-compactor on, `NewServer`, `Start`);
`common.Serve` (`v3rpc.Server`, `Listen`, `go gs.Serve(l)`) with the ghost step
`common.kv_served` (one gRPC slot; etcd's `Put` and `Range` registered at the address);
`common.NewClient` (`clientv3.New`); each call's context with the request timeout
(`context.WithTimeout(context.Background(), common.RequestTimeout)`, `client.wp_WithTimeout_bg`:
an `isContext` whose `Err()` returns client errors, cancelled after the call; since 2026-10-23,
`notes/client-timeouts-plan.md`; `context.Background()` alone, quiet, until then); the client's
invariant at the bootstrap log (`putGetInv_alloc_log`); `cli.Put` (`client_Put_own`, its flag),
`cli.Get` (`client_Get_own`: the first key-value's value is `v`); the check, on the reply's message
(`rangeRespMsg`), takes the `else` branch. Every step's error ends `Main` (`return`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.putgetc.Main
public import Spec.go_uber_org.zap.NewNop
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.StartCompactingServer
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.Serve
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.NewClient
public import Perennial.Spec.context.Background
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Alloc
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Served
public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet
public import Proof.go_etcd_io.etcd.client.v3.InvServerKV
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace putgetc

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.putgetc.Assumptions]

set_option maxHeartbeats 800000 in
theorem Main.wp_proof
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_StartCompactingServer : common.StartCompactingServer.spec (GF := GF) (hG := hG))
    (wp_Serve : common.Serve.spec (GF := GF) (hG := hG))
    (wp_NewClient : common.NewClient.spec (GF := GF) (hG := hG))
    (wp_Background : context.Background.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  intro CS CRE CEC N id ctxs boot Hbf Htb Hrb48 HrbN Hck Haf Hbuq Hrf Hdbo Hms hAs
  wp_start as ⟨Haddr, Htok, #Hprem⟩
  iunfold premises at Hprem
  icases Hprem with ⟨#Hboot, #Hmarsh, #Hzap, #Hsetlg, #Htd, #Hns, #Htk, #Hnrl⟩
  -- `Main`'s premises in the shared start's form
  ihave #Hb := common.bootPremise_of N [id] (LogEntry.toEntries boot 0) ctxs (putgetcDir id)
      go!"putgetc" go!"putgetc"
      (common.urls1 go!"putgetc" go!"127.0.0.1:23801" go!"127.0.0.1:23791") id cfgOk urlsOk
      (fun _ h => by obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h; exact ⟨h1, by rw [h2]; rfl, h3, h4, h5, h6⟩)
      (fun _ h => by obtain ⟨h1, h2, h3, h4⟩ := h; exact ⟨h1, h2, h3, h4⟩) $$ Hboot
  ihave #Hcom : common.commonPremises (GF := GF) $$ []
  · iunfold common.commonPremises; iframe #
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
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_NewNop as %lg %Hlg
  (try wp_auto)
  -- the ghost state `NewServer` takes (`alloc1`)
  have hblen0 : boot.length = 1 := by rw [Hbf.boot.1]; rfl
  imod (common.alloc1 id ctxs boot Hbf.idLow Hbf.boot Hbf.cc (putgetcDir id) (dirOne_member id _)
      (by omega) (by omega) (cmp := true)) $$ Hmarsh
    with ⟨%γ, %ρ, %E₀, %Φs, %γn, %Hal, Hmb, #Hnet, Hetcd⟩
  obtain ⟨hvs, hrule, hboot, hγn1, hγn2, hlog⟩ := Hal
  have hblen : (LogEntry.toEntries boot 0).length ≤ 2 ^ 60 := by
    simp [LogEntry.toEntries, hblen0]
  -- `StartCompactingServer("putgetc", "127.0.0.1:23801", clientAddr, retention, lg)`
  -- (2026-10-24, rafthttp stage 6d) the one-member directory is well formed
  have Hdirok : netDirOk (putgetcDir id) :=
    dirOne_ok id _ (by intro h; apply Hbf.idLow; rw [h]; decide) (by decide)
  wp_apply (wp_StartCompactingServer N go!"putgetc" go!"127.0.0.1:23801" go!"127.0.0.1:23791"
      (W64 1) lg
      (LogEntry.toEntries boot 0) ctxs (putgetcDir id) id γ ρ E₀ Φs γn Htb Hrb48 HrbN hvs
      hrule hboot hblen hγn1 hγn2 Hdirok
      (by simp [putgetcDir, dirOne]) Hlg (by decide) Hck Haf Hbuq Hdbo) $$ [Htok Hmb]
    as %srv %err Hr
  · iframe; iframe #
  icases Hr with (⟨%Herr, -⟩ | ⟨%Herr, Hup⟩)
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Herr
  wp_auto
  iunfold common.memberUp at Hup
  icases Hup with ⟨%E, %cfg, %γw, %HEc, #Hreq, #Hrd, Hgo, Hlg3, Hrslots, #Hwb, #Hsf, Hwpi,
    Hbemu, Hlts, Hlgs, Hrds, Hsts, Hbms, -, HWR⟩
  obtain ⟨HEa, HEo, HElg, HEtr, HEw⟩ := HEc
  -- `Serve(s, clientAddr)`, with etcd's KV calls registered at the address
  haveI := Hms
  wp_apply (wp_Serve srv go!"127.0.0.1:23791" E { ρ with wait := γw } ρ.rd cfg
      (fun cid mid _ => common.etcdKVAt go!"127.0.0.1:23791" E { ρ with wait := γw } ρ.rd cid mid)
      (by rw [HElg]; exact Hlg) HEtr HEw Hms Hbuq)
    $$ [Haddr Hlg3 Hbemu Hgo Hwpi HWR Hlts Hlgs Hrds Hsts Hrslots Hbms] as %serr Hs
  · iframe; iframe #
    iintro %gs %lis %cid %mid %R Hg
    iapply (common.kv_served srv E { ρ with wait := γw } ρ.rd gs lis go!"127.0.0.1:23791" cid mid
      R Hrb48 Hrf)
    iframe; iframe #
  icases Hs with (%Hserr | ⟨%Hserr, %cid, %mid, %R, #Hkv⟩)
  · cases serr with
    | nil => exact absurd rfl Hserr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Hserr
  wp_auto
  ihave #Hregs := common.etcdKVAt_regs go!"127.0.0.1:23791" E { ρ with wait := γw } ρ.rd cid mid
    rfl $$ Hkv
  -- `NewClient(clientAddr, lg)`
  wp_apply (wp_NewClient go!"127.0.0.1:23791" lg
      (EtcdGrove.client.srvWEnv R go!"127.0.0.1:23791" [] null null [] null default) Hlg
      (by unfold plainEndpoint; decide) Htb) as %cl %cerr Hcl
  icases Hcl with (⟨%Hcerr, #Hnc, -⟩ | %Hcfail)
  rotate_left
  · obtain ⟨Hcerr, -⟩ := Hcfail
    cases cerr with
    | nil => exact absurd rfl Hcerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Hcerr
  wp_auto
  -- `pctx, pcancel := context.WithTimeout(context.Background(), common.RequestTimeout)`
  wp_apply wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
    as %pctx %pcd %pcancel ⟨#Hpcancel, #Hpctx, #Hpce, -⟩
  (try wp_auto)
  -- the client's invariant, the floor, no options
  rw [kvModelSt_boot _ (fun _ _ => True) _ _ (srvBootLogOk_of_BootLog _ _ _ Hbf.boot)]
  imod (client.putGetInv_alloc_log ρ.rd (kvModel ρ.rd.kv (bootEntries (LogEntry.toEntries boot 0))) go!"k" go!"v" ⊤)
    $$ Hetcd with ⟨%γf, #Hinv⟩
  imod mvcc.idxCert_nil (GF := GF) E.γ.idx with #HF0
  ihave #Hnil : optsAt (GF := GF) slice.nil [] $$ []
  · iunfold optsAt
    iexists ([] : List GoFunc)
    isplitl
    · iapply ownSlice_nil
    isplitl
    · ipureintro; rfl
    imodintro
    iintro %i %f %g %Hf %Hg
    simp at Hf
  -- `cli.Put(ctx, "k", "v")`
  wp_apply (client.client_Put_own cl go!"127.0.0.1:23791" _ E ρ.rd γf cid mid
      pctx pcd go!"k" go!"v" slice.nil []
      (opSizeOk_opPutModel (K := 1) (E := 0) (V := 1) (optsKeep_nil _ _ _) (by decide) (by decide)
        (by decide))) as %presp %perr Hput
  · iframe #
  -- `pcancel()`
  (try wp_auto)
  wp_apply Hpcancel
  icases Hput with (⟨%Hperr, -, #Hflag⟩ | %Hpfail)
  rotate_left
  · obtain ⟨Hperr, -⟩ := Hpfail
    cases perr with
    | nil => exact absurd rfl Hperr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Hperr
  (try wp_auto)
  -- `gctx, gcancel := context.WithTimeout(context.Background(), common.RequestTimeout)`
  wp_apply wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
    as %gctx %gcd %gcancel ⟨#Hgcancel, #Hgctx, #Hgce, -⟩
  (try wp_auto)
  -- `cli.Get(gctx, "k")`
  imod monoNatLbOwn_0 (GF := GF) ρ.rd.committed with #Hc0
  wp_apply (client.client_Get_own cl go!"127.0.0.1:23791" _ E ρ.rd γf (W64 0) cid mid
      gctx gcd go!"k" go!"v" slice.nil []
      (opSizeOk_opGetModel (K := 1) (E := 0) (V := 0) (optsKeep_nil _ _ _) (by decide) (by decide))) as %gresp %gerr Hget
  · iframe #
    iunfold committedAtLeast
    iExactEq Hc0; rfl
  -- `gcancel()`
  (try wp_auto)
  wp_apply Hgcancel
  icases Hget with (⟨%Hgerr, %m, #Hm, %Hv⟩ | %Hgfail)
  rotate_left
  · obtain ⟨Hgerr, -⟩ := Hgfail
    cases gerr with
    | nil => exact absurd rfl Hgerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Hgerr
  (try wp_auto)
  iunfold rangeRespMsg at Hm
  icases Hm with ⟨%Hnn, %h, %sl, %ps, #Hh, #Hhf, #Hkvf, #Hsl, #Hkvs, #Hmore, #Hcount⟩
  -- the reply's first key-value holds `v`
  obtain ⟨kv0, Hkv0, Hval0⟩ : ∃ kv0, m.kvs[0]? = some kv0 ∧ kv0.value = go!"v" := by
    cases h : m.kvs with
    | nil => simp [h] at Hv
    | cons x xs => simp [h] at Hv; exact ⟨x, rfl, Hv⟩
  iunfold txn.kvsIs at Hkvs
  icases Hkvs with ⟨%Hlen, #Hall⟩
  obtain ⟨p0, Hp0⟩ : ∃ p0, ps[0]? = some p0 := by
    have : 0 < ps.length := by
      rw [Hlen]
      cases h : m.kvs with
      | nil => simp [h] at Hkv0
      | cons x xs => simp
    exact ⟨ps[0], List.getElem?_eq_getElem this⟩
  ihave #Hkv := Hall $$ %0 %p0 %kv0 %Hp0 %Hkv0
  iunfold txn.kvIs at Hkv
  icases Hkv with ⟨%kSl, %vSl, -, -, -, -, -, #HvF, #HvS, -⟩
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  have Hne : decide (sl.len = W64 0) = false := by
    rw [decide_eq_false_iff_not]
    intro h
    have hl := Hsll.1
    rw [h] at hl
    have : 0 < ps.length := List.length_pos_of_mem (List.mem_of_getElem? Hp0)
    rw [hl] at this
    exact absurd this (by decide)
  wp_auto
  simp only [Hne]
  wp_auto
  have Hbnd : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len := by
    have := Hsll.1
    have : 0 < ps.length := List.length_pos_of_mem (List.mem_of_getElem? Hp0)
    constructor <;> word
  simp only [Hbnd, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index _ (sint.Z (W64 0)) _ DFrac.discard p0 Hbnd.1 $$ [Hsl] as -
  · iframe Hsl; ipureintro; exact Hp0
  wp_apply wp_bytes_to_string vSl kv0.value DFrac.discard $$ [HvS] as -
  · iframe #
  rw [Hval0]
  wp_auto
  iapply HΦ; itrivial

end proof

end putgetc
end EtcdGrove
end Perennial
