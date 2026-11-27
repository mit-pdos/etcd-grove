/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/client/checkCompactRev.lean` (#50 F5,
`notes/etcd-dist-plan.md` §26). Lean-first (no Rocq counterpart).

compactwatch's `checkCompactRev` proof at the cluster's view: the client's `Watcher` (`watchClient_of_new`),
the watch's context (`WithTimeout(Background(), readTimeout)` with no metadata, `wp_WithTimeout_bgMd`), the
watch from revision 2 over `Watch_dist` with compact's read update (`cwReadAu`), `CompactRev` on its channel
(`isRespChan_of_state_cmp`); a compaction response's revision is the cluster's permit (`cmpOkOf_permit`: its
revision plus the retention `1` reached), which the KV invariant turns into a lower bound of the shared
history (`kvPfx_seen`); the latest `Get` from that bound (`wp_cliGetR`, `cwSeen`) reads at a revision at
least the compaction's plus one, so the check does not panic.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.checkCompactRev
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.WatchDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.CompactCallsDist
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.CompactRev
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.RespChan
public import Spec.go_etcd_io.etcd.client.v3.WithRev
public import Perennial.Spec.context.Background
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProofMode Net client go_etcd_io.etcd.server.v3.etcdserver
open github_com.mit_pdos.etcd_grove.examples.etcd.dist
open etcd_dist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
theorem checkCompactRev.wp_proof
    (wp_Background : context.Background.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (hWTMd : context.WithTimeoutBackgroundMd.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_WithRev : WithRev.spec (GF := GF) (hG := hG))
    (wp_Watch : Watch_dist.spec (GF := GF) (hG := hG))
    (wp_CompactRev : etcdstart.CompactRev.spec (GF := GF) (hG := hG))
    (wp_KV_Get : KV_Get_dist.spec (GF := GF) (hG := hG)) :
    checkCompactRev.spec (GF := GF) (hG := hG) := by
  intro π cl key eps V Γ γr γ γF γh σ₀ l0 hpk hkl hcr hAs
  wp_start as ⟨Hlt, #Hnc, #Hnp, #Hms, #Hkvi, #Hpfx, #Hcw, #Hf, #Hl0⟩
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  ihave #Pcom : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart $$ []
  · iPkgInit
  -- the client's `Watcher` and `KV`
  ihave ⟨%w, #Hwc⟩ := watchClient_of_new cl eps V Γ $$ [Hnc Hnp Hms]
  · iframe #
  ihave #Hwc' := Hwc
  iunfold watchClientAt at Hwc'
  icases Hwc' with ⟨-, -, #Hwf, -⟩
  ihave ⟨%api, #Hkc⟩ := kvClient_of_new cl eps V Γ $$ [Hnc Hnp Hms]
  · iframe #
  (try wp_auto)
  -- `cctx, ccancel := context.WithTimeout(context.Background(), readTimeout)`
  wp_apply wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bgMd hWTMd wp_ErrAny hAs _) $$ []
    as %cctx %ccd %ccancel ⟨#Hccancel, -, -, #Hcctx, #HcMd, -⟩
  ihave #HcO := metadata.outgoingCtxOkC_of_outMD cctx none $$ HcMd
  (try wp_auto)
  -- the watch's option, `WithRev(2)`
  wp_apply wp_WithRev (W64 2) as %f2 #Hf2
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %osl ⟨Hosl, -⟩
  ipersist Hosl
  (try wp_auto)
  generalize hosl : slice.mk osl _ _ = optsSl
  ihave #Hopts : optsAt optsSl ([withRevM (W64 2)] : List (OpFull → OpFull)) $$ []
  · iunfold optsAt
    iexists _
    iframe Hosl
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %i %f %g %Hf %Hg
    rcases i with _ | i
    · cases Hf; cases Hg; iexact Hf2
    · simp at Hf
  -- compact's read update
  ihave #Hau := cwReadAu (Gg := hG.goose_globalGS) Γ.kv γ γF γh σ₀ l0 key hpk $$ [Hpfx Hcw Hl0 Hf]
  · iframe #
  iunfold kvReadAu at Hau
  iunfold kvAu at Hau
  -- `cch := cli.Watcher.Watch(cctx, key, clientv3.WithRev(2))`
  wp_apply (wp_Watch cl w eps V Γ cctx ccd none key optsSl ([withRevM (W64 2)] : List (OpFull → OpFull))
      (W64 2) (fun σ => iprop(⌜cwSeen σ₀ l0 key σ⌝))) $$ [] as %wch %γw ⟨#Hsp, Hcons, Hcur⟩
  · iframe #
    isplitr
    · iapply EtcdGrove.context.watchCtx_of_isContext; isplitl [] <;> iassumption
    ipureintro; exact cw_watch_ok key hkl
  ihave #Hwch := etcdstart.isRespChan_of_state_cmp wch Γ.kv γw _
    (fun σ => iprop(⌜cwSeen σ₀ l0 key σ⌝)) iprop(True) $$ Hsp
  (try wp_auto)
  ihave Hcons : etcdWatchConsumer γw 0 (W64 2 - W64 1) $$ [Hcons Hcur]
  · unfold etcdWatchConsumer
    iexists []
    iframe Hcons Hcur
    ipureintro; rfl
  -- `crev, cok := etcdstart.CompactRev(cch)`
  wp_apply (wp_CompactRev _ wch γw (W64 2 - W64 1)) $$ [Hcons] as %crev %cok Hcr
  · iframe; iframe #
  (try wp_auto)
  wp_apply Hccancel
  (try wp_auto)
  cases cok
  · (try wp_auto)
    iapply HΦ; iframe Hlt
  (try wp_auto)
  ihave ⟨%c', %v, %r, Hok, %Hv⟩ := Hcr $$ %rfl
  iunfold etcdstart.stateCmpOk at Hok
  icases Hok with ⟨-, #Hcmp0⟩
  ihave #Hcmp : cmpOkOf Γ.kv crev $$ []
  · rw [← Hv.1]; iexact Hcmp0
  -- the response's permit: its revision plus the retention reached; a lower bound of the history
  ihave ⟨%Hpos, #Hlb⟩ := cmpOkOf_permit Γ.kv crev Hv.2 $$ Hcmp
  imod (kvPfx_seen Γ.kv compactPfx γ cwOk γh σ₀ γr (sint.Z crev + Γ.kv.cret)) $$ Hpfx Hkvi Hlb
    with ⟨%l, #Hl, %Hle⟩
  -- `lctx, lcancel := context.WithTimeout(...)`; `lresp, err := cli.Get(lctx, key)`
  wp_apply wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
    as %lctx %lcd %lcancel ⟨#Hlcancel, #Hlctx, #Hlce, -⟩
  (try wp_auto)
  ihave #Hau' := cwReadAu (Gg := hG.goose_globalGS) Γ.kv γ γF γh σ₀ l key hpk $$ [Hpfx Hcw Hl Hf]
  · iframe #
  ihave #Hnil := optsAt_nil (GF := GF)
  ihave #Hnil' := optsAt_res slice.nil [] iprop(True) $$ Hnil
  have hsz : opSizeOk (opGetModel key []) :=
    opSizeOk_opGetModel (K := 70) (E := 0) (V := 0) (optsKeep_nil _ _ _) hkl (by decide)
  wp_apply (wp_cliGetR wp_KV_Get cl api eps V Γ lctx lcd key slice.nil [] iprop(True)
      (fun σ => iprop(⌜cwSeen σ₀ l key σ⌝))
      ⟨by unfold opGetPanics opFold OpFull.newOp; simp, rfl⟩ rfl hsz)
    $$ [Hlt] as %lresp %lerr ⟨Hlt, -, Hget⟩
  · iframe Hlt
    iframe #
    try isplitl []
    try itrivial
    rw [show (opGetModel key []).base.sortSet = false from rfl]
    iapply sortNamesIf_false
  (try wp_auto)
  wp_apply Hlcancel
  icases Hget with (⟨%Hgerr, %mg, %σ, #Hmg, #HQ, %Hs⟩ | %Hgfail)
  rotate_left
  · obtain ⟨Hgerr, -⟩ := Hgfail
    cases lerr with
    | nil => exact absurd rfl Hgerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; iframe Hlt
  subst Hgerr
  icases HQ with %Hseen
  (try wp_auto)
  iunfold rangeRespMsg at Hmg
  icases Hmg with ⟨%Hnn', %h', %sl, %ps, #Hh', #Hhf', -⟩
  iunfold hdrFull at Hhf'
  icases Hhf' with ⟨%Hhn', -, -, #HrevF', -, -⟩
  -- the get read at a revision at least the compaction's plus one
  have hrv : sint.Z crev + 1 ≤ (σ.rev : Int) := by
    have h1 := Hseen.1.length_le
    have h2 := Hseen.2.1.rev_eq
    rw [hcr] at Hle
    omega
  have Hnlt : ¬ sint.Z mg.hdr.revision < sint.Z (crev + W64 1) := by
    have hfit := Hs.2.2
    rw [Hs.2.1]
    unfold kvRevFits at hfit
    have hc63 : sint.Z crev < 2 ^ 63 - 1 := by
      have : (σ.rev : Int) < 2 ^ 63 := by omega
      omega
    have : sint.Z (crev + W64 1) = sint.Z crev + 1 := by word
    rw [this]
    have : sint.Z (W64 (σ.rev : Int)) = σ.rev := by word
    rw [this]; omega
  wp_auto
  try simp only [Hnlt, decide_false, ↓reduceIte]
  wp_auto
  iapply HΦ; iframe Hlt

end proof

end etcd_dist_client
end EtcdGrove
end Perennial
