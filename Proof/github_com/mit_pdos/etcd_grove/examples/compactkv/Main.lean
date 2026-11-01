/-
**`compactkv`** (the client's `kv.Compact`, 2026-11-01): putgetc's file, for putgetc under
compaction pressure (`common.StartCompactingServer`, revision mode, retention 1; five rounds of a
put of the round's key, a client compaction at the revision before it, a get of the key, and
from the second round a get of the previous round's key at that round's put's revision,
`client.client_Get_kv` with `getAtAu_round`: if `nil`, the previous put's value, by the rounds'
invariant's history; an error skips the check);
putgetc's and putget's history below is the originals'.

Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/compactkv/Main.lean` (item 9, stage 2,
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

public import Spec.github_com.mit_pdos.etcd_grove.examples.compactkv.Main
public import Spec.go_uber_org.zap.NewNop
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.StartCompactingServer
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.Serve
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.NewClient
public import Spec.go_etcd_io.etcd.client.v3.WithRev
public import Perennial.Spec.context.Background
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Alloc
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Served
public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet
public import Proof.github_com.mit_pdos.etcd_grove.examples.compactkv.RoundCalls
public import Proof.go_etcd_io.etcd.client.v3.KMClient
public import Proof.go_etcd_io.etcd.client.v3.InvServerKV
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace compactkv

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof

/-- The rounds' keys, in order (`Main`'s `keys`). -/
abbrev keysL [GooseExts] : List GoString :=
  [go!"k1", go!"k2", go!"k3", go!"k4", go!"k5"]

variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.compactkv.Assumptions]

/-- **The previous round's key and put's revision** (`Main`'s `prevKey`, `prevRev`): none (`0`), or
a round's key, at most 2 bytes, whose put first fired at a revision at most `pr`, past `0`. -/
def prevOk (γl : GName) (pk : GoString) (pr : w64) : IProp GF :=
  iprop(⌜pr = W64 0⌝ ∨ ∃ (j r0 : Nat), ⌜keysL[j]? = some pk ∧ (r0 : Int) ≤ sint.Z pr ∧
    1 ≤ sint.Z pr ∧ pk.length ≤ 2⌝ ∗ monoListIdxOwn γl j r0)

instance prevOk_persistent (γl : GName) (pk : GoString) (pr : w64) :
    Persistent (prevOk (GF := GF) γl pk pr) := by
  unfold prevOk; infer_instance

set_option maxHeartbeats 800000 in
set_option maxRecDepth 8192 in
theorem Main.wp_proof
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_StartCompactingServer : common.StartCompactingServer.spec (GF := GF) (hG := hG))
    (wp_Serve : common.Serve.spec (GF := GF) (hG := hG))
    (wp_NewClient : common.NewClient.spec (GF := GF) (hG := hG))
    (wp_Background : context.Background.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_WithRev : WithRev.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  intro CS CRE CEC N id ctxs boot Hbf Htb Hrb48 HrbN Hck Haf Hbuq Hrf Hdbo Hms hAs
  wp_start as ⟨Haddr, Htok, #Hprem⟩
  iunfold premises at Hprem
  icases Hprem with ⟨#Hboot, #Hmarsh, #Hzap, #Hsetlg, #Htd, #Hns, #Htk, #Hnrl⟩
  -- `Main`'s premises in the shared start's form
  ihave #Hb := common.bootPremise_of (N + N) [id] (LogEntry.toEntries boot 0) ctxs (compactkvDir id)
      go!"compactkv" go!"compactkv"
      (common.urls1 go!"compactkv" go!"127.0.0.1:23804" go!"127.0.0.1:23794") id cfgOk urlsOk
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
  imod (common.alloc1 id ctxs boot Hbf.idLow Hbf.boot Hbf.cc (compactkvDir id) (dirOne_member id _)
      (by omega) (by omega) (cmp := true)) $$ Hmarsh
    with ⟨%γ, %ρ, %E₀, %Φs, %γn, %Hal, Hmb, #Hnet, Hetcd⟩
  obtain ⟨hvs, hrule, hboot, hγn1, hγn2, hlog, hkc⟩ := Hal
  have hblen : (LogEntry.toEntries boot 0).length ≤ 2 ^ 60 := by
    simp [LogEntry.toEntries, hblen0]
  -- `StartCompactingServer("compactkv", "127.0.0.1:23804", clientAddr, retention, lg)`
  -- (2026-10-24, rafthttp stage 6d) the one-member directory is well formed
  have Hdirok : netDirOk (compactkvDir id) :=
    dirOne_ok id _ (by intro h; apply Hbf.idLow; rw [h]; decide) (by decide)
  wp_apply (wp_StartCompactingServer N go!"compactkv" go!"127.0.0.1:23804" go!"127.0.0.1:23794"
      (W64 1) lg
      (LogEntry.toEntries boot 0) ctxs (compactkvDir id) id γ ρ E₀ Φs γn Htb Hrb48 HrbN hvs
      hrule hboot hblen hγn1 hγn2 Hdirok
      (by simp [compactkvDir, dirOne]) Hlg (by decide) Hck Haf Hbuq Hdbo) $$ [Htok Hmb]
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
  wp_apply (wp_Serve srv go!"127.0.0.1:23794" E { ρ with wait := γw } ρ.rd cfg
      (fun cid mid _ => common.etcdKVAt go!"127.0.0.1:23794" E { ρ with wait := γw } ρ.rd cid mid)
      (by rw [HElg]; exact Hlg) HEtr HEw Hms Hbuq)
    $$ [Haddr Hlg3 Hbemu Hgo Hwpi HWR Hlts Hlgs Hrds Hsts Hrslots Hbms] as %serr Hs
  · iframe; iframe #
    iintro %gs %lis %cid %mid %R Hg
    iapply (common.kv_served srv E { ρ with wait := γw } ρ.rd gs lis go!"127.0.0.1:23794" cid mid
      R Hrb48 Hrf rfl)
    iframe; iframe #
  icases Hs with (%Hserr | ⟨%Hserr, %cid, %mid, %R, #Hkv⟩)
  · cases serr with
    | nil => exact absurd rfl Hserr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Hserr
  wp_auto
  ihave #Hregs := common.etcdKVAt_regs go!"127.0.0.1:23794" E { ρ with wait := γw } ρ.rd cid mid
    rfl $$ Hkv
  -- `NewClient(clientAddr, lg)`
  wp_apply (wp_NewClient go!"127.0.0.1:23794" lg
      (EtcdGrove.client.srvWEnv R go!"127.0.0.1:23794" [] null null [] null default) Hlg
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
  -- the client's `KV`: a client of etcd's KV (`isKv`), from the member's registrations
  ihave #Hnc' := Hnc
  iunfold isNewClient at Hnc'
  icases Hnc' with ⟨-, -, ⟨%api, #Hkvf, #Hkvo⟩, -⟩
  imod (client.isKv_of_regs api [go!"127.0.0.1:23794"] E ρ.rd cid mid ρ.rd.kv (kvSame_refl _)
      (by omega)) $$ [Hkvo] with #Hisk
  · iframe Hkvo
    iapply client.kvRegs_one
    iexact Hregs
  -- the rounds' invariant at the bootstrap log
  rw [kvModelSt_boot _ (fun _ _ => True) _ _ (srvBootLogOk_of_BootLog _ _ _ Hbf.boot)]
  imod (roundsInv_alloc ρ.rd (kvModel ρ.rd.kv (bootEntries (LogEntry.toEntries boot 0))) keysL
      go!"v" ⊤ (by
        have h := (kvRaftOf_extends ρ.rd.kv.c0 ρ.rd.kv.ch0 ρ.rd.kv.log0
          (bootEntries (LogEntry.toEntries boot 0))).length_le
        unfold kvModel; rw [hlog] at h ⊢; simpa using h)) $$ Hetcd with ⟨%γf, %γl, #Hinv⟩
  imod (monoNatLbOwn_0 (GF := GF) γf) with #Hlb0
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
  -- `keys := []string{"k1", ..., "k5"}`
  wp_apply (wp_slice_literal (V := GoString) keysL)
  isplitr
  · ipureintro; rfl
  iintro %ksl ⟨Hksl, -⟩
  (try wp_auto)
  ipersist Hksl
  -- the rounds: `for _, k := range keys { ... }`
  -- the previous round's key and put's revision: none (`0`), or a round's key whose first firing
  -- is at most that revision
  ihave IH : (∃ (n : w64) (kv pk : GoString) (pr : w64),
      "i" ∷ i_ptr ↦ n ∗ "k" ∷ k_ptr ↦ kv ∗ "pk" ∷ prevKey_ptr ↦ pk ∗ "pr" ∷ prevRev_ptr ↦ pr ∗
      "#Hlb" ∷ monoNatLbOwn γf (sint.nat n) ∗
      "#Hprev" ∷ prevOk γl pk pr ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ 5⌝ : IProp GF) $$ [i k prevKey prevRev]
  · iexists W64 0, _, _, _
    simp only [named]
    iframe
    isplitl
    · iExactEq Hlb0; rfl
    isplitl
    · iunfold prevOk; ileft; ipureintro; rfl
    ipureintro; constructor <;> decide
  wp_for IH
  have hsz5 : (go.arrayLiteralSize
      [KeyedElement none (ElementExpression go.string #(go!"k1")),
        KeyedElement none (ElementExpression go.string #(go!"k2")),
        KeyedElement none (ElementExpression go.string #(go!"k3")),
        KeyedElement none (ElementExpression go.string #(go!"k4")),
        KeyedElement none (ElementExpression go.string #(go!"k5"))]) = 5 := by
    simp [go.arrayLiteralSize]; rfl
  wp_if_destruct
  · -- a round: `k := keys[i]`
    have Hlt : sint.Z n < 5 := by simp only [hsz5] at Hif; word
    have hi : sint.nat n < keysL.length := by simp; word
    obtain ⟨kk, hk⟩ : ∃ kk, keysL[sint.nat n]? = some kk := ⟨_, List.getElem?_eq_getElem hi⟩
    simp only [hsz5]
    have Hlt5 : sint.Z n < sint.Z (W64 5) := by word
    have Hge0 : 0 ≤ sint.Z n := Hn.1
    simp only [Hlt5, Hge0, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index _ (sint.Z n) keysL DFrac.discard kk Hn.1 $$ [Hksl] as -
    · iframe Hksl; ipureintro; exact hk
    (try wp_auto)
    have hkl : kk.length ≤ 2 := by
      have : kk ∈ keysL := List.mem_of_getElem? hk
      simp [keysL] at this
      rcases this with rfl | rfl | rfl | rfl | rfl <;> decide
    -- `pctx, pcancel := context.WithTimeout(context.Background(), common.RequestTimeout)`
    wp_apply wp_Background
    (try wp_auto)
    wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
      as %pctx %pcd %pcancel ⟨#Hpcancel, #Hpctx, #Hpce, -⟩
    (try wp_auto)
    -- `presp, err := cli.Put(pctx, k, value)`: round `i`'s put
    ihave #Hau := putAu_round ρ.rd γf γl keysL go!"v" (sint.nat n) kk hk $$ [Hinv Hlb]
    · iframe #
    wp_apply (client.client_Put_kv cl api ρ.rd.kv true pctx pcd kk go!"v" slice.nil
        (fun σ => iprop(□ (monoNatLbOwn γf (sint.nat n + 1) ∗
          (∃ r0, monoListIdxOwn γl (sint.nat n) r0 ∗ ⌜r0 ≤ σ.rev + 1⌝) ∗ ⌜1 ≤ σ.rev⌝)))
        (opSizeOk_opPutModel (K := 2) (E := 0) (V := 1) (optsKeep_nil _ _ _) hkl (by decide)
          (by decide))) $$ [] as %presp %perr Hput
    · iframe #
      iunfold kvOpAu at Hau
      iunfold kvAu at Hau
      rw [show putWireOf (opPutModel kk go!"v" []) = client.putKeyOp kk go!"v" from rfl]
      iexact Hau
    -- `pcancel()`
    (try wp_auto)
    wp_apply Hpcancel
    icases Hput with (⟨%Hperr, %m, %σ, #Hm, #HQ, %Hs, #Hrv⟩ | ⟨%Hperr, -⟩)
    rotate_left
    · cases perr with
      | nil => exact absurd rfl Hperr
      | ok ei => ?_
      wp_auto
      wp_for_post
      (try wp_auto)
      iapply HΦ; itrivial
    subst Hperr
    icases HQ with ⟨#Hlb', ⟨%r0, #Hidx, %Hr0⟩, %Hσ1⟩
    (try wp_auto)
    -- `presp.Header.Revision - 1`: the revision before the put's, past `0`
    ihave #Hm' := Hm
    iunfold putRespMsg at Hm'
    icases Hm' with ⟨%Hnn, %h, %ppk, #Hh, #Hhf, -⟩
    iunfold hdrFull at Hhf
    icases Hhf with ⟨%Hhn, -, -, #HrevF, -, -⟩
    (try wp_auto)
    have Hr1 : 1 ≤ sint.Z (m.hdr.revision - W64 1) := by rw [Hs.1]; have := Hs.2.1.lt; word
    ihave #Hrv1 := kvRevLb_mono ρ.rd.kv m.hdr.revision (m.hdr.revision - W64 1)
      (by rw [Hs.1]; have := Hs.2.1.lt; word) $$ Hrv
    -- `cctx, ccancel := context.WithTimeout(...)`; `cli.Compact(cctx, ...)`, its outcome ignored
    wp_apply wp_Background
    (try wp_auto)
    wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
      as %cctx %ccd %ccancel ⟨#Hccancel, #Hcctx, #Hcce, -⟩
    (try wp_auto)
    wp_apply (client.client_Compact_kv cl api ρ.rd.kv true cctx ccd (m.hdr.revision - W64 1) Hr1
        hkc) $$ [] as %cresp %cerr -
    · iframe #
    (try wp_auto)
    wp_apply Hccancel
    (try wp_auto)
    -- `gctx, gcancel := context.WithTimeout(...)`; `resp, err := cli.Get(gctx, k)`
    wp_apply wp_Background
    (try wp_auto)
    wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
      as %gctx %gcd %gcancel ⟨#Hgcancel, #Hgctx, #Hgce, -⟩
    (try wp_auto)
    imod monoNatLbOwn_0 (GF := GF) ρ.rd.committed with #Hc0
    wp_apply (client_Get_round cl go!"127.0.0.1:23794" _ E ρ.rd γf γl keysL go!"v" (sint.nat n) kk hk
        (W64 0) cid mid gctx gcd slice.nil []
        (opSizeOk_opGetModel (K := 2) (E := 0) (V := 0) (optsKeep_nil _ _ _) hkl (by decide)))
        as %gresp %gerr Hget
    · iframe #
      iunfold committedAtLeast
      iExactEq Hc0; rfl
    (try wp_auto)
    wp_apply Hgcancel
    icases Hget with (⟨%Hgerr, %mg, #Hmg, %Hv⟩ | %Hgfail)
    rotate_left
    · obtain ⟨Hgerr, -⟩ := Hgfail
      cases gerr with
      | nil => exact absurd rfl Hgerr
      | ok ei => ?_
      wp_auto
      wp_for_post
      (try wp_auto)
      iapply HΦ; itrivial
    subst Hgerr
    (try wp_auto)
    iunfold rangeRespMsg at Hmg
    icases Hmg with ⟨%Hnn', %h', %sl, %ps, #Hh', #Hhf', #Hkvf', #Hsl, #Hkvs, #Hmore, #Hcount⟩
    -- the reply's first key-value holds `v`
    obtain ⟨kv0, Hkv0, Hval0⟩ : ∃ kv0, mg.kvs[0]? = some kv0 ∧ kv0.value = go!"v" := by
      cases h : mg.kvs with
      | nil => simp [h] at Hv
      | cons x xs => simp [h] at Hv; exact ⟨x, rfl, Hv⟩
    iunfold txn.kvsIs at Hkvs
    icases Hkvs with ⟨%Hlen, #Hall⟩
    obtain ⟨p0, Hp0⟩ : ∃ p0, ps[0]? = some p0 := by
      have : 0 < ps.length := by
        rw [Hlen]
        cases h : mg.kvs with
        | nil => simp [h] at Hkv0
        | cons x xs => simp
      exact ⟨ps[0], List.getElem?_eq_getElem this⟩
    ihave #Hkv0' := Hall $$ %0 %p0 %kv0 %Hp0 %Hkv0
    iunfold txn.kvIs at Hkv0'
    icases Hkv0' with ⟨%kSl, %vSl, -, -, -, -, -, #HvF, #HvS, -⟩
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
    have Hbnd0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len := by
      have := Hsll.1
      have : 0 < ps.length := List.length_pos_of_mem (List.mem_of_getElem? Hp0)
      constructor <;> word
    simp only [Hbnd0, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index _ (sint.Z (W64 0)) _ DFrac.discard p0 Hbnd0.1 $$ [Hsl] as -
    · iframe Hsl; ipureintro; exact Hp0
    wp_apply wp_bytes_to_string vSl kv0.value DFrac.discard $$ [HvS] as -
    · iframe #
    rw [Hval0]
    wp_auto
    -- the previous round's key and revision, for the next round: this round's
    ihave #Hprev' : prevOk γl kk m.hdr.revision $$ []
    · iunfold prevOk
      iright
      iexists sint.nat n, r0
      iframe Hidx
      ipureintro
      refine ⟨hk, ?_, ?_, hkl⟩ <;> (rw [Hs.1]; have := Hs.2.1.lt; word)
    -- `if prevRev != 0`: the get of the previous round's key at its put's revision
    iunfold prevOk at Hprev
    icases Hprev with (%Hpr0 | ⟨%j, %rj, %Hj, #Hidxj⟩)
    · subst Hpr0
      wp_auto
      -- the next round
      wp_for_post
      iframe
      iexists n + W64 1, kk, kk, m.hdr.revision
      simp only [named]
      iframe
      isplitl
      · rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word]; iexact Hlb'
      isplitl
      · iexact Hprev'
      ipureintro; constructor <;> word
    obtain ⟨Hjk, Hrj, Hpr1, Hpkl⟩ := Hj
    have Hpr : pr ≠ W64 0 := by intro h; rw [h] at Hpr1; exact absurd Hpr1 (by decide)
    simp only [Hpr, decide_false]
    wp_auto
    -- `octx, ocancel := context.WithTimeout(...)`
    wp_apply wp_Background
    (try wp_auto)
    wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
      as %octx %ocd %ocancel ⟨#Hocancel, #Hoctx, #Hoce, -⟩
    (try wp_auto)
    -- `oresp, err := cli.Get(octx, prevKey, clientv3.WithRev(prevRev))`
    wp_apply wp_WithRev pr as %fr #Hfr
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %osl ⟨Hosl, -⟩
    ipersist Hosl
    (try wp_auto)
    generalize hosl : slice.mk osl _ _ = optsSl
    ihave #Hopts : optsAt optsSl ([withRevM pr] : List (OpFull → OpFull)) $$ []
    · iunfold optsAt
      iexists _
      iframe Hosl
      isplitr
      · ipureintro; rfl
      imodintro
      iintro %i %f %g %Hf %Hg
      rcases i with _ | i
      · cases Hf; cases Hg; iexact Hfr
      · simp at Hf
    ihave #Hau' := getAtAu_round ρ.rd γf γl keysL go!"v" j rj pk Hjk $$ [Hinv Hidxj]
    · iframe #
    wp_apply (client.client_Get_kv cl api ρ.rd.kv true octx ocd pk pr optsSl
        (fun σ => iprop(⌜∀ r, rj ≤ r → r ≤ σ.rev →
          (mvcc.findKey pk (σ.at r).kvs).map EtcdKv.value = some go!"v"⌝))
        (opSizeOk_opGetModel (K := 2) (E := 0) (V := 0)
          (optsKeep_cons (withRevM_keep pr) (optsKeep_nil _ _ _)) Hpkl (by decide))) $$ []
      as %oresp %oerr Hog
    · iframe #
    (try wp_auto)
    wp_apply Hocancel
    icases Hog with (⟨%Hoerr, %mo, %σo, #Hmo, %HQo, %Hso⟩ | ⟨%Hoerr, -⟩)
    rotate_left
    · -- an error (`ErrCompacted` among them): no check
      cases oerr with
      | nil => exact absurd rfl Hoerr.1
      | ok ei => ?_
      wp_auto
      -- the next round
      wp_for_post
      iframe
      iexists n + W64 1, kk, kk, m.hdr.revision
      simp only [named]
      iframe
      isplitl
      · rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word]; iexact Hlb'
      isplitl
      · iexact Hprev'
      ipureintro; constructor <;> word
    subst Hoerr
    (try wp_auto)
    -- the reply is the previous key's at revision `prevRev`, at `v` (the invariant's history)
    have Hvo : mo.kvs.head?.map EtcdKv.value = some go!"v" := by
      obtain ⟨Hle, Hkvs⟩ := Hso
      have hrr : σo.readRev pr = sint.nat pr := by
        unfold KVState.readRev; rw [if_neg (by omega)]
      have hpn : (sint.nat pr : Int) = sint.Z pr := by
        show ((sint.Z pr).toNat : Int) = sint.Z pr; omega
      have hv := HQo (sint.nat pr) (by omega) (by omega)
      obtain ⟨kv, hkv, hval⟩ : ∃ kv, mvcc.findKey pk (σo.at (sint.nat pr)).kvs = some kv ∧
          kv.value = go!"v" := by
        cases h : mvcc.findKey pk (σo.at (sint.nat pr)).kvs with
        | none => simp [h] at hv
        | some x => simp [h] at hv; exact ⟨x, rfl, hv⟩
      rw [Hkvs, hrr, client.filter_key_of_findKey pk _ (KVStore.kvs_sorted _) kv hkv]
      simp [hval]
    iunfold rangeRespMsg at Hmo
    icases Hmo with ⟨%Hnno, %ho, %slo, %ps, #Hho, #Hhfo, #Hkvfo, #Hslo, #Hkvso, #Hmoreo, #Hcounto⟩
    -- the reply's first key-value holds `v`
    obtain ⟨kv1, Hkv1, Hval1⟩ : ∃ kv1, mo.kvs[0]? = some kv1 ∧ kv1.value = go!"v" := by
      cases h : mo.kvs with
      | nil => simp [h] at Hvo
      | cons x xs => simp [h] at Hvo; exact ⟨x, rfl, Hvo⟩
    iunfold txn.kvsIs at Hkvso
    icases Hkvso with ⟨%Hleno, #Hallo⟩
    obtain ⟨p1, Hp1⟩ : ∃ p1, ps[0]? = some p1 := by
      have : 0 < ps.length := by
        rw [Hleno]
        cases h : mo.kvs with
        | nil => simp [h] at Hkv1
        | cons x xs => simp
      exact ⟨ps[0], List.getElem?_eq_getElem this⟩
    ihave #Hkv1' := Hallo $$ %0 %p1 %kv1 %Hp1 %Hkv1
    iunfold txn.kvIs at Hkv1'
    icases Hkv1' with ⟨%kSlo, %vSlo, -, -, -, -, -, #HvFo, #HvSo, -⟩
    ihave %Hsllo := ownSlice_len _ _ _ $$ Hslo
    have Hneo : decide (slo.len = W64 0) = false := by
      rw [decide_eq_false_iff_not]
      intro h
      have hl := Hsllo.1
      rw [h] at hl
      have : 0 < ps.length := List.length_pos_of_mem (List.mem_of_getElem? Hp1)
      rw [hl] at this
      exact absurd this (by decide)
    wp_auto
    simp only [Hneo]
    wp_auto
    have Hbnd1 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z slo.len := by
      have := Hsllo.1
      have : 0 < ps.length := List.length_pos_of_mem (List.mem_of_getElem? Hp1)
      constructor <;> word
    simp only [Hbnd1, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index _ (sint.Z (W64 0)) _ DFrac.discard p1 Hbnd1.1 $$ [Hslo] as -
    · iframe Hslo; ipureintro; exact Hp1
    wp_apply wp_bytes_to_string vSlo kv1.value DFrac.discard $$ [HvSo] as -
    · iframe #
    rw [Hval1]
    wp_auto
    -- the next round
    wp_for_post
    iframe
    iexists n + W64 1, kk, kk, m.hdr.revision
    simp only [named]
    iframe
    isplitl
    · rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word]; iexact Hlb'
    isplitl
    · iexact Hprev'
    ipureintro; constructor <;> word
  · -- the rounds are done
    (try wp_auto)
    iapply HΦ; itrivial

end proof

end compactkv
end EtcdGrove
end Perennial
