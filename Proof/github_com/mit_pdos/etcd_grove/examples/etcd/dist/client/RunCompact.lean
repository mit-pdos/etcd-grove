/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/client/RunCompact.lean` (#50 F5,
`notes/etcd-dist-plan.md` §26). Lean-first (no Rocq counterpart).

compactwatch's `Main` (`compactwatch/Main.lean`) past its start, over the cross-machine contracts at the
cluster's view, with compact's invariant (`cwInv_alloc`, from the share's half) in place of the rounds'
invariant over the whole KV:

- `newClient` (its error ends the workload), `defer cli.Close()`;
- the 20 rounds, with the previous round's key and revision (`prevOk`: none, or a key under `cw/` whose put's
  result `cwPutQ` was returned at that revision): the put (`wp_cliPutR`, its update `cwPutAu`; an error skips
  the round); the compaction at the revision before the put's (`wp_cliCompact`: the put's revision reached,
  the retention `1`); the latest get after the put (`wp_cliGetR` with `cwReadAu` from the put's lower bound:
  `v`, at a revision at least the put's); the get of the previous key at its put's revision (the same read
  update from the previous put's bound: the state at that revision is the previous put's, `cwAt_put`); an
  error of either get skips its check;
- the watch of the last key from revision 2 (`Watch_dist`, with `cwReadAu`), `AfterFunc`'s timer, `Collect`
  (every event of value `v`: compact's discipline, `resp_cw`), `Stop`, the cancel, the check;
- `checkCompactRev` (its spec, a hypothesis); `checked`; the deferred `Close`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.RunCompact
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.checkCompactRev
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.newClient
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.checked
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.ended
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.WatchDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.CompactCallsDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.RespChan
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Collect
public import Spec.go_etcd_io.etcd.client.v3.WithRev
public import Spec.strconv.Itoa
public import Spec.go_etcd_io.etcd.client.v3.Client__Close
public import Perennial.Spec.context.Background
public import Perennial.Spec.time.AfterFunc
public import Perennial.Spec.time.Timer__Stop
public import Perennial.Proof.context.Link
public import Perennial.Proof.context.Results
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx
public import Proof.go_etcd_io.etcd.client.v3.ClientCallLaws
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProofMode Net client go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.cache.v3
open github_com.mit_pdos.etcd_grove.examples.etcd.dist
open etcd_dist

section pure
variable [GooseExts]

/-- Round `i`'s put and gets fit a gRPC message (`s` is `strconv.Itoa(i)`). -/
theorem cw_sizes (s : GoString) (hs : s.length ≤ 66) :
    (go!"cw/k" ++ s).length ≤ 70 ∧ opSizeOk (opPutModel (go!"cw/k" ++ s) compactVal []) ∧
      opSizeOk (opGetModel (go!"cw/k" ++ s) []) := by
  have h1 : (go!"cw/k" ++ s).length ≤ 70 := by
    rw [List.length_append]
    have : (go!"cw/k").length = 4 := rfl
    omega
  have h2 : compactVal.length ≤ 1 := by decide
  exact ⟨h1, opSizeOk_opPutModel (K := 70) (E := 0) (V := 1) (optsKeep_nil _ _ _) h1 h2 (by decide),
    opSizeOk_opGetModel (K := 70) (E := 0) (V := 0) (optsKeep_nil _ _ _) h1 (by decide)⟩

theorem cw_key (s : GoString) : compactPfx <+: go!"cw/k" ++ s :=
  ⟨go!"k" ++ s, by simp [compactPfx]⟩

end pure

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

/-- **The previous round's key and put's revision** (`RunCompact`'s `prevKey`, `prevRev`): none (`0`), or a
key under `cw/` whose put returned at that revision with its result `cwPutQ`. -/
def prevOk (γF γh : GName) (σ₀ : KVState) (pk : GoString) (pr : w64) : IProp GF :=
  iprop(⌜pr = W64 0⌝ ∨ ∃ σp : KVState, cwPutQ (Gg := hG.goose_globalGS) γF γh σ₀ pk σp ∗
    ⌜pr = W64 ((σp.rev + 1 : Nat) : Int) ∧ kvRevFits (σp.rev + 1) ∧ compactPfx <+: pk ∧
      pk.length ≤ 70⌝)

instance prevOk_persistent (γF γh : GName) (σ₀ : KVState) (pk : GoString) (pr : w64) :
    Persistent (prevOk (GF := GF) γF γh σ₀ pk pr) := by
  unfold prevOk; infer_instance

/-- **One response of the watch of a compact key** (`Collect`'s premise at `Watch_dist`'s responses, at
compact's read update): every event is of value `v` (`rangeEvents_cw`). -/
theorem resp_cw (o : OpFull) (σ₀ : KVState)
    (l0 : List (List mvcc.Change)) (k : GoString)
    (hk : compactPfx <+: o.key) (hend : o.base.rangeEnd = []) (c c' : w64)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) (hne : ¬ watchErr v) :
    ⊢ etcdstart.stateOk (GF := GF) o (fun σ => iprop(⌜cwSeen σ₀ l0 k σ⌝)) c c' v r ={⊤}=∗
      □ ∀ (j : Nat) (e : EvModel), ⌜r.events[j]? = some e⌝ -∗
        ∃ kvv : EtcdKv, kvValAt e.kv kvv ∗ ⌜kvv.value = compactVal⌝ := by
  iintro Hok
  unfold etcdstart.stateOk
  icases Hok with ⟨%σ, #HQ, #Hr⟩
  icases HQ with %Hseen
  unfold watchStateRespOk
  icases Hr with (⟨%H, -⟩ | %H | %H | ⟨%H, #Hev⟩)
  · exact absurd H.1 hne
  · obtain ⟨-, he0, -, -⟩ := H
    imodintro; iintro !> %j %e %h
    rw [he0] at h; simp at h
  · obtain ⟨-, hp, -⟩ := H
    have he0 := isProgressNotify_events hp
    imodintro; iintro !> %j %e %h
    rw [he0] at h; simp at h
  · iunfold eventsIs at Hev
    icases Hev with ⟨%hlen, #Hall⟩
    imodintro
    iintro !> %j %e %hj
    have hjl : j < r.events.length := (List.getElem?_eq_some_iff.mp hj).1
    obtain ⟨ev, hev⟩ : ∃ ev, (σ.rangeEvents o (sint.nat c + 1) (sint.nat c' + 1))[j]? = some ev :=
      ⟨_, List.getElem?_eq_getElem (by rw [← hlen]; exact hjl)⟩
    ihave #Hei := Hall $$ %j %e %ev %hj %hev
    iunfold eventIs at Hei
    icases Hei with ⟨-, #Hkv⟩
    iexists ev.kv
    iframe Hkv
    ipureintro
    exact rangeEvents_cw σ o hk hend Hseen.2.2.1 _ _ ev (List.mem_of_getElem? hev)

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 8192 in
theorem RunCompact.wp_proof
    (wp_newClient : newClient.spec (GF := GF) (hG := hG))
    (wp_checked : checked.spec (GF := GF) (hG := hG))
    (wp_ended : ended.spec (GF := GF) (hG := hG))
    (wp_checkCompactRev : checkCompactRev.spec (GF := GF) (hG := hG))
    (wp_Itoa : EtcdGrove.strconv.Itoa.spec (GF := GF) (hG := hG))
    (wp_Background : context.Background.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_Close : EtcdGrove.Client.Close.spec (GF := GF) (hG := hG))
    (wp_WithRev : WithRev.spec (GF := GF) (hG := hG))
    (wp_AfterFunc : time.AfterFunc.spec (GF := GF) (hG := hG))
    (wp_Stop : time.Timer.Stop.spec (GF := GF) (hG := hG))
    (wp_Collect : etcdstart.Collect.spec (GF := GF) (hG := hG))
    (wp_KV_Put : kv.Put.spec (GF := GF) (hG := hG))
    (wp_KV_Get : kv.Get.spec (GF := GF) (hG := hG))
    (wp_KV_Compact : kv.Compact.spec (GF := GF) (hG := hG))
    (wp_Watch : Watch_dist.spec (GF := GF) (hG := hG)) :
    RunCompact.spec (GF := GF) (hG := hG) := by
  intro π eps addrs hV Htb hpl hAs
  wp_start as ⟨Hlt, #Heps, Hsh⟩
  iunfold compactShare at Hsh
  icases Hsh with ⟨%Γ, %γr, %γ, %γh, %σ₀, %Hfacts, #Hms, #Hkvi, #Hpfx, Hhalf⟩
  obtain ⟨Hauth, Hcmp, Hcret, Hrev0⟩ := Hfacts
  -- compact's invariant, from the owner's half
  imod (cwInv_alloc γ ⊤) $$ Hhalf with ⟨%γF, #Hcw⟩
  ihave #Hcci : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Pstr : isPkgInit (PROP := IProp GF) pkg_id.strconv $$ []
  · iPkgInit
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  ihave #Pes : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  -- `cli, err := newClient(eps)`
  wp_apply (wp_newClient eps addrs (Classical.choice hV) Htb hpl) $$ [$Hlt] as %cl %cerr ⟨Hlt, Hcl⟩
  · iframe #
  icases Hcl with (⟨%Hcerr, #Hnc, #Hnp, -⟩ | %Hcfail)
  rotate_left
  · obtain ⟨Hcerr, -⟩ := Hcfail
    cases cerr with
    | nil => exact absurd rfl Hcerr
    | ok ei => ?_
    wp_auto
    wp_apply wp_ended as %r -
    (try wp_auto)
    iapply HΦ; iframe Hlt
  subst Hcerr
  ihave #Hcore := clientCoreAt_of_new cl addrs (Classical.choice hV) $$ [Hnc Hnp]
  · iframe #
  ihave ⟨%api, #Hkc⟩ := kvClient_of_new cl addrs (Classical.choice hV) Γ $$ [Hnc Hnp Hms]
  · iframe #
  ihave #Hnil := optsAt_nil (GF := GF)
  ihave #Hnil' := optsAt_res slice.nil [] iprop(True) $$ Hnil
  (try wp_auto)
  -- the rounds
  ihave IB : (∃ (j : w64) (pk : GoString) (pr : w64), "i" ∷ i_ptr ↦ j ∗ "pk" ∷ prevKey_ptr ↦ pk ∗
      "pr" ∷ prevRev_ptr ↦ pr ∗ "Hlt" ∷ levelTok 0 ∗
      "#Hprev" ∷ prevOk γF γh σ₀ pk pr ∗ "%Hj" ∷ ⌜0 ≤ sint.Z j⌝ : IProp GF) $$ [i prevKey prevRev Hlt]
  · iexists W64 0, _, _
    simp only [named]
    iframe
    isplitl
    · iunfold prevOk; ileft; ipureintro; rfl
    ipureintro; decide
  wp_for IB
  wp_if_destruct
  · (try wp_auto)
    -- `k := "cw/" + "k" + strconv.Itoa(i)`
    wp_apply wp_Itoa as %s %Hs
    have hlen : s.length ≤ 66 := by rw [Hs]; exact fmtInt_length_le _ _
    obtain ⟨hkl, hpsz, hgsz⟩ := cw_sizes s hlen
    have hk := cw_key s
    (try wp_auto)
    -- `pctx, pcancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)`
    wp_apply wp_Background
    (try wp_auto)
    wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
      as %pctx %pcd %pcancel ⟨#Hpcancel, #Hpctx, #Hpce, -⟩
    (try wp_auto)
    -- `presp, err := cli.Put(pctx, k, compactValue)`, with the round's update
    ihave Hau := cwPutAu (Gg := hG.goose_globalGS) Γ.kv γ γF γh σ₀ (go!"cw/k" ++ s) hk $$ [Hpfx Hcw]
    · iframe #
    wp_apply (wp_cliPutR wp_KV_Put cl api addrs (Classical.choice hV) Γ pctx pcd (go!"cw/k" ++ s)
        compactVal (cwPutQ (Gg := hG.goose_globalGS) γF γh σ₀ (go!"cw/k" ++ s)) hpsz Hauth)
      $$ [Hlt Hau] as %presp %perr ⟨Hlt, Hput⟩
    · iframe Hlt Hau
      iframe #
    (try wp_auto)
    wp_apply Hpcancel
    icases Hput with (⟨%Hperr, %m, %σp, #Hm, #HQ, %Hpm, #Hrv⟩ | %Hpfail)
    rotate_left
    · obtain ⟨Hperr, -⟩ := Hpfail
      cases perr with
      | nil => exact absurd rfl Hperr
      | ok ei => ?_
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, pk, pr
      simp only [named]
      iframe
      iframe Hprev
      ipureintro; word
    subst Hperr
    ihave #HQ' := HQ
    iunfold cwPutQ at HQ'
    icases HQ' with ⟨#Hfired, #Hplb, %Hpext⟩
    have hσp1 : 1 ≤ σp.rev := Nat.le_trans Hrev0 Hpext.rev_le
    have hfit := Hpm.2.lt
    have hrevZ : sint.Z m.hdr.revision = (σp.rev : Int) + 1 := by rw [Hpm.1]; word
    ihave ⟨%l1, #Hl1, %Hl1eq⟩ : (∃ l1 : List (List mvcc.Change), monoListLbOwn γh l1 ∗
        ⌜(kvOpStep (.put (putKeyOp (go!"cw/k" ++ s) compactVal)) σp).changes = l1⌝ : IProp GF) $$ [Hplb]
    · iexists _; iframe Hplb; ipureintro; rfl
    (try wp_auto)
    -- `presp.Header.Revision - 1`: past `0`, reached with the retention
    ihave #Hm' := Hm
    iunfold putRespMsg at Hm'
    icases Hm' with ⟨%Hnn, %h, %ppk, #Hh, #Hhf, -⟩
    iunfold hdrFull at Hhf
    icases Hhf with ⟨%Hhn, -, -, #HrevF, -, -⟩
    (try wp_auto)
    have Hr1 : 1 ≤ sint.Z (m.hdr.revision - W64 1) := by
      have : sint.Z (m.hdr.revision - W64 1) = sint.Z m.hdr.revision - 1 := by
        rw [hrevZ]; rw [Hpm.1]; word
      omega
    ihave #Hrv1 : kvRevLbZ Γ.kv (sint.Z (m.hdr.revision - W64 1) + Γ.kv.cret) $$ []
    · iapply kvRevLbZ_mono Γ.kv _ (sint.Z m.hdr.revision)
        (by
          rw [Hcret]
          have : sint.Z (m.hdr.revision - W64 1) = sint.Z m.hdr.revision - 1 := by
            rw [hrevZ]; rw [Hpm.1]; word
          push_cast; omega)
      iunfold kvRevLb at Hrv; iexact Hrv
    -- `cctx, ccancel := context.WithTimeout(...)`; `cli.Compact(cctx, ...)`, its outcome ignored
    wp_apply wp_Background
    (try wp_auto)
    wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
      as %cctx %ccd %ccancel ⟨#Hccancel, #Hcctx, #Hcce, -⟩
    (try wp_auto)
    wp_apply (wp_cliCompact wp_KV_Compact cl api addrs (Classical.choice hV) Γ cctx ccd
        (m.hdr.revision - W64 1) Hr1 Hcmp Hauth) $$ [$Hlt] as %cresp %cerr Hlt
    · iframe #
    (try wp_auto)
    wp_apply Hccancel
    (try wp_auto)
    -- `gctx, gcancel := ...`; `resp, err := cli.Get(gctx, k)`, the read update after the put
    wp_apply wp_Background
    (try wp_auto)
    wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
      as %gctx %gcd %gcancel ⟨#Hgcancel, #Hgctx, #Hgce, -⟩
    (try wp_auto)
    ihave #Hgau := cwReadAu (Gg := hG.goose_globalGS) Γ.kv γ γF γh σ₀
      l1 (go!"cw/k" ++ s) hk $$ [Hpfx Hcw Hl1 Hfired]
    · iframe #
    wp_apply (wp_cliGetR wp_KV_Get cl api addrs (Classical.choice hV) Γ gctx gcd (go!"cw/k" ++ s)
        slice.nil [] iprop(True)
        (fun σ => iprop(⌜cwSeen σ₀ l1 (go!"cw/k" ++ s) σ⌝))
        ⟨by unfold opGetPanics opFold OpFull.newOp; simp, rfl⟩ rfl hgsz Hauth)
      $$ [Hlt] as %gresp %gerr ⟨Hlt, -, Hget⟩
    · iframe Hlt
      iframe #
      try isplitl []
      try itrivial
      rw [show (opGetModel (go!"cw/k" ++ s) []).base.sortSet = false from rfl]
      iapply sortNamesIf_false
    (try wp_auto)
    wp_apply Hgcancel
    -- the next round's previous key and revision: this round's
    ihave #Hprev' : prevOk γF γh σ₀ (go!"cw/k" ++ s) m.hdr.revision $$ []
    · iunfold prevOk
      iright
      iexists σp
      iframe HQ
      ipureintro; exact ⟨Hpm.1, Hpm.2, hk, hkl⟩
    icases Hget with (⟨%Hgerr, %mg, %σg, #Hmg, #HQg, %Hsg⟩ | %Hgfail)
    rotate_left
    · -- an error: no check
      obtain ⟨Hgerr, -⟩ := Hgfail
      cases gerr with
      | nil => exact absurd rfl Hgerr
      | ok ei => ?_
      (try wp_auto)
      -- `if prevRev != 0`: the get of the previous round's key at its put's revision
      iunfold prevOk at Hprev
      icases Hprev with (%Hpr0 | ⟨%σq, #HQq, %Hq⟩)
      · subst Hpr0
        wp_auto
        -- the next round
        wp_for_post
        iframe
        iexists j + W64 1, (go!"cw/k" ++ s), m.hdr.revision
        simp only [named]
        iframe
        isplitl
        · iexact Hprev'
        ipureintro; word
      obtain ⟨Hpq, Hqfit, Hpk, Hpkl⟩ := Hq
      ihave #HQq' := HQq
      iunfold cwPutQ at HQq'
      icases HQq' with ⟨#Hqfired, #Hqlb, %Hqext⟩
      ihave ⟨%l0, #Hl0, %Hl0eq⟩ : (∃ l0 : List (List mvcc.Change), monoListLbOwn γh l0 ∗
          ⌜(kvOpStep (.put (putKeyOp pk compactVal)) σq).changes = l0⌝ : IProp GF) $$ [Hqlb]
      · iexists _; iframe Hqlb; ipureintro; rfl
      have Hqf := Hqfit.lt
      have hprZ : sint.Z pr = (σq.rev : Int) + 1 := by rw [Hpq]; word
      have Hpr : pr ≠ W64 0 := by
        intro h; rw [h] at hprZ; simp at hprZ; omega
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
      ihave #Hopts' := optsAt_res optsSl ([withRevM pr] : List (OpFull → OpFull)) iprop(True) $$ Hopts
      ihave #Hoau := cwReadAu (Gg := hG.goose_globalGS) Γ.kv γ γF γh σ₀
        l0 pk Hpk $$ [Hpfx Hcw Hl0 Hqfired]
      · iframe #
      wp_apply (wp_cliGetR wp_KV_Get cl api addrs (Classical.choice hV) Γ octx ocd pk optsSl
          ([withRevM pr] : List (OpFull → OpFull)) iprop(True)
          (fun σ => iprop(⌜cwSeen σ₀ l0 pk σ⌝))
          ⟨by simp [opGetPanics, opFold, withRevM, OpFull.newOp, OpModel.zero], rfl⟩ rfl
          (opSizeOk_opGetModel (K := 70) (E := 0) (V := 0)
            (optsKeep_cons (withRevM_keep pr) (optsKeep_nil _ _ _)) Hpkl (by decide)) Hauth)
        $$ [Hlt] as %oresp %oerr ⟨Hlt, -, Hog⟩
      · iframe Hlt
        iframe #
        try isplitl []
        try itrivial
        rw [show (opGetModel pk ([withRevM pr] : List (OpFull → OpFull))).base.sortSet = false from rfl]
        iapply sortNamesIf_false
      (try wp_auto)
      wp_apply Hocancel
      icases Hog with (⟨%Hoerr, %mo, %σo, #Hmo, #HQo, %Hso⟩ | %Hofail)
      rotate_left
      · -- an error (`ErrCompacted` among them): no check
        obtain ⟨Hoerr, -⟩ := Hofail
        cases oerr with
        | nil => exact absurd rfl Hoerr
        | ok ei => ?_
        wp_auto
        -- the next round
        wp_for_post
        iframe
        iexists j + W64 1, (go!"cw/k" ++ s), m.hdr.revision
        simp only [named]
        iframe
        isplitl
        · iexact Hprev'
        ipureintro; word
      subst Hoerr
      (try wp_auto)
      icases HQo with %Hseen
      -- the reply is the previous key's at revision `prevRev`, at `v` (the history)
      have Hvo : mo.kvs.head?.map EtcdKv.value = some compactVal := by
        have hbr : (rangeWireOf (opGetModel pk ([withRevM pr] : List (OpFull → OpFull)))).base.rev = pr :=
          rfl
        have hrr : σo.readRev pr = σq.rev + 1 := by
          have hpos : ¬ sint.Z pr ≤ 0 := by rw [hprZ]; omega
          unfold KVState.readRev; rw [if_neg hpos]
          rw [show sint.nat pr = (sint.Z pr).toNat from rfl, hprZ]; omega
        have hv := cwAt_put pk Hqext Hseen.2.1 (by rw [Hl0eq]; exact Hseen.1)
        obtain ⟨kv, hkv, hval⟩ : ∃ kv, mvcc.findKey pk (σo.at (σq.rev + 1)).kvs = some kv ∧
            kv.value = compactVal := by
          cases h : mvcc.findKey pk (σo.at (σq.rev + 1)).kvs with
          | none => simp [h] at hv
          | some x => simp [h] at hv; exact ⟨x, rfl, hv⟩
        have hsel := Hso.1
        rw [hrr] at hsel
        rw [srvRangeOk_getKeyRev pk pr _ _ _ hsel,
          client.filter_key_of_findKey pk _ (KVStore.kvs_sorted _) kv hkv]
        simp [hval]
      iunfold rangeRespMsg at Hmo
      icases Hmo with ⟨%Hnno, %ho, %slo, %ps, #Hho, #Hhfo, #Hkvfo, #Hslo, #Hkvso, #Hmoreo, #Hcounto⟩
      -- the reply's first key-value holds `v`
      obtain ⟨kv1, Hkv1, Hval1⟩ : ∃ kv1, mo.kvs[0]? = some kv1 ∧ kv1.value = compactVal := by
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
      iexists j + W64 1, (go!"cw/k" ++ s), m.hdr.revision
      simp only [named]
      iframe
      isplitl
      · iexact Hprev'
      ipureintro; word
    subst Hgerr
    (try wp_auto)
    icases HQg with %Hrd
    -- the reply's first key-value holds `v`
    have Hsel := Hsg.1
    have hb0 : (rangeWireOf (opGetModel (go!"cw/k" ++ s) [])).base.rev = W64 0 := rfl
    rw [show σg.readRev (W64 0) = σg.rev by simp [KVState.readRev]] at Hsel
    have h1 := (srvRangeOk_getKey (go!"cw/k" ++ s) σg.kvs mg.kvs mg.more Hsel).1
    obtain ⟨kv0, Hkv0, Hval0⟩ := cwReadOk_head Hrd.2.2.2
    rw [← h1] at Hkv0
    iunfold rangeRespMsg at Hmg
    icases Hmg with ⟨%Hnn', %h', %sl, %ps, #Hh', #Hhf', #Hkvf', #Hsl, #Hkvs, #Hmore, #Hcount⟩
    iunfold txn.kvsIs at Hkvs
    icases Hkvs with ⟨%Hlen, #Hall⟩
    obtain ⟨p0, Hp0⟩ : ∃ p0, ps[0]? = some p0 := by
      have : 0 < ps.length := by
        rw [Hlen]
        cases hk' : mg.kvs with
        | nil => rw [hk'] at Hkv0; simp at Hkv0
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
    -- the get read at a revision at least the put's (the history's bound)
    iunfold hdrFull at Hhf'
    icases Hhf' with ⟨%Hhn', -, -, #HrevF', -, -⟩
    have Hge : σp.rev + 1 ≤ σg.rev := by
      have he := KVExt_putKey (go!"cw/k" ++ s) compactVal Hpext
      have e1 := he.rev_eq
      rw [putKey_rev] at e1
      have e2 := Hrd.2.1.rev_eq
      have e3 := Hrd.1.length_le
      rw [← Hl1eq] at e3
      omega
    have Hnlt : ¬ sint.Z mg.hdr.revision < sint.Z m.hdr.revision := by
      have hf := Hsg.2.2.lt
      have e : sint.Z mg.hdr.revision = (σg.rev : Int) := by rw [Hsg.2.1]; word
      rw [e, hrevZ]; omega
    wp_auto
    try simp only [Hnlt, decide_false, ↓reduceIte]
    wp_auto
    -- `if prevRev != 0`: the get of the previous round's key at its put's revision
    iunfold prevOk at Hprev
    icases Hprev with (%Hpr0 | ⟨%σq, #HQq, %Hq⟩)
    · subst Hpr0
      wp_auto
      -- the next round
      wp_for_post
      iframe
      iexists j + W64 1, (go!"cw/k" ++ s), m.hdr.revision
      simp only [named]
      iframe
      isplitl
      · iexact Hprev'
      ipureintro; word
    obtain ⟨Hpq, Hqfit, Hpk, Hpkl⟩ := Hq
    ihave #HQq' := HQq
    iunfold cwPutQ at HQq'
    icases HQq' with ⟨#Hqfired, #Hqlb, %Hqext⟩
    ihave ⟨%l0, #Hl0, %Hl0eq⟩ : (∃ l0 : List (List mvcc.Change), monoListLbOwn γh l0 ∗
        ⌜(kvOpStep (.put (putKeyOp pk compactVal)) σq).changes = l0⌝ : IProp GF) $$ [Hqlb]
    · iexists _; iframe Hqlb; ipureintro; rfl
    have Hqf := Hqfit.lt
    have hprZ : sint.Z pr = (σq.rev : Int) + 1 := by rw [Hpq]; word
    have Hpr : pr ≠ W64 0 := by
      intro h; rw [h] at hprZ; simp at hprZ; omega
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
    ihave #Hopts' := optsAt_res optsSl ([withRevM pr] : List (OpFull → OpFull)) iprop(True) $$ Hopts
    ihave #Hoau := cwReadAu (Gg := hG.goose_globalGS) Γ.kv γ γF γh σ₀
      l0 pk Hpk $$ [Hpfx Hcw Hl0 Hqfired]
    · iframe #
    wp_apply (wp_cliGetR wp_KV_Get cl api addrs (Classical.choice hV) Γ octx ocd pk optsSl
        ([withRevM pr] : List (OpFull → OpFull)) iprop(True)
        (fun σ => iprop(⌜cwSeen σ₀ l0 pk σ⌝))
        ⟨by simp [opGetPanics, opFold, withRevM, OpFull.newOp, OpModel.zero], rfl⟩ rfl
        (opSizeOk_opGetModel (K := 70) (E := 0) (V := 0)
          (optsKeep_cons (withRevM_keep pr) (optsKeep_nil _ _ _)) Hpkl (by decide)) Hauth)
      $$ [Hlt] as %oresp %oerr ⟨Hlt, -, Hog⟩
    · iframe Hlt
      iframe #
      try isplitl []
      try itrivial
      rw [show (opGetModel pk ([withRevM pr] : List (OpFull → OpFull))).base.sortSet = false from rfl]
      iapply sortNamesIf_false
    (try wp_auto)
    wp_apply Hocancel
    icases Hog with (⟨%Hoerr, %mo, %σo, #Hmo, #HQo, %Hso⟩ | %Hofail)
    rotate_left
    · -- an error (`ErrCompacted` among them): no check
      obtain ⟨Hoerr, -⟩ := Hofail
      cases oerr with
      | nil => exact absurd rfl Hoerr
      | ok ei => ?_
      wp_auto
      -- the next round
      wp_for_post
      iframe
      iexists j + W64 1, (go!"cw/k" ++ s), m.hdr.revision
      simp only [named]
      iframe
      isplitl
      · iexact Hprev'
      ipureintro; word
    subst Hoerr
    (try wp_auto)
    icases HQo with %Hseen
    -- the reply is the previous key's at revision `prevRev`, at `v` (the history)
    have Hvo : mo.kvs.head?.map EtcdKv.value = some compactVal := by
      have hbr : (rangeWireOf (opGetModel pk ([withRevM pr] : List (OpFull → OpFull)))).base.rev = pr :=
        rfl
      have hrr : σo.readRev pr = σq.rev + 1 := by
        have hpos : ¬ sint.Z pr ≤ 0 := by rw [hprZ]; omega
        unfold KVState.readRev; rw [if_neg hpos]
        rw [show sint.nat pr = (sint.Z pr).toNat from rfl, hprZ]; omega
      have hv := cwAt_put pk Hqext Hseen.2.1 (by rw [Hl0eq]; exact Hseen.1)
      obtain ⟨kv, hkv, hval⟩ : ∃ kv, mvcc.findKey pk (σo.at (σq.rev + 1)).kvs = some kv ∧
          kv.value = compactVal := by
        cases h : mvcc.findKey pk (σo.at (σq.rev + 1)).kvs with
        | none => simp [h] at hv
        | some x => simp [h] at hv; exact ⟨x, rfl, hv⟩
      have hsel := Hso.1
      rw [hrr] at hsel
      rw [srvRangeOk_getKeyRev pk pr _ _ _ hsel,
        client.filter_key_of_findKey pk _ (KVStore.kvs_sorted _) kv hkv]
      simp [hval]
    iunfold rangeRespMsg at Hmo
    icases Hmo with ⟨%Hnno, %ho, %slo, %ps, #Hho, #Hhfo, #Hkvfo, #Hslo, #Hkvso, #Hmoreo, #Hcounto⟩
    -- the reply's first key-value holds `v`
    obtain ⟨kv1, Hkv1, Hval1⟩ : ∃ kv1, mo.kvs[0]? = some kv1 ∧ kv1.value = compactVal := by
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
    iexists j + W64 1, (go!"cw/k" ++ s), m.hdr.revision
    simp only [named]
    iframe
    isplitl
    · iexact Hprev'
    ipureintro; word
  · (try wp_auto)
    -- `if prevRev == 0 { return ended(...) }`
    wp_if_destruct
    · wp_apply wp_ended as %r -
      (try wp_auto)
      wp_apply wp_Close as %ce -
      · iframe #
      (try wp_auto)
      iapply HΦ; iframe Hlt
    iunfold prevOk at Hprev
    icases Hprev with (%H0 | ⟨%σq, #HQq, %Hq⟩)
    · exact absurd H0 (by simpa using Hif)
    obtain ⟨Hpq, Hqfit, Hpk, Hpkl⟩ := Hq
    ihave #HQq' := HQq
    iunfold cwPutQ at HQq'
    icases HQq' with ⟨#Hqfired, #Hqlb, %Hqext⟩
    ihave ⟨%l0, #Hl0, %Hl0eq⟩ : (∃ l0 : List (List mvcc.Change), monoListLbOwn γh l0 ∗
        ⌜(kvOpStep (.put (putKeyOp pk compactVal)) σq).changes = l0⌝ : IProp GF) $$ [Hqlb]
    · iexists _; iframe Hqlb; ipureintro; rfl
    -- the client's `Watcher`
    ihave ⟨%w, #Hwc⟩ := watchClient_of_new cl addrs (Classical.choice hV) Γ $$ [Hnc Hnp Hms]
    · iframe #
    ihave #Hwc' := Hwc
    iunfold watchClientAt at Hwc'
    icases Hwc' with ⟨-, -, #Hwf, -⟩
    (try wp_auto)
    -- `wctx, wcancel := context.WithCancel(context.Background())`
    wp_apply context.wp_Background
    wp_apply context.wp_WithCancel_Background iprop(True) $$ [$Pctx $Hcci]
      as %wctx %γctx %wcancel ⟨#Hwcancel, #Hwctx, -, #wctxFrom⟩
    ihave #wctxO := metadata.outgoingCtxOkC_bgFrom wctx $$ wctxFrom
    ihave #wctxM := metadata.outMD_bgFrom wctx $$ wctxFrom
    (try wp_auto)
    -- `t := time.AfterFunc(readTimeout, wcancel)`
    wp_apply (wp_AfterFunc _ wcancel) $$ [] as %t Ht
    · wp_apply Hwcancel $$ [] as -
      · itrivial
      ipureintro; exact isPanic_intoVal ()
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
    -- compact's read update, from the last put's bound
    ihave #Hwau := cwReadAu (Gg := hG.goose_globalGS) Γ.kv γ γF γh σ₀
      l0 pk Hpk $$ [Hpfx Hcw Hl0 Hqfired]
    · iframe #
    iunfold kvReadAu at Hwau
    iunfold kvAu at Hwau
    -- `wch := cli.Watcher.Watch(wctx, prevKey, clientv3.WithRev(2))`
    wp_apply (wp_Watch cl w addrs (Classical.choice hV) Γ wctx
        ({ Values := ∅, Deadline := none, Done_gn := γctx, PDone := iprop(True) } :
          context.ContextDesc (IProp GF)) none
        pk optsSl ([withRevM (W64 2)] : List (OpFull → OpFull)) (W64 2)
        (fun σ => iprop(⌜cwSeen σ₀ l0 pk σ⌝)))
      $$ [] as %wch %γw ⟨#Hsp, Hcons, Hcur⟩
    · iframe #
      isplitr
      · iapply EtcdGrove.context.watchCtx_of_isContext; isplitl [] <;> iassumption
      ipureintro; exact cw_watch_ok pk Hpkl
    ihave #Hwch := etcdstart.isRespChan_of_state wch Γ.kv γw _
      (fun σ => iprop(⌜cwSeen σ₀ l0 pk σ⌝))
      iprop(True) $$ Hsp
    (try wp_auto)
    ihave Hcons : etcdWatchConsumer γw 0 (W64 2 - W64 1) $$ [Hcons Hcur]
    · unfold etcdWatchConsumer
      iexists []
      iframe Hcons Hcur
      ipureintro; rfl
    obtain ⟨hnk, hne⟩ := cw_watchNorm pk (cw_ne_nil Hpk)
    -- `evs, ok := etcdstart.Collect(wch, prevRev)`: every event of value `v`
    wp_apply (wp_Collect (etcdstart.stateOk (opWatchModel pk ([withRevM (W64 2)] : List (OpFull → OpFull))).watchNorm
          (fun σ => iprop(⌜cwSeen σ₀ l0 pk σ⌝)))
        (fun _ _ => True) (fun _ e => iprop(⌜e.Val' = compactVal⌝)) iprop(True)
        wch γw pr (W64 2 - W64 1) trivial (fun _ _ _ _ => inferInstance)
        (fun c c' v r => etcdstart.stateOk_closeErr _ _ c c' v r)
        (fun n c c' v r hne' _ => by
          iintro - Hok
          imod (resp_cw _ σ₀ l0 pk
            (by rw [hnk]; exact Hpk) hne c c' v r hne') $$ Hok with #Hv
          imodintro
          isplitr
          · ipureintro; trivial
          iintro !> %j' %e %hj
          ihave ⟨%kvv, #Hk, %Hval⟩ := Hv $$ %j' %e %hj
          iexists kvv
          iframe Hk
          ipureintro; simp [etcdstart.evWev, Hval])) $$ [Hcons]
      as %esl %ok Hcol
    · iframe; iframe #
      iintro !>; itrivial
    (try wp_auto)
    -- `t.Stop()`, `wcancel()`
    wp_apply (wp_Stop t) $$ [Ht] as %b -
    · iright; iexact Ht
    (try wp_auto)
    wp_apply Hwcancel $$ [] as -
    · itrivial
    (try wp_auto)
    cases ok
    · (try wp_auto)
      -- `checkCompactRev(cli, prevKey)`
      wp_apply (wp_checkCompactRev cl pk addrs (Classical.choice hV) Γ γr γ γF γh σ₀
          l0 Hpk Hpkl Hcret Hauth hAs) $$ [$Hlt] as Hlt
      · iframe #
      (try wp_auto)
      wp_apply wp_checked as %r -
      (try wp_auto)
      wp_apply wp_Close as %ce -
      · iframe #
      (try wp_auto)
      iapply HΦ; iframe Hlt
    ihave ⟨%evs, Hes, -, #Hall⟩ := Hcol $$ %rfl
    (try wp_auto)
    -- `for _, e := range evs { if e.Val != compactValue { panic(...) } }`
    imod ownSlice_persist _ _ _ $$ Hes with #Hes
    ihave %Hlen := ownSlice_len $$ Hes
    ihave IE : (∃ (n : w64) (ev : etcdstart.wev), "i" ∷ i_ptr ↦ n ∗ "e" ∷ e_ptr ↦ ev ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n⌝ : IProp GF) $$ [i e]
    · iexists W64 0, _
      simp only [named]
      iframe
      ipureintro; decide
    wp_for IE
    wp_if_destruct
    · -- an event: its value is `v`
      have Hlt' : sint.nat n < evs.length := by rw [Hlen.1]; word
      obtain ⟨ev, hev⟩ : ∃ ev, evs[sint.nat n]? = some ev :=
        ⟨_, List.getElem?_eq_getElem Hlt'⟩
      have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z esl.len := ⟨Hn, by word⟩
      simp only [Hbnd, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index _ (sint.Z n) evs DFrac.discard ev Hn $$ [Hes] as -
      · iframe Hes; ipureintro; exact hev
      (try wp_auto)
      ihave %Hv := Hall $$ %(sint.nat n) %ev %hev
      rw [Hv]
      (try wp_auto)
      wp_for_post
      iframe
      iexists n + W64 1, ev
      simp only [named]
      iframe
      ipureintro; word
    · (try wp_auto)
      -- `checkCompactRev(cli, prevKey)`
      wp_apply (wp_checkCompactRev cl pk addrs (Classical.choice hV) Γ γr γ γF γh σ₀
          l0 Hpk Hpkl Hcret Hauth hAs) $$ [$Hlt] as Hlt
      · iframe #
      (try wp_auto)
      wp_apply wp_checked as %r -
      (try wp_auto)
      wp_apply wp_Close as %ce -
      · iframe #
      (try wp_auto)
      iapply HΦ; iframe Hlt

end proof

end etcd_dist_client
end EtcdGrove
end Perennial
