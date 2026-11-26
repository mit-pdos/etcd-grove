/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/client/RunPutGet.lean` (#50 N9a,
`notes/etcd-dist-plan.md` §23). Lean-first (no Rocq counterpart).

The orchestrator allocates putget's invariant from its share's half (`pgInv_alloc`), connects (`newClient`;
its error ends the workload), defers `Close`, and runs the 50 rounds with the invariant `i ≥ 0` (and the
token): round `i`'s key and value are `pg/k<s>`/`v<s>` for `s = strconv.Itoa(i)`; its put (`wp_cliPut`, over
`KV_Put_dist`) carries the round's one-shot update (`pgPutAu_round`), whose result on `nil` is the put's
`pgFired`; its get (`CompactCallsDist.wp_cliGetR`, over `KV_Get_dist`) the read update after it (`pgGetAu`), whose result
`pgReadOk` makes the reply's first key-value the round's value (`pgReadOk_head`, the selection
`srvRangeOk_getKey`), so the check does not panic. A failed put or get continues. Then `ended`/`checked`, and
the deferred `Close`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.RunPutGet
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.newClient
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.checked
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.ended
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.KVCallsDist
public import Spec.strconv.Itoa
public import Spec.go_etcd_io.etcd.client.v3.Client__Close
public import Perennial.Spec.context.Background
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx

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

set_option maxHeartbeats 1600000 in
theorem RunPutGet.wp_proof
    (wp_newClient : newClient.spec (GF := GF) (hG := hG))
    (wp_checked : checked.spec (GF := GF) (hG := hG))
    (wp_ended : ended.spec (GF := GF) (hG := hG))
    (wp_Itoa : EtcdGrove.strconv.Itoa.spec (GF := GF) (hG := hG))
    (wp_Background : context.Background.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_Close : EtcdGrove.Client.Close.spec (GF := GF) (hG := hG))
    (wp_KV_Put : KV_Put_dist.spec (GF := GF) (hG := hG))
    (wp_KV_Get : KV_Get_dist.spec (GF := GF) (hG := hG)) :
    RunPutGet.spec (GF := GF) (hG := hG) := by
  intro π eps addrs hV Htb hpl hAs
  wp_start as ⟨Hlt, #Heps, Hsh⟩
  (try iunfold putgetShare at Hsh)
  iunfold kvPfxShare at Hsh
  icases Hsh with ⟨%Γ, %γ, %Hauth, #Hms, #Hpfx, Hhalf⟩
  -- putget's invariant, from the owner's half
  ihave Hpg0 := pgInv_alloc (Gg := hG.goose_globalGS) γ ⊤ $$ Hhalf
  imod Hpg0 with ⟨%γP, #Hpg⟩
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
  ihave IB : (∃ (j : w64) (rv : Bool), "i" ∷ i_ptr ↦ j ∗ "ran" ∷ ran_ptr ↦ rv ∗ "Hlt" ∷ levelTok 0 ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j⌝ : IProp GF) $$ [i ran Hlt]
  · iexists W64 0, false
    simp only [named]
    iframe
    ipureintro; decide
  wp_for IB
  wp_if_destruct
  · (try wp_auto)
    -- `k := "pg/k" + strconv.Itoa(i)`, `v := "v" + strconv.Itoa(i)`
    wp_apply wp_Itoa as %s1 %Hs1
    (try wp_auto)
    wp_apply wp_Itoa as %s2 %Hs2
    have hs : s2 = s1 := Hs2.trans Hs1.symm
    subst hs
    have hlen : s2.length ≤ 66 := by rw [Hs2]; exact fmtInt_length_le _ _
    (try wp_auto)
    -- `pctx, pcancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)`
    wp_apply wp_Background
    (try wp_auto)
    wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
      as %pctx %pcd %pcancel ⟨#Hpcancel, #Hpctx, #Hpce, -⟩
    (try wp_auto)
    -- `cli.Put(pctx, k, v)`, with the round's update
    ihave Hau := pgPutAu_round (Gg := hG.goose_globalGS) Γ.kv γ γP s2 $$ [Hpfx Hpg]
    · iframe #
    wp_apply (wp_cliPut wp_KV_Put cl api addrs (Classical.choice hV) Γ pctx pcd (go!"pg/k" ++ s2)
        (go!"v" ++ s2) (fun _ => pgFired (Gg := hG.goose_globalGS) γP (go!"pg/k" ++ s2))
        (pg_sizes s2 hlen).1 Hauth) $$ [Hlt Hau] as %presp %perr ⟨Hlt, Hput⟩
    · iframe Hlt Hau
      iframe #
    (try wp_auto)
    wp_apply Hpcancel
    icases Hput with (⟨%Hperr, %σp, #Hfired⟩ | %Hpfail)
    rotate_left
    · obtain ⟨Hperr, -⟩ := Hpfail
      cases perr with
      | nil => exact absurd rfl Hperr
      | ok ei => ?_
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, rv
      simp only [named]
      iframe
      ipureintro; word
    subst Hperr
    (try wp_auto)
    -- `gctx, gcancel := ...`
    wp_apply wp_Background
    (try wp_auto)
    wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
      as %gctx %gcd %gcancel ⟨#Hgcancel, #Hgctx, #Hgce, -⟩
    (try wp_auto)
    -- `cli.Get(gctx, k)`, with the read update after the put
    ihave #Hgau := pgGetAu (Gg := hG.goose_globalGS) Γ.kv γ γP (go!"pg/k" ++ s2) (putgetPfx_key s2)
      $$ [Hpfx Hpg Hfired]
    · iframe #
    wp_apply (wp_cliGetR wp_KV_Get cl api addrs (Classical.choice hV) Γ gctx gcd (go!"pg/k" ++ s2)
        slice.nil [] iprop(True) (fun σ => iprop(⌜pgReadOk (go!"pg/k" ++ s2) σ⌝))
        ⟨by unfold opGetPanics opFold OpFull.newOp; simp, rfl⟩ rfl (pg_sizes s2 hlen).2)
      $$ [Hlt] as %gresp %gerr ⟨Hlt, -, Hget⟩
    · iframe Hlt
      iframe #
      isplitl []
      · itrivial
      rw [show (opGetModel (go!"pg/k" ++ s2) []).base.sortSet = false from rfl]
      iapply sortNamesIf_false
    (try wp_auto)
    wp_apply Hgcancel
    icases Hget with (⟨%Hgerr, %m, %σ, #Hm, #HQ, %Hsel⟩ | %Hgfail)
    rotate_left
    · obtain ⟨Hgerr, -⟩ := Hgfail
      cases gerr with
      | nil => exact absurd rfl Hgerr
      | ok ei => ?_
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, rv
      simp only [named]
      iframe
      ipureintro; word
    subst Hgerr
    (try wp_auto)
    icases HQ with %Hrd
    -- the reply's first key-value holds the round's value
    have Hsel' : txn.srvRangeOk (rangeWireOf (opGetModel (go!"pg/k" ++ s2) [])) σ.kvs m.kvs m.more := by
      have h := Hsel.1
      rwa [at_readRev_zero σ _ rfl] at h
    have h1 := (srvRangeOk_getKey (go!"pg/k" ++ s2) σ.kvs m.kvs m.more Hsel').1
    obtain ⟨kv0, Hkv0, Hval0⟩ := pgReadOk_head Hrd
    rw [← h1] at Hkv0
    rw [pgVal_key] at Hval0
    iunfold rangeRespMsg at Hm
    icases Hm with ⟨%Hnn, %h, %sl, %ps, #Hh, #Hhf, #Hkvf, #Hsl, #Hkvs, #Hmore, #Hcount⟩
    iunfold txn.kvsIs at Hkvs
    icases Hkvs with ⟨%Hlen, #Hall⟩
    obtain ⟨p0, Hp0⟩ : ∃ p0, ps[0]? = some p0 := by
      have : 0 < ps.length := by
        rw [Hlen]
        cases hk : m.kvs with
        | nil => rw [hk] at Hkv0; simp at Hkv0
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
    wp_for_post
    iframe
    iexists j + W64 1, true
    simp only [named]
    iframe
    ipureintro; word
  (try wp_auto)
  wp_if_destruct
  · wp_apply wp_ended as %r -
    (try wp_auto)
    wp_apply wp_Close as %ce -
    · iframe #
    (try wp_auto)
    iapply HΦ; iframe Hlt
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
