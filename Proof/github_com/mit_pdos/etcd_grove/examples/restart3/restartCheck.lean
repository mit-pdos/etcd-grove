/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/restart3/restartCheck.lean` (the restart
plan's R2, 2026-11-02): over the drafted specs of the stop and the restart. Lean-first (no Rocq
counterpart).

The steps: `stop(m)` (`stop.spec`: the image at the stopped incarnation's names, the peer address
and its protocol's right back); the `NPuts` puts of `k ↦ v2` (`put.spec`; the loop keeps the put's
flag once one put returned `nil`); the member started again (`startMember.specRestart`: new names
`ρ'` that agree with `ρ`, `restartNames`); its gRPC API served (`serveClient`, with the ghost step
`common.kv_served`); a client of it (`common.NewClient`); the `Get` (`client.client_Get_own`) under
the client's invariant moved to the restarted member's names (`putGetInv_st`: it reads only the KV
state's ghost variable, which `restartNames` keeps); and the check, as putget3's.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.restart3.restartCheck
public import Spec.github_com.mit_pdos.etcd_grove.examples.restart3.stop
public import Spec.github_com.mit_pdos.etcd_grove.examples.restart3.startMember
public import Spec.github_com.mit_pdos.etcd_grove.examples.restart3.serveClient
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.NewClient
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Served
public import Perennial.Spec.context.Background
public import Proof.go_etcd_io.etcd.client.v3.ServeFromStart
public import Proof.go_etcd_io.etcd.client.v3.InvServerKV
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace restart3

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.restart3.Assumptions]

/-- **The client's invariant reads only the KV state's ghost variable**: at read names sharing it,
it is the same invariant. -/
theorem putGetInv_st (γ γ' : ReadNames) (h : γ.kv.st = γ'.kv.st) (γf : GName) (key val : GoString) :
    client.putGetInv (GF := GF) γ γf key val = client.putGetInv γ' γf key val := by
  unfold client.putGetInv
  simp only [etcdKV_congr γ.kv γ'.kv h]

set_option maxHeartbeats 1000000 in
theorem restartCheck.wp_proof
    (wp_stop : stop.spec (GF := GF) (hG := hG))
    (wp_put : put.spec (GF := GF) (hG := hG))
    (wp_startMemberR : startMember.specRestart (GF := GF) (hG := hG))
    (wp_serveClient : serveClient.spec (GF := GF) (hG := hG))
    (wp_NewClient : common.NewClient.spec (GF := GF) (hG := hG))
    (wp_Background : context.Background.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG)) :
    restartCheck.spec (GF := GF) (hG := hG) := by
  intro CS CRE CEC cl ep V E₁ γr γf cid mid m s pl E ρ N name peerAddr caddr peer cluster lg M iu
    Uok ps bootLog ctxs dir id γ γn ThB RcB RcN Hst hvs hrule hboot hblen Hγn1 Hγn2 Hdirok Hdir HU
    Hpe Hlg Hck Haf Hbuq Hrf Hdbo Hms hAs
  wp_start as ⟨Hmst, #Hreq, #Hcl, #Hregs, #Hinv, Hca, Htok, #Hpeer, #Hclu, #Hsls, #HbR, #Hcom,
    #Hcci, #Hnet⟩
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  ihave #Pv3 : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc $$ []
  · iPkgInit
  ihave #Pcom : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.common $$ []
  · iPkgInit
  (try wp_auto)
  -- `stop(m)`
  wp_apply (wp_stop m s pl γ id peerAddr γn E ρ) $$ [Hmst] as ⟨Himg, Hpa, Hpown⟩
  · iframe; iframe #
  (try wp_auto)
  -- the puts of `k ↦ v2`: once one returned `nil`, the put's flag
  simp only [github_com.mit_pdos.etcd_grove.examples.restart3.NPuts]
  ihave HI : (∃ (j : w64), "i" ∷ i_ptr ↦ j ∗ "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ 20⌝ ∗
      "Hlb" ∷ (⌜j = W64 0⌝ ∨ monoNatLbOwn γf 1) : IProp GF) $$ [i]
  · iexists W64 0
    iframe
    isplitr
    · ipureintro; constructor <;> word
    ileft; ipureintro; rfl
  wp_for HI
  wp_if_destruct
  · wp_apply (wp_put cl ep V E₁ γr γf cid mid go!"k" go!"v2"
        (opSizeOk_opPutModel (K := 1) (E := 0) (V := 2) (optsKeep_nil _ _ _) (by decide) (by decide)
          (by decide)) hAs) as %err Hput
    · iframe #
    icases Hput with (%Herr | ⟨%Herr, #Hlb'⟩)
    · cases err with
      | nil => exact absurd rfl Herr
      | ok ei => ?_
      wp_auto
      wp_for_post
      iapply HΦ; itrivial
    subst Herr
    wp_auto
    wp_for_post
    iframe
    iexists j + W64 1
    iframe
    isplitr
    · ipureintro; constructor <;> word
    iright; iexact Hlb'
  -- the loop done: some put returned `nil`
  ihave #Hlb1 : monoNatLbOwn γf 1 $$ [Hlb]
  · icases Hlb with (%Hj0 | #Hlb)
    · exfalso; subst Hj0; revert Hif; decide
    · iexact Hlb
  -- the stopped member started again
  have Hu : Uok ⟨[common.httpURL peerAddr], [common.httpURL caddr], M, iu⟩ := HU
  wp_apply (wp_startMemberR N name peerAddr caddr peer cluster lg M iu Uok ps bootLog ctxs dir id γ ρ γn
      hvs hrule hboot hblen Hγn1 Hγn2 Hdirok Hdir Hu Hlg Hck Haf Hbuq Hdbo)
    $$ [Hpa Htok Himg Hpown] as %mR %err Hr
  · iframe; iframe #
  icases Hr with (⟨%Herr, -⟩ | ⟨%Herr, %sR, %plR, %ρ', %E₀', %Hρ', Hup, Hst⟩)
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Herr
  wp_auto
  iunfold common.memberUp at Hup
  icases Hup with ⟨%E', %cfg, %γw, %HEc, #Hreq', #Hrd, Hgo, Hlg3, Hrslots, #Hwb, #Hsf, Hbemu,
    Hlts, Hlgs, Hrds, Hsts, Hbms, -, HWR, -⟩
  obtain ⟨HEa, HEo, HElg, HEtr, HEw⟩ := HEc
  iunfold memberStop at Hst
  icases Hst with ⟨HmR, -, -, -⟩
  ihave #Hcm := Hcom
  iunfold common.commonPremises at Hcm
  icases Hcm with ⟨-, -, -, -, -, #Hnrl⟩
  -- `serveClient(mR, client)`, with etcd's KV calls registered at the address
  haveI := Hms
  have Hrb48 := ReceiptBoundLe.le (GF := GF) (2 ^ 48)
  wp_apply (wp_serveClient mR sR plR caddr E' { ρ' with wait := γw } ρ'.rd cfg
      (fun cid mid _ => common.etcdKVAt caddr E' { ρ' with wait := γw } ρ'.rd cid mid)
      (by rw [HElg]; exact Hlg) HEtr HEw Hms Hbuq)
    $$ [HmR Hca Hlg3 Hbemu Hgo HWR Hlts Hlgs Hrds Hsts Hrslots Hbms] as %serr ⟨-, Hs⟩
  · iframe; iframe #
    iintro %gs %lis %cid' %mid' %R Hg
    iapply (common.kv_served sR E' { ρ' with wait := γw } ρ'.rd gs lis caddr cid' mid' R Hrb48
      Hrf rfl)
    unfold common.kvServeStocks
    iframe; iframe #
  icases Hs with (%Hserr | ⟨%Hserr, %cidR, %midR, %R, #Hkv⟩)
  · cases serr with
    | nil => exact absurd rfl Hserr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Hserr
  wp_auto
  ihave #HregsR := common.etcdKVAt_regs caddr E' { ρ' with wait := γw } ρ'.rd cidR midR
    rfl $$ Hkv
  -- `NewClient(client, lg)`
  have Htb := ThreadBoundLe.le (GF := GF) (2 ^ 28)
  wp_apply (wp_NewClient caddr lg
      (EtcdGrove.client.srvWEnv R caddr [] null null [] null default) Hlg Hpe (by omega))
    as %clR %cerr Hcl'
  icases Hcl' with (⟨%Hcerr, #Hnc, -⟩ | %Hcfail)
  rotate_left
  · obtain ⟨Hcerr, -⟩ := Hcfail
    cases cerr with
    | nil => exact absurd rfl Hcerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Hcerr
  wp_auto
  -- `gctx, gcancel := context.WithTimeout(context.Background(), common.RequestTimeout)`
  wp_apply wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
    as %gctx %gcd %gcancel ⟨#Hgcancel, #Hgctx, #Hgce, -⟩
  (try wp_auto)
  -- `cliR.Get(gctx, "k")`, under the client's invariant at the restarted member's names
  obtain ⟨-, Hst', -⟩ := Hρ'
  ihave #HinvR : client.putGetInv ρ'.rd γf go!"k" go!"v2" $$ []
  · rw [putGetInv_st ρ'.rd γr (by rw [Hst', Hst]) γf]
    iexact Hinv
  imod monoNatLbOwn_0 (GF := GF) ρ'.rd.committed with #Hc0
  imod mvcc.idxCert_nil (GF := GF) E'.γ.idx with #HF0
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
  wp_apply (client.client_Get_own clR caddr _ E' ρ'.rd γf (W64 0) cidR midR
      gctx gcd go!"k" go!"v2" slice.nil []
      (opSizeOk_opGetModel (K := 1) (E := 0) (V := 0) (optsKeep_nil _ _ _) (by decide) (by decide)))
    as %gresp %gerr Hget
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
  -- the reply's first key-value holds `v2`
  obtain ⟨kv0, Hkv0, Hval0⟩ : ∃ kv0, m.kvs[0]? = some kv0 ∧ kv0.value = go!"v2" := by
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

end restart3
end EtcdGrove
end Perennial
