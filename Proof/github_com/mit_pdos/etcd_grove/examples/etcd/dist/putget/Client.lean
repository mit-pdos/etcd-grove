/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/putget/Client.lean` (2026-11-24,
`notes/putget-dist-plan.md` §12). Lean-first (no Rocq counterpart).

The in-process putget's `Main` from `NewClient` on (`Proof/.../examples/etcd/putget/Main.lean`), on a
machine of its own: `zap.NewNop()`; `etcdstart.NewClient` (at any watch environment, `wenv_nonempty`:
`Put`/`Get` read none of it), whose client dials with no proxy (`clientNoProxy`); each call's context
with the request timeout (`client.wp_WithTimeout_bg`); `cli.Put` before the member's view is known
(`etcd_dist.Client_Put_dist`, a trust-boundary axiom until #24's S2), whose deposit the publication
invariant gives (`etcd_dist.envAt_pub`: `▷ □ putgetPub ν`, the putget invariant at the client's own heap,
under the later the deposit allows) and whose `nil` reply gives the view, the invariant and the put's
flag; `cli.Get` at that view (`etcd_dist.Client_Get_dist`); the check, on the reply's message
(`rangeRespMsg`), takes the `else` branch, as `Main`'s. Every step's error returns `false`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.Client
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.ClientPutDist
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.ClientGetDist
public import Spec.go_uber_org.zap.NewNop
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.NewClient
public import Perennial.Spec.context.Background
public import Proof.go_etcd_io.etcd.client.v3.InvOp
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.AddrOk
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.AddrPlain

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_putget_dist

open Iris Iris.BI Iris.ProofMode Net go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.Assumptions]

set_option maxHeartbeats 800000 in
theorem Client.wp_proof
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_NewClient : etcdstart.NewClient.spec (GF := GF) (hG := hG))
    (wp_Background : context.Background.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_Put_dist : etcd_dist.Client_Put_dist.spec (GF := GF) (hG := hG))
    (wp_Get_dist : etcd_dist.Client_Get_dist.spec (GF := GF) (hG := hG))
    (wp_AddrOk : AddrOk.spec (GF := GF) (hG := hG))
    (hne : mvcc.api.names_nonempty.law) :
    Client.spec (GF := GF) (hG := hG) := by
  intro CS TB π ep γE mid hlen hAs
  have Htb : threadBound GF ≤ 2 ^ 30 := TB.threadBound_le
  wp_start as ⟨Hlt, Hshare⟩
  (try wp_auto)
  -- the address's check: `!AddrOk(ep)` returns `false`
  wp_apply wp_AddrOk _ hlen
  cases hc : Net.addrOk ep
  · simp only [Bool.not_false]
    try wp_auto
    iapply HΦ; itrivial
  simp only [Bool.not_true]
  try wp_auto
  have hplain := etcd_dist.addrOk_plainEndpoint hc
  ispecialize Hshare $$ %(by simp [hc])
  iunfold clientShare at Hshare
  icases Hshare with ⟨#Haddr, #Hinv⟩
  -- `context`'s `closedchan`, from its package's fact
  ihave #Hcci : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  -- the imports' package facts
  ihave #Pes : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart $$ []
  · iPkgInit
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_NewNop as %lg #Hlgz
  (try wp_auto)
  -- `NewClient(ep, lg)`, at any watch environment (`Put`/`Get` read none of it)
  wp_apply (wp_NewClient ep lg (Classical.choice (wenv_nonempty (GF := GF) hne)) hplain Htb) $$ [$Hlt]
    as %cl %cerr ⟨Hlt, Hcl⟩
  · iframe #
  icases Hcl with (⟨%Hcerr, #Hnc, -, #Hnp⟩ | %Hcfail)
  rotate_left
  · obtain ⟨Hcerr, -⟩ := Hcfail
    cases cerr with
    | nil => exact absurd rfl Hcerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Hcerr
  wp_auto
  -- `pctx, pcancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)`
  wp_apply wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
    as %pctx %pcd %pcancel ⟨#Hpcancel, #Hpctx, #Hpce, -⟩
  (try wp_auto)
  -- no options
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
  -- the deposit: at every view published at `γE`, the putget invariant at the client's own heap
  -- (`envAt_pub`, under the later the deposit allows)
  ihave #Hdep : □ (∀ ν : etcd_dist.EnvView, etcd_dist.envAt (Gg := hG.goose_globalGS) γE ν ={⊤}=∗
      ▷ ∃ (γr : ReadNames) (γf : GName), ⌜γr.kv.st = ν.st⌝ ∗
        client.putGetInv γr γf go!"k" go!"v") $$ []
  · imodintro
    iintro %ν #Hν
    imod (etcd_dist.envAt_pub_h ⊤ γE CoPset.subseteq_top
      (putgetPub (G := hG.goose_globalGS)) ν) $$ Hinv Hν with #Hpub
    imodintro
    inext
    iunfold putgetPub at Hpub
    icases Hpub with ⟨%γr, %γf, %Hst, #Hall⟩
    iexists γr, γf
    isplitr
    · ipureintro; exact Hst
    ihave HL := Hall $$ %hG.goose_localGS
    iexact HL
  -- `cli.Put(pctx, "k", "v")`, before the view is known
  wp_apply (wp_Put_dist cl ep (Classical.choice (wenv_nonempty (GF := GF) hne)) γE mid pctx pcd
      go!"k" go!"v" slice.nil
      (opSizeOk_opPutModel (K := 1) (E := 0) (V := 1) (optsKeep_nil _ _ _) (by decide) (by decide)
        (by decide))) $$ [$Hlt] as %presp %perr ⟨Hlt, Hput⟩
  · iframe #
  -- `pcancel()`
  (try wp_auto)
  wp_apply Hpcancel
  icases Hput with (⟨%Hperr, %ν, %γr, %γf, #Hν, %Hst, #Hpg, #Hflag⟩ | %Hpfail)
  rotate_left
  · obtain ⟨Hperr, -⟩ := Hpfail
    cases perr with
    | nil => exact absurd rfl Hperr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Hperr
  (try wp_auto)
  -- `gctx, gcancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)`
  wp_apply wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
    as %gctx %gcd %gcancel ⟨#Hgcancel, #Hgctx, #Hgce, -⟩
  (try wp_auto)
  -- `cli.Get(gctx, "k")`, at the view the `Put` learned
  wp_apply (wp_Get_dist cl ep (Classical.choice (wenv_nonempty (GF := GF) hne)) γE mid ν γr γf
      gctx gcd go!"k" go!"v" slice.nil
      (opSizeOk_opGetModel (K := 1) (E := 0) (V := 0) (optsKeep_nil _ _ _) (by decide) (by decide))
      Hst) $$ [$Hlt] as %gresp %gerr ⟨-, Hget⟩
  · iframe #
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

end etcd_putget_dist
end EtcdGrove
end Perennial
