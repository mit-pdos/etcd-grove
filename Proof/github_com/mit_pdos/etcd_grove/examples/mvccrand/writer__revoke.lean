/- Lean-first (no Rocq counterpart). The proof of `writer.revoke`: `genLease`'s `0` returns at once
(no live lease is `0`, so `L` is `L.filter (· != 0)`); a live `id` is in `L`. The model: the keys'
loop collects the tester's keys on `id` in key order (`keyList.filter (onLease M id)`, `M` the last
state), which are the store's `leaseDelKeys` (`leaseDelKeys_eq_onLease`), and the second loop deletes
them from the pending state, appending their deletes (`delOne_foldl`): `pendOk` of `leaseDels`. The
store: `end`'s callback is the closure calling `Revoke` (`lessor.Revoke.spec`), whose update is the
writer's begin at its `σ` and `End`'s two steps (`revoke_au`, as `endCb_txnEnd`'s), the hook's
contract the tester's (`hookOk`), the begin state reachable (`mvccState_reachable.law`, in the
invariant) and of at most six key-values (`stMatch_length_le`); `Revoke` returns `nil` (`id ∈ L`).
After: the hook's check, `id` out of the model's leases, `Lookup(id)` `nil` (`id ∉ L.filter`). -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__revoke
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__genLease
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__begin
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__end
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__checkHook
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.check
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Revoke
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Lookup
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.TxnEnd
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.WriteLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccrand mvcc mvcc.api

section model
variable [GooseExts]

/-- The `j`-th key is not among the first `j`. -/
private theorem keyList_get_not_mem_take' (j : Nat) (x : GoString) (h : keyList[j]? = some x) :
    x ∉ keyList.take j := by
  rcases j with _ | _ | _ | _ | _ | _ | j <;> simp [keyList] at h ⊢ <;> subst h <;> decide

private theorem filter_take_succ'' (n : Nat) (x : GoString) (pr : GoString → Bool)
    (hx : keyList[n]? = some x) :
    (keyList.take (n + 1)).filter pr =
      (keyList.take n).filter pr ++ (if pr x then [x] else []) := by
  rw [List.take_add_one, hx, List.filter_append]
  cases h : pr x <;> simp [List.filter, h]

/-- **A state the tester's map matches has at most its six key-values** (sorted: distinct keys). -/
theorem stMatch_length_le (M : GMap GoString kvRec) (s : List EtcdKv) (hM : stMatch M s)
    (hs : s.Pairwise etcdKvLess) : s.length ≤ 6 := by
  have hnd : (s.map EtcdKv.key).Nodup := by
    unfold List.Nodup
    rw [List.pairwise_map]
    exact hs.imp fun h heq => go.goStringLt_irrefl _ (heq ▸ h)
  have hsub : s.map EtcdKv.key ⊆ keyList := by
    intro k hk
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hk
    exact hM.2 v hv
  have := (List.subperm_of_subset hnd hsub).length_le
  simpa [keyList] using this

/-- **The model after the revoke's loops is the tester's model of the lease's deletes.** -/
theorem pendOk_revoke (σ : MvccState) (Hs : List HRev) (hlen : Hs.length = σ.log.length)
    (hM : stMatch (lastSt Hs) (stateAfter σ.log)) (id : w64) (hid : id ≠ W64 0) :
    pendOk σ Hs (leaseDels (stateAfter σ.log) id)
      ⟨W64 (Hs.length : Int), delAll (keyList.filter (onLease (lastSt Hs) id)) (lastSt Hs),
        (keyList.filter (onLease (lastSt Hs) id)).map delChange⟩ := by
  have hs : (stateAfter σ.log).Pairwise etcdKvLess := stateAfter_sorted σ.log
  have hk := leaseDelKeys_eq_onLease (lastSt Hs) _ hM hs id hid
  unfold leaseDels
  rw [hk]
  refine ⟨?_, stMatch_delAll _ _ _ _ hM⟩
  have := delOne_foldl (keyList.filter (onLease (lastSt Hs) id)) ⟨W64 (Hs.length : Int), lastSt Hs, []⟩
  simpa only [List.nil_append, pendOf] using this

end model

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The begin state is reachable** (the invariant's state, the writer's). -/
theorem writer_reach (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (kv : GoInterface) (h : Loc) (γ : RandNames) (σ : MvccState) :
    isMvcc kv γ.kv ∗ inv worldN (worldInv h γ) ∗ ghostVar γ.σ (1 : Qp).half σ ⊢
      |={⊤}=> ghostVar γ.σ (1 : Qp).half σ ∗ ⌜MvccReachable σ⌝ := by
  haveI := fun σ => hpers.2.2.2.2.1 γ.kv σ
  haveI := fun S => hpers.2.2.2.2.2.1 γ.ws S
  haveI := hpers.1 kv γ.kv
  haveI : Timeless (worldInv (GF := GF) h γ) := by unfold worldInv; infer_instance
  iintro ⟨#Hkv, #Hinv, Hw⟩
  iinv Hinv with >Hi Hclose
  iunfold worldInv at Hi
  icases Hi with ⟨%σ1, %S, %p, %Hl, %W, Hσ, Hgσ, HS, Hreg, Hpub, Hpv, Hpm, Hlb, %Hok⟩
  ihave %Hag := ghostVar_agree γ.σ _ _ _ _ $$ Hgσ Hw
  icases (persistent_entails_right (hreach kv γ.kv σ1)) $$ [$Hkv $Hσ] with ⟨%Hr, -, Hσ⟩
  imod Hclose $$ [Hσ Hgσ HS Hreg Hpub Hpv Hpm Hlb] with -
  · inext; iunfold worldInv; iexists σ1, S, p, Hl, W; iframe; ipureintro; exact Hok
  imodintro
  iframe Hw
  ipureintro
  rw [← Hag]; exact Hr.1

/-- **`Revoke`'s update** at the writer's begin state `σ`: the begin commits it unchanged (the
writer's half of `γ.σ`), then `End`'s two steps as `endCb_txnEnd`'s (the notify step at the
history `histAfter Hs P`, which covers the notified log), to the writer's half at the committed
state. -/
theorem revoke_au (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (h : Loc) (γ : RandNames) (σ : MvccState) (Hs : List HRev) (pend : List Change) (P : PendM)
    (hok : pendOk σ Hs pend P) (hpn : σ.pending = none) (hlen : Hs.length = σ.log.length)
    (hrev : ∀ r < Hs.length, ∃ e, Hs[r]? = some e ∧ revOk σ.log Hs r e) :
    inv worldN (worldInv h γ) ∗ ghostVar γ.σ (1 : Qp).half σ ∗ monoListLbOwn γ.h.l (histAfter Hs P) ⊢
      srvApi.auBegin γ.kv σ
        (srvApi.auEnd γ.kv σ pend (ghostVar γ.σ (1 : Qp).half (commitSt σ pend))) := by
  haveI := fun σ => hpers.2.2.2.2.1 γ.kv σ
  haveI := fun S => hpers.2.2.2.2.2.1 γ.ws S
  haveI : Timeless (worldInv (GF := GF) h γ) := by unfold worldInv; infer_instance
  have hdisj : (↑worldN : CoPset) ⊆ ⊤ \ ↑mvccN :=
    nclose_subseteq' "world" (mask_ndot_ne' nroot "mvccrand" "mvcc" (by decide))
  iintro ⟨#Hinv, Hw, #Hlb⟩
  unfold srvApi.auBegin
  -- the begin
  iauintro
  unfold atomic_acc
  iinv Hinv with >Hi Hclose
  iunfold worldInv at Hi
  icases Hi with ⟨%σ1, %S, %p, %Hl, %W, Hs, Hgσ, HS, Hreg, Hpub, Hpv, Hpm, Hlb0, %Hok⟩
  ihave %Hag := ghostVar_agree γ.σ _ _ _ _ $$ Hgσ Hw
  have Hag' := Hag.symm
  subst Hag'
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑mvccN) \ ↑worldN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ
  iframe Hs
  isplit
  · iintro Hs
    imod Hclose2 with -
    imod Hclose $$ [Hs Hgσ HS Hreg Hpub Hpv Hpm Hlb0] with -
    · inext; iunfold worldInv; iexists σ, S, p, Hl, W; iframe; ipureintro; exact Hok
    imodintro
    iframe Hw
  iintro ⟨-, Hs⟩
  imod Hclose2 with -
  imod Hclose $$ [Hs Hgσ HS Hreg Hpub Hpv Hpm Hlb0] with -
  · inext; iunfold worldInv; iexists σ, S, p, Hl, W; iframe; ipureintro; exact Hok
  imodintro
  isplitr
  · ipureintro; rfl
  unfold srvApi.auEnd
  -- the notify step
  iauintro
  unfold atomic_acc
  iinv Hinv with >Hi Hclose
  iunfold worldInv at Hi
  icases Hi with ⟨%σ1, %S, %p, %Hl, %W, Hs, Hgσ, HS, Hreg, Hpub, Hpv, Hpm, Hlb0, %Hok⟩
  ihave %Hag := ghostVar_agree γ.σ _ _ _ _ $$ Hgσ Hw
  have Hag' := Hag.symm
  subst Hag'
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑mvccN) \ ↑worldN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ
  iframe Hs
  isplit
  · iintro Hs
    imod Hclose2 with -
    imod Hclose $$ [Hs Hgσ HS Hreg Hpub Hpv Hpm Hlb0] with -
    · inext; iunfold worldInv; iexists σ, S, p, Hl, W; iframe; ipureintro; exact Hok
    imodintro
    iframe Hw
  · iintro ⟨%Heq, Hs, -⟩
    imod Hclose2 with -
    imod ghostVar_update_halves (σ.notify pend) γ.σ _ _ $$ Hgσ Hw with ⟨Hgσ, Hw⟩
    iclear Hlb0
    imod Hclose $$ [Hs Hgσ HS Hreg Hpub Hpv Hpm] with -
    · inext; iunfold worldInv; iexists σ.notify pend, S, p, histAfter Hs P, W; iframe; iframe #
      ipureintro
      obtain ⟨h1, h2, h3, -, h5⟩ := Hok
      exact ⟨h1, h2, h3, histOkM_notify σ Hs pend P hok hlen hrev, h5⟩
    imodintro
    -- the commit step
    iauintro
    unfold atomic_acc
    iinv Hinv with >Hi Hclose
    iunfold worldInv at Hi
    icases Hi with ⟨%σ2, %S2, %p2, %Hl2, %W2, Hs, Hgσ, HS, Hreg, Hpub, Hpv, Hpm, Hlb2, %Hok2⟩
    iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑mvccN) \ ↑worldN from
      Std.LawfulSet.empty_subset)
    iintro Hclose2
    isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
    iexists σ2
    iframe Hs
    isplit
    · iintro Hs
      imod Hclose2 with -
      imod Hclose $$ [Hs Hgσ HS Hreg Hpub Hpv Hpm Hlb2] with -
      · inext; iunfold worldInv; iexists σ2, S2, p2, Hl2, W2; iframe; ipureintro; exact Hok2
      imodintro
      iframe Hw
    · iintro ⟨%Heq2, Hs⟩
      imod Hclose2 with -
      subst Heq2
      imod ghostVar_update_halves (commitSt σ pend) γ.σ _ _ $$ Hgσ Hw with ⟨Hgσ, Hw⟩
      imod Hclose $$ [Hs Hgσ HS Hreg Hpub Hpv Hpm Hlb2] with -
      · inext; iunfold worldInv; iexists commitSt σ pend, S2, p2, Hl2, W2; iframe
        ipureintro
        obtain ⟨h1, h2, h3, h4, h5⟩ := Hok2
        have hr := commitSt_rev_ge σ pend
        refine ⟨h1, h2, ?_, ?_, h5⟩
        · simp only [MvccState.rev, MvccState.notify] at h3 hr ⊢; omega
        · unfold histOkM at h4 ⊢; rw [commitSt_notifiedLog]; exact h4
      imodintro
      iexact Hw

theorem writer.revoke.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_genLease : writer.genLease.spec (GF := GF) (hG := hG))
    (wp_begin : writer.begin.spec (GF := GF) (hG := hG))
    (wp_end : writer.end.spec (GF := GF) (hG := hG))
    (wp_checkHook : writer.checkHook.spec (GF := GF) (hG := hG))
    (wp_Revoke : lease.lessor.Revoke.spec (GF := GF) (hG := hG))
    (wp_Lookup : lease.lessor.Lookup.spec (GF := GF) (hG := hG)) :
    writer.revoke.spec (GF := GF) (hG := hG) := by
  intro w wv γ B f q σ Hs L n k T R i s
  wp_start as ⟨Hctx, Hown, Hle, Hpre⟩
  iunfold writerCtx at Hctx
  icases Hctx with ⟨#Hpkg, #Hmv, #Htu, #Hw, #Hinv, #Hhist, #Hkv, #Hhook, Hhok⟩
  iunfold hookOk at Hhok
  icases Hhok with #Hhok
  iunfold writerOwn at Hown
  icases Hown with ⟨Htt, Hbk, Hrd, Hidle, ⟨%g, Hg⟩, ⟨%Lm, Hlm, %HLm⟩, Hlo⟩
  iunfold writerLe at Hle
  icases Hle with ⟨%lp, %rd, %r, #Hro, Hlrd, Hrvk, HR, HT, Hrdo, Hdel, Hbe, Hrb, %HlP, Hnext,
    %Hn⟩
  ihave #Hro2 := Hro
  iunfold writerLeRO at Hro2
  icases Hro2 with ⟨%HleEq, #Hlpkg, #Hlinv, #Hlcfg, #Hguard, #Hlbe⟩
  ihave #Hw2 := Hw
  iunfold writerRO at Hw2
  icases Hw2 with ⟨#kvW, #leW, #hW, #rW, #leasesW, #applyingW, #savedW, #ticksW⟩
  iunfold writerIdle at Hidle
  icases Hidle with ⟨Hgσ, HW, Hpv, %Hid⟩
  obtain ⟨Hpn, Hlen, Hbound, Hmatch⟩ := Hid
  wp_auto
  wp_apply wp_genLease w wv Lm g $$ [$Hpkg $Hw $Hlm $Hg] as %id ⟨Hlm, Hg, %Hl⟩
  (try wp_auto)
  by_cases hid0 : id = W64 0
  · -- no live lease: nothing
    subst hid0
    (try wp_auto)
    have hf : L.filter (· != W64 0) = L := by
      apply List.filter_eq_self.2
      intro a ha
      have := (Hn.2 a ha).1
      simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]
      intro h; rw [h] at this; simp at this
    iapply HΦ
    rw [hf]
    iexists σ, Hs, W64 0
    isplitl [Htt Hbk Hrd Hgσ HW Hpv Hg Hlm Hlo]
    · iunfold writerOwn
      iframe Htt Hbk Hrd Hg Hlo
      isplitl [Hgσ HW Hpv]
      · iunfold writerIdle; iframe; ipureintro; exact ⟨Hpn, Hlen, Hbound, Hmatch⟩
      iexists Lm; iframe; ipureintro; exact HLm
    isplitr [Hpre]
    · iunfold writerLe
      iexists lp, rd, r
      iframe
      isplitl []
      · iexact Hro
      ipureintro; exact ⟨HlP, Hn⟩
    iright; iexact Hpre
  sorry

end proof

end mvccrand
end EtcdGrove
end Perennial
