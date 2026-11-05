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
    refine hs.imp ?_
    intro a b h heq
    unfold etcdKvLess at h
    rw [heq] at h
    exact go.goStringLt_irrefl _ h
  have hsub : s.map EtcdKv.key ⊆ keyList := by
    intro k hk
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hk
    exact hM.2 v hv
  have := (List.subperm_of_subset hnd hsub).length_le
  simpa [keyList] using this

/-- **The model after the revoke's loops is the tester's model of the lease's deletes.** -/
theorem pendOk_revoke (σ : MvccState) (Hs : List HRev) (_hlen : Hs.length = σ.log.length)
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
  haveI := fun σ => hpers.2.2.2.2.2.1 γ.kv σ
  haveI := fun S => hpers.2.2.2.2.2.2.1 γ.ws S
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
    (hok : pendOk σ Hs pend P) (_hpn : σ.pending = none) (hlen : Hs.length = σ.log.length)
    (hrev : ∀ r < Hs.length, ∃ e, Hs[r]? = some e ∧ revOk σ.log Hs r e) :
    inv worldN (worldInv h γ) ∗ ghostVar γ.σ (1 : Qp).half σ ∗ monoListLbOwn γ.h.l (histAfter Hs P) ⊢
      srvApi.auBegin γ.kv σ
        (srvApi.auEnd γ.kv σ pend (ghostVar γ.σ (1 : Qp).half (commitSt σ pend))) := by
  haveI := fun σ => hpers.2.2.2.2.2.1 γ.kv σ
  haveI := fun S => hpers.2.2.2.2.2.2.1 γ.ws S
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
  haveI := hpers.1 wv.kv' γ.kv
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
      simp only [bne_iff_ne, ne_eq]
      intro h; rw [h] at this; simp at this
    iapply HΦ
    iexists σ, Hs, W64 0
    rw [hf]
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
  -- a live lease
  have hidL : id ∈ L := by
    rcases Hl with h | h
    · exact absurd h hid0
    · exact (HLm id).1 h
  have hM := lastSt_match σ.log Hs Hlen Hmatch
  simp only [hid0, decide_false]
  (try wp_auto)
  wp_apply wp_begin w wv γ σ Hs $$ [$Hpkg $Hw $Hrd $Hinv Hgσ HW Hpv] as %p ⟨Hrd, Hidle, Hp⟩
  · iunfold writerIdle; iframe; ipureintro; exact ⟨Hpn, Hlen, Hbound, Hmatch⟩
  (try wp_auto)
  iunfold ownPending at Hp
  icases Hp with ⟨%pv, Hp, %Hrev, Hst, Hchs, Hcap⟩
  ihave Hmi : (mvccrandInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  iunfold mvccrandInit at Hmi
  icases Hmi with ⟨⟨%kss, #Hks, #Hksl⟩, -⟩
  ihave %Hksn := ownSlice_len $$ Hksl
  have hks6 : sint.Z kss.len = 6 := by
    have h := Hksn.1; simp only [keyList, List.length_cons, List.length_nil] at h
    have h4 : sint.nat kss.len = (sint.Z kss.len).toNat := rfl
    have := Hksn.2; omega
  have hmatch_succ : ∀ (n : Nat) (x : GoString) (pr : GoString → Bool), keyList[n]? = some x →
      (keyList.take (n + 1)).filter pr =
        (keyList.take n).filter pr ++ (if pr x then [x] else []) := by
    intro n x pr hx
    rw [List.take_add_one, hx, List.filter_append]
    cases h : pr x <;> simp [List.filter, h]
  (try wp_auto)
  -- the keys on the lease, in key order
  ihave HI : (∃ (j : w64) (wsl : GoSlice) (kv0 : GoString),
      "i" ∷ i_ptr ↦ j ∗ "ks" ∷ ks_ptr ↦ wsl ∗
      "Hwl" ∷ wsl ↦* ((keyList.take (sint.nat j)).filter (onLease (lastSt Hs) id)) ∗
      "Hwc" ∷ ownSliceCap GoString wsl (DFrac.own 1) ∗ "k" ∷ k_ptr ↦ kv0 ∗
      "Hst" ∷ pv.st' ↦$ lastSt Hs ∗ "Hp" ∷ p ↦ pv ∗ "p" ∷ p_ptr ↦ p ∗ "id" ∷ id_ptr ↦ id ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ 6⌝ : IProp GF) $$ [i ks k Hst Hp p id]
  · iexists W64 0, slice.nil, _
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.filter_nil]
    iframe
    isplitl
    · iapply ownSlice_nil
    isplitl
    · iapply ownSliceCap_nil
    ipureintro; constructor <;> word
  wp_for HI
  by_cases Hlt : sint.Z j < sint.Z kss.len
  · rw [decide_eq_true Hlt]; simp only [↓reduceIte]
    have hj6 : sint.Z j < 6 := by rw [← hks6]; exact Hlt
    list_elem keyList (sint.nat j) as x
    have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z kss.len := ⟨Hj.1, Hlt⟩
    (try wp_auto)
    (try simp only [hb, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index kss (sint.Z j) keyList DFrac.discard x Hj.1 $$ [Hksl] as -
    · iframe #; ipureintro; exact Hx_lookup
    (try wp_auto)
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    wp_apply (wp_map_lookup2 go.string kvRec.ty pv.st' (lastSt Hs) x (DFrac.own 1)) $$ [$Hst] as Hst
    (try wp_auto)
    cases hx : (lastSt Hs) !! x with
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, decide_false]
      (try wp_auto)
      wp_for_post
      iframe
      iexists j + W64 1, wsl, x
      rw [hj1, hmatch_succ (sint.nat j) x _ Hx_lookup]
      simp only [onLease, hx, Bool.false_eq_true, ↓reduceIte, List.append_nil]
      iframe
      ipureintro; constructor <;> word
    | some ev =>
      simp only [Option.isSome_some, decide_true, Option.getD_some]
      (try wp_auto)
      by_cases hev : ev.lease' = id
      · simp only [hev, decide_true]
        (try wp_auto)
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %osl ⟨Hosl, -⟩
        (try wp_auto)
        wp_apply wp_slice_append $$ [$Hwl $Hwc $Hosl] as %wsl' ⟨Hwl, Hwc, -⟩
        wp_for_post
        iframe
        iexists j + W64 1, wsl', x
        rw [hj1, hmatch_succ (sint.nat j) x _ Hx_lookup]
        simp only [onLease, hx, hev, decide_true, ↓reduceIte]
        iframe
        ipureintro; constructor <;> word
      · simp only [hev, decide_false]
        (try wp_auto)
        wp_for_post
        iframe
        iexists j + W64 1, wsl, x
        rw [hj1, hmatch_succ (sint.nat j) x _ Hx_lookup]
        simp only [onLease, hx, hev, decide_false, Bool.false_eq_true, ↓reduceIte, List.append_nil]
        iframe
        ipureintro; constructor <;> word
  rw [decide_eq_false Hlt]; simp only [Bool.false_eq_true, ↓reduceIte]
  have hj6 : sint.nat j = 6 := by
    have : ¬ sint.Z j < 6 := by rw [← hks6]; exact Hlt
    have h0 := Hj.2; have h4 : sint.nat j = (sint.Z j).toNat := rfl; rw [h4]; omega
  have htk : keyList.take 6 = keyList := rfl
  simp only [hj6, htk]
  (try wp_auto)
  -- their deletes
  generalize hKS : keyList.filter (onLease (lastSt Hs) id) = KS
  ihave %Hwln := ownSlice_len $$ Hwl
  have hn : ∀ x : w64, sint.nat x = (sint.Z x).toNat := fun _ => rfl
  ihave HI2 : (∃ (j : w64) (cs : GoSlice) (kv0 : GoString),
      "i" ∷ i_ptr ↦ j ∗ "k" ∷ k_ptr ↦ kv0 ∗
      "Hp" ∷ p ↦ { pv with changes' := cs } ∗
      "Hst" ∷ pv.st' ↦$ delAll (KS.take (sint.nat j)) (lastSt Hs) ∗
      "Hchs" ∷ cs ↦* ((KS.take (sint.nat j)).map delChange) ∗
      "Hcap" ∷ ownSliceCap change cs (DFrac.own 1) ∗
      "Hwl" ∷ wsl ↦* KS ∗ "p" ∷ p_ptr ↦ p ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z wsl.len⌝ : IProp GF) $$ [i k Hp Hst Hchs Hcap Hwl p]
  · iexists W64 0, pv.changes', _
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.map_nil, delAll,
      List.foldl_nil]
    iframe
    ipureintro; constructor <;> word
  wp_for HI2
  by_cases Hlt : sint.Z j < sint.Z wsl.len
  · rw [decide_eq_true Hlt]; simp only [↓reduceIte]
    have hjl : sint.nat j < KS.length := by have := Hwln.1; rw [hn] at this ⊢; omega
    list_elem KS (sint.nat j) as x
    have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z wsl.len := ⟨Hj.1, Hlt⟩
    (try wp_auto)
    (try simp only [hb, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index wsl (sint.Z j) KS (DFrac.own 1) x Hj.1 $$ [Hwl] as Hwl
    · iframe; ipureintro; exact Hx_lookup
    (try wp_auto)
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    have htk1 : KS.take (sint.nat j + 1) = KS.take (sint.nat j) ++ [x] := by
      rw [List.take_add_one, Hx_lookup]; rfl
    wp_apply (wp_mapDelete pv.st' _ x go.string kvRec.ty) $$ [$Hst] as Hst
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %osl ⟨Hosl, -⟩
    (try wp_auto)
    wp_apply wp_slice_append $$ [$Hchs $Hcap $Hosl] as %cs' ⟨Hchs, Hcap, -⟩
    (try wp_auto)
    wp_for_post
    iframe
    iexists j + W64 1, cs', x
    rw [hj1, htk1, delAll_append]
    simp only [List.map_append, List.map_cons, List.map_nil]
    iframe
    ipureintro; constructor <;> word
  rw [decide_eq_false Hlt]; simp only [Bool.false_eq_true, ↓reduceIte]
  have hjK : sint.nat j = KS.length := by have := Hwln.1; rw [hn] at this ⊢; omega
  rw [hjK, List.take_length]
  (try wp_auto)
  subst hKS
  -- `end`, with the closure calling `Revoke`
  have hok := pendOk_revoke σ Hs Hlen hM id hid0
  ihave Hpd : ownPending p ⟨W64 (Hs.length : Int), delAll (keyList.filter (onLease (lastSt Hs) id))
      (lastSt Hs), (keyList.filter (onLease (lastSt Hs) id)).map delChange⟩ $$ [Hp Hst Hchs Hcap]
  · iunfold ownPending; iexists { pv with changes' := cs }; iframe; ipureintro; exact Hrev
  iunfold writerIdle at Hidle
  icases Hidle with ⟨Hgσ, HW, Hpv, -⟩
  imod writer_reach hpers hreach wv.kv' wv.h' γ σ $$ [$Hkv $Hinv $Hgσ] with ⟨Hgσ, %Hreach⟩
  have hs6 := stMatch_length_le _ _ hM (stateAfter_sorted σ.log)
  iunfold mvccDeleter at Hdel
  icases Hdel with ⟨%Hrdnn, #Hdel⟩
  have hR := wp_Revoke lp γ.kv id rd q B iprop(True) f σ L r (hookPre wv i s)
    iprop(True ∗ hookPost wv i) (hookPost wv i)
    (ghostVar γ.σ (1 : Qp).half (commitSt σ (leaseDels (stateAfter σ.log) id)))
  dsimp only at hR
  wp_func_lits
  wp_apply (wp_end w wv γ σ Hs p _ (leaseDels (stateAfter σ.log) id) _
      iprop(threadTok ∗ w_ptr ↦ w ∗ id_ptr ↦ id ∗ mvccBackend γ.kv q (etcdStorage B) iprop(True) ∗
        lease.rdOwn (mvccLeases γ.kv) rd ∗ hookPre wv i s ∗
        lease.leaseOwn (mvccLeases γ.kv) L (pendItems σ.log []) ∗
        lease.leaseRevokers (mvccLeases γ.kv) L ∗ backend.rbPart B.γB (· = leaseName) r ∗
        lease.lessorBeOn lp B.be)
      iprop(w_ptr ↦ w ∗ id_ptr ↦ id ∗ mvccBackend γ.kv q (etcdStorage B) iprop(True) ∗
        lease.rdOwn (mvccLeases γ.kv) rd ∗ hookPost wv i ∗
        lease.leaseOwn (mvccLeases γ.kv) (L.filter (· != id))
          (leaseItemsOf (stateAfter (commitLog σ.log (leaseDels (stateAfter σ.log) id)))) ∗
        lease.leaseRevokers (mvccLeases γ.kv) (L.filter (· != id)) ∗
        backend.rbPart B.γB (· = leaseName) (rbDel r leaseName (u64Le id).reverse) ∗
        lease.lessorBeOn lp B.be) hok)
    $$ [Hrd Hgσ HW Hpv Hpd Htt w id Hbk Hrdo Hpre Hlo Hrvk Hrb Hbe]
    as ⟨Hrd, Htt, ⟨w, id, Hbk, Hrdo, Hpost, Hlo, Hrvk, Hrb, Hbe⟩, Hidle⟩
  · iframe Hw Hrd Hinv Hkv Hpd
    isplitl [Hgσ HW Hpv]
    · iunfold writerIdle; iframe; ipureintro; exact ⟨Hpn, Hlen, Hbound, Hmatch⟩
    iframe Htt w id Hbk Hrdo Hpre Hlo Hrvk Hrb Hbe
    -- the closure is `end`'s callback
    iunfold endCb
    iintro %Φ' ⟨Hgσ, #Hlb, Htt, w, id, Hbk, Hrdo, Hpre, Hlo, Hrvk, Hrb, Hbe⟩ HΦ'
    (try wp_auto)
    rw [HleEq]
    simp only
    (try wp_auto)
    ihave Hau := revoke_au hpers wv.h' γ σ Hs _ _ hok Hpn Hlen Hmatch $$ [$Hinv $Hgσ $Hlb]
    wp_apply hR $$ [Htt Hrdo Hbk Hpre Hlo Hrvk Hrb Hbe Hau]
      as %err ⟨Htt, Hrdo, Hbk, Hbe, Hres⟩
    · iframe Hlinv Htt Hrdo Hbk Hhook Hrvk Hrb Hbe
      isplitr
      · iunfold mvccDeleter; iframe Hdel; ipureintro; exact Hrdnn
      isplitl [Hpre]
      · iunfold srvApi.csContractA
        iframe Hpre
        isplitl
        · iapply Hhok
        iintro HQ
        imodintro
        iexact HQ
      isplitr
      · ipureintro; exact ⟨Hpn, by omega, Hreach, Hbound⟩
      isplitl [Hau]
      · simp only [hidL, decide_true, ↓reduceIte]
        iexact Hau
      isplitl [Hlo]
      · rw [← pendItems_nil]; iexact Hlo
      ipureintro; exact HlP
    icases Hres with (⟨%Hnin, -⟩ | ⟨%Hok2, HY, Hpost, Hlo, Hrvk, Hrb⟩)
    · exact absurd hidL Hnin
    obtain ⟨-, rfl⟩ := Hok2
    (try wp_auto)
    wp_apply wp_check
    · ipureintro; simp
    (try wp_auto)
    iapply HΦ'
    iframe
  -- after `end`: the hook's check, the model's lease gone, `Lookup` nil
  iunfold hookPost at Hpost
  icases Hpost with ⟨Happ, Hsav⟩
  (try wp_auto)
  wp_apply wp_checkHook w wv i $$ [$Hsav $Hw] as Hsav
  (try wp_auto)
  wp_apply (wp_mapDelete wv.leases' Lm id go.int64 go.bool) $$ [$Hlm] as Hlm
  (try wp_auto)
  rw [HleEq]
  simp only
  (try wp_auto)
  ihave ⟨Hlo, #Hlb0⟩ := lease.leaseOwn_lb (mvccLeases γ.kv) _ _ $$ Hlo
  wp_apply (wp_Lookup lp (mvccLeases γ.kv) id 0 (some (L.filter (· != id),
      leaseItemsOf (stateAfter (commitLog σ.log (leaseDels (stateAfter σ.log) id))))))
    $$ [Hlrd Hlo] as %l ⟨Hlrd, -, Ho⟩
  · iframe Hlinv Hlrd Hlb0; rw [lease.lookupView_some]; iexact Hlo
  ihave ⟨%Hl0, Ho⟩ : iprop(⌜l = null ↔ id ∉ L.filter (· != id)⌝ ∗
      ((⌜l = null⌝ ∗ lease.leaseOwn (mvccLeases γ.kv) (L.filter (· != id))
          (leaseItemsOf (stateAfter (commitLog σ.log (leaseDels (stateAfter σ.log) id))))) ∨
        lease.leaseOwnOpen (mvccLeases γ.kv) (L.filter (· != id))
          (leaseItemsOf (stateAfter (commitLog σ.log (leaseDels (stateAfter σ.log) id)))) id l))
    $$ [Ho]
  · rw [← lease.lookupViewAfter_some]; iexact Ho
  have hnin : id ∉ L.filter (· != id) := by simp
  have hlnull : l = null := Hl0.2 hnin
  ihave Hlo : lease.leaseOwn (mvccLeases γ.kv) (L.filter (· != id))
      (leaseItemsOf (stateAfter (commitLog σ.log (leaseDels (stateAfter σ.log) id)))) $$ [Ho]
  · icases Ho with (⟨-, Ho⟩ | Ho)
    · iexact Ho
    · iapply lease.leaseOwnOpen_close $$ Ho
  subst hlnull
  (try wp_auto)
  wp_apply wp_check
  · ipureintro; simp
  (try wp_auto)
  iapply HΦ
  iexists commitSt σ (leaseDels (stateAfter σ.log) id), _, id
  isplitl [Htt Hbk Hrd Hidle Hg Hlm Hlo]
  · iunfold writerOwn
    iframe Htt Hbk Hrd Hidle Hg
    isplitl [Hlm]
    · iexists (GMap.delete id Lm)
      iframe Hlm
      ipureintro
      intro x
      by_cases hx : x = id
      · subst hx; simp
      · rw [GMap.lookup_delete_ne _ (Ne.symm hx), HLm x]
        simp [hx]
    rw [pendItems_nil, commitSt_log]
    iexact Hlo
  isplitr [Happ Hsav]
  · iunfold writerLe
    iexists lp, rd, _
    iframe
    isplitl []
    · iexact Hro
    isplitl []
    · iunfold mvccDeleter; iframe Hdel; ipureintro; exact Hrdnn
    ipureintro
    refine ⟨HlP, Hn.1, fun x hx => Hn.2 x (List.mem_filter.1 hx).1⟩
  ileft
  iunfold hookPost
  iframe

end proof

end mvccrand
end EtcdGrove
end Perennial
