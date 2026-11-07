/- Lean-first (no Rocq counterpart). The proof of `writer.end`: the pending revision (made
persistent) appended to the history when it has a change, the callback (`endCb`: the store's
`End`), the store's revision (`KV.Rev`, its update at the invariant's state, the writer's half of
`γ.σ` at `commitSt σ pend`) checked against `want`, and `published` stored in the tester's
invariant (both halves of `γ.pv` moved to the new revision, `γ.pub` bumped). -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__end
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.history__appendRev
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.check
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.TxnEnd

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccrand mvcc mvcc.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem writer.end.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_appendRev : history.appendRev.spec (GF := GF) (hG := hG)) :
    writer.end.spec (GF := GF) (hG := hG) := by
  intro w wv γ σ Hs p P pend e E E' hok
  haveI := hpers.1
  haveI := fun σ => hpers.2.2.2.2.2.1 γ.kv σ
  haveI := fun S => hpers.2.2.2.2.2.2.1 γ.ws S
  haveI : Timeless (worldInv (GF := GF) wv.h' γ) := by unfold worldInv; infer_instance
  have hdisj : (↑worldN : CoPset) ⊆ ⊤ \ ↑mvccN :=
    nclose_subseteq' "world" (mask_ndot_ne' nroot "mvccrand" "mvcc" (by decide))
  wp_start as ⟨#Hw, Hrd, #Hinv, #Hkv, Hidle, Hpend, Hcb, HE⟩
  iunfold writerIdle at Hidle
  icases Hidle with ⟨Hgσ, HW, Hpv, %Hid⟩
  obtain ⟨Hpn, Hlen, Hbound, Hmatch⟩ := Hid
  ihave #Hw2 := Hw
  iunfold writerRO at Hw2
  icases Hw2 with ⟨#kvW, #leW, #hW, #rW, #leasesW, #applyingW, #savedW, #ticksW⟩
  iunfold ownPending at Hpend
  icases Hpend with ⟨%pv, Hp, %Hrev, Hst, Hchs, Hcap⟩
  ihave %Hcl := ownSlice_len $$ Hchs
  iunfold histRd at Hrd
  icases Hrd with ⟨#Hh, Hrd⟩
  have hPrev : P.rev = W64 (Hs.length : Int) := by rw [hok.1]; exact pendOf_rev _ _ _
  have hlenc : (sint.Z (W64 0) < sint.Z pv.changes'.len) ↔ P.chs ≠ [] := by
    have : sint.nat pv.changes'.len = (sint.Z pv.changes'.len).toNat := rfl
    rw [Ne, ← List.length_eq_zero_iff]
    constructor <;> intro h <;> word
  wp_auto
  -- the history after `appendRev` (if the pending revision has a change)
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ histW γ.h (histAfter Hs P) ∗
      p_ptr ↦ p ∗ w_ptr ↦ w ∗ (p ↦ pv)))) $$ [HW Hst Hchs Hp p w]
  · by_cases hc : P.chs = []
    · have h0 : ¬ (sint.Z (W64 0) < sint.Z pv.changes'.len) := fun h => hlenc.1 h hc
      simp only [h0, _root_.decide_false]
      wp_auto
      unfold histAfter; simp only [hc, ↓reduceIte]
      iframe
    · have h0 : sint.Z (W64 0) < sint.Z pv.changes'.len := hlenc.2 hc
      simp only [h0, _root_.decide_true]
      wp_auto
      imod ownMap_persist _ _ _ $$ Hst with #Hst
      imod ownSlice_persist _ _ _ $$ Hchs with #Hchs
      wp_apply wp_appendRev wv.h' γ.h Hs pv.st' P.st pv.changes' P.chs $$ [$Hh $HW $Hst $Hchs] as HW
      (try wp_auto)
      unfold histAfter; simp only [hc, ↓reduceIte]
      iframe
  iintro %v ⟨%hv, HW, p, w, Hp⟩
  subst hv
  wp_auto
  -- `end()`
  icases histW_lb γ.h _ $$ HW with ⟨HW, #Hlb⟩
  wp_bind (App (Val #e) (Val #()))
  iunfold endCb at Hcb
  iapply Hcb $$ [$Hgσ $Hlb $HE]
  inext
  iintro ⟨Hgσ, Hrdr, HE'⟩
  wp_auto
  -- `want`
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ want_ptr ↦ viewRev P ∗
      p_ptr ↦ p ∗ (p ↦ pv)))) $$ [want p Hp]
  · by_cases hc : P.chs = []
    · have h0 : ¬ (sint.Z (W64 0) < sint.Z pv.changes'.len) := fun h => hlenc.1 h hc
      simp only [h0, _root_.decide_false]
      wp_auto
      unfold viewRev; simp only [hc, ↓reduceIte, Hrev]
      iframe
    · have h0 : sint.Z (W64 0) < sint.Z pv.changes'.len := hlenc.2 hc
      simp only [h0, _root_.decide_true]
      wp_auto
      unfold viewRev; simp only [hc, ↓reduceIte, Hrev]
      iframe
  iintro %v ⟨%hv, want, p, Hp⟩
  subst hv
  -- `w.kv.Rev()`: its update at the invariant's state, the writer's
  ihave %Hsh := hsh.1 wv.kv' γ.kv $$ Hkv
  obtain ⟨kty, kvv, hkv, -, -, hRevC, -⟩ := Hsh
  ihave #kvW' : (wF go!"kv" w ↦□ interface.mkOk kty kvv : IProp GF) $$ [kvW]
  · rw [← hkv]; iexact kvW
  ihave #Hkv' : isMvcc (interface.mkOk kty kvv) γ.kv $$ [Hkv]
  · rw [← hkv]; iexact Hkv
  iclear kvW
  wp_auto
  wp_apply (hRevC γ.kv (fun σ' => iprop(⌜σ' = commitSt σ pend ∧ σ'.log.length + 3 ≤ 2 ^ 63 ∧
      1 ≤ σ'.rev⌝ ∗ ghostVar γ.σ (1 : Qp).half (commitSt σ pend)))) $$ [$Hkv' $Hrdr Hgσ]
    as %r ⟨Hrdr, %σ', ⟨%Hq, Hgσ⟩, %Hr⟩
  · iauintro
    unfold atomic_acc
    iinv Hinv with >Hi Hclose
    iunfold worldInv at Hi
    icases Hi with ⟨%σ1, %S, %p1, %Hl, %W, Hs, Hgσ1, HS, Hreg, Hpub, Hpv1, Hpm, Hlb1, %Hok⟩
    ihave %Hag := ghostVar_agree γ.σ _ _ _ _ $$ Hgσ1 Hgσ
    subst Hag
    icases (persistent_entails_right (hreach _ γ.kv _)) $$ [$Hkv' $Hs] with ⟨%Hre, -, Hs⟩
    iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑mvccN) \ ↑worldN from
      Std.LawfulSet.empty_subset)
    iintro Hclose2
    isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
    iexists _
    iframe Hs
    isplit
    · iintro Hs
      imod Hclose2 with -
      imod Hclose $$ [Hs Hgσ1 HS Hreg Hpub Hpv1 Hpm Hlb1] with -
      · inext; iunfold worldInv; iexists _, S, p1, Hl, W; iframe; ipureintro; exact Hok
      imodintro
      iframe Hgσ
    · iintro Hs
      imod Hclose2 with -
      imod Hclose $$ [Hs Hgσ1 HS Hreg Hpub Hpv1 Hpm Hlb1] with -
      · inext; iunfold worldInv; iexists _, S, p1, Hl, W; iframe; ipureintro; exact Hok
      imodintro
      iframe Hgσ
      ipureintro
      obtain ⟨-, h2, h3, -, -⟩ := Hok
      refine ⟨rfl, Hre.2, ?_⟩
      have : sint.nat p1 = (sint.Z p1).toNat := rfl
      omega
  obtain ⟨rfl, hb, h1⟩ := Hq
  subst Hr
  -- the revision is `want`
  have hco := histOk_commit σ Hs pend P hok Hlen Hmatch
  have hcl := commitSt_log σ pend
  have hnil : P.chs = [] ↔ pend = [] := by rw [hok.1]; exact pendOf_chs_nil_iff _ _ _
  have hwant : viewRev P = W64 ((commitSt σ pend).rev : Int) := by
    unfold viewRev MvccState.rev at *
    rw [hcl] at h1 ⊢
    rw [hPrev, Hlen]
    by_cases hp : pend = []
    · have hc : P.chs = [] := hnil.2 hp
      simp only [hc, ↓reduceIte, commitLog, hp] at h1 ⊢
      have : ((σ.log.length - 1 : Nat) : Int) = (σ.log.length : Int) - 1 := by omega
      rw [this]; word
    · have hc : P.chs ≠ [] := fun h => hp (hnil.1 h)
      simp only [hc, ↓reduceIte, commitLog, hp, List.length_append, List.length_singleton,
        Nat.add_sub_cancel]
  (try wp_auto)
  wp_apply wp_check
  · ipureintro; simp only [hwant, decide_true]
  (try wp_auto)
  -- `published.Store(want)`: the invariant's cell, both halves of `γ.pv`, `γ.pub` bumped
  rw [hwant]
  wp_apply_core sync.atomic.Int64.wp_Store (hPub wv.h') (W64 ((commitSt σ pend).rev : Int)) $$ [] [-]
  · iPkgInit
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑worldN from Std.LawfulSet.empty_subset)
  iintro Hcl
  inext
  iunfold worldInv at Hi
  icases Hi with ⟨%σ1, %S, %p1, %Hl, %W, Hs, Hgσ1, HS, Hreg, Hpub, Hpv1, Hpm, Hlb1, %Hok⟩
  ihave %Hag := ghostVar_agree γ.σ _ _ _ _ $$ Hgσ1 Hgσ
  subst Hag
  ihave %Hagp := ghostVar_agree γ.pv _ _ _ _ $$ Hpv1 Hpv
  subst Hagp
  iexists _
  iframe Hpub
  iintro Hpub
  imod ghostVar_update_halves (W64 ((commitSt σ pend).rev : Int)) γ.pv _ _ $$ Hpv1 Hpv
    with ⟨Hpv1, Hpv⟩
  have hr := commitSt_rev_ge σ pend
  have hnat : ∀ n : Nat, n < 2 ^ 63 → sint.nat (W64 (n : Int)) = n := by
    intro n hn
    have : sint.nat (W64 (n : Int)) = (sint.Z (W64 (n : Int))).toNat := rfl
    rw [this]; word
  have hrev63 : (commitSt σ pend).rev < 2 ^ 63 := by unfold MvccState.rev; omega
  have hσ63 : σ.rev < 2 ^ 63 := by omega
  imod mono_nat_own_update (sint.nat (W64 ((commitSt σ pend).rev : Int))) (by
    rw [hnat _ hrev63, hnat _ hσ63]; exact hr) $$ Hpm with ⟨Hpm, -⟩
  imod Hcl with -
  imod Hclose $$ [Hs Hgσ1 HS Hreg Hpub Hpv1 Hpm Hlb1] with -
  · inext; iunfold worldInv; iexists _, S, _, Hl, W; iframe
    ipureintro
    obtain ⟨h1', -, -, h4, h5⟩ := Hok
    refine ⟨h1', ?_, ?_, h4, h5⟩
    · have : sint.Z (W64 ((commitSt σ pend).rev : Int)) = ((commitSt σ pend).rev : Int) := by word
      rw [this]; omega
    · rw [hnat _ hrev63]; exact Nat.le_refl _
  imodintro
  wp_auto
  iapply HΦ
  iframe
  isplitl [Hrd]
  · iunfold histRd; iframe; iframe #
  iunfold writerIdle
  iframe
  ipureintro
  refine ⟨rfl, by rw [hcl]; exact hco.1, hb, ?_⟩
  rw [hcl]; exact hco.2

end proof

end mvccrand
end EtcdGrove
end Perennial
