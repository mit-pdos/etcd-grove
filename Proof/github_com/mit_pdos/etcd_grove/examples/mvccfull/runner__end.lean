/- Lean-first (no Rocq counterpart). The proof of `runner.end`: proved.

The outline: for the leader with a change, `history.snapshot`'s length check against the
writer part, `history.appendRev`, the counter's `Add` (`ctrInv`); `end()` (`endCb`, at the history's
lower bound with the revision); `m.kv.Rev()` (`KV.Rev.contract` at the incarnation's invariant,
`reader_au`-like, the state `commitSt σ pend`, which the writer's half pins); `revLo`/`revHi` stored
(`m.bnd`'s halves).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__end
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.history__snapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.history__appendRev
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.check
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.EndLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.RestoreLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.WriterLemmas
public import Perennial.Spec.sync.atomic.Int64__Add

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem runner.end.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (wp_snapshot : history.snapshot.spec (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_appendRev : history.appendRev.spec (GF := GF) (hG := hG)) :
    runner.end.spec (GF := GF) (hG := hG) := by
  intro x ks h γh i mp m ι kv qw σ b Hs Cs p P pend e E E' lead hok hlen hpn hb hσ
  haveI := isInc_persistent hpers
  haveI := hpers.1
  wp_start as ⟨HH, Hctr, Hrd, Hrev, Hkvf, HincW, Hpend, Hlead, Hcb, HE⟩
  iunfold runnerH at HH
  icases HH with #HH
  iunfold ctrInv at Hctr
  icases Hctr with #Hctr
  iunfold ownPending at Hpend
  icases Hpend with ⟨%pv, Hp, %Hrev', Hst, Hchs, Hcap⟩
  ihave %Hcl := ownSlice_len $$ Hchs
  iunfold histRd at Hrd
  icases Hrd with ⟨#Hh, Hrd⟩
  have hPrev : P.rev = W64 (Hs.length : Int) := pendOk_rev' hok
  have hlenc : (sint.Z (W64 0) < sint.Z pv.changes'.len) ↔ P.chs ≠ [] := by
    have : sint.nat pv.changes'.len = (sint.Z pv.changes'.len).toNat := rfl
    rw [Ne, ← List.length_eq_zero_iff]
    constructor <;> intro h <;> word
  have hHs63 : (Hs.length : Int) < 2 ^ 63 := by
    have : σ.log.length - 1 + 2 < 2 ^ 63 := hσ
    omega
  wp_auto
  -- the leader's revision appended (if it has a change); the history's lower bound after it
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
      (if lead then histW γh (histAfter Hs P) Cs else iprop(True)) ∗
      monoListLbOwn γh.l (histAfter Hs P) ∗ sync.ownRWMutex (hMu h) (histR h γh) ∗
      p_ptr ↦ p ∗ x_ptr ↦ x ∗ (p ↦ pv)))) $$ [Hlead Hst Hchs Hp Hrd p x lead]
  · by_cases hc : P.chs = []
    · have h0 : ¬ (sint.Z (W64 0) < sint.Z pv.changes'.len) := fun h => hlenc.1 h hc
      simp only [h0, _root_.decide_false]
      wp_auto
      have hA : histAfter Hs P = Hs := by unfold histAfter; simp only [hc, ↓reduceIte]
      rw [hA]
      cases lead
      · simp only [Bool.false_eq_true, ↓reduceIte]
        iframe
      · simp only [↓reduceIte]
        icases histW_lb γh _ _ $$ Hlead with ⟨Hlead, #Hlb⟩
        iframe; iframe #
    · have h0 : sint.Z (W64 0) < sint.Z pv.changes'.len := hlenc.2 hc
      simp only [h0, _root_.decide_true]
      cases lead
      · simp only [Bool.false_eq_true, ↓reduceIte]
        wp_auto
        iframe
        ipureintro; rfl
      · simp only [↓reduceIte]
        wp_auto
        -- `check(len(x.h.snapshot()) == int(p.rev))`: the snapshot is the writer's history
        icases histW_lb γh _ _ $$ Hlead with ⟨Hlead, #Hlb0⟩
        wp_apply wp_snapshot h γh Hs $$ [Hrd] as %sl ⟨Hrd, %ms, %Hs', ⟨%Hpre, %Hl2⟩, %Hcap', #Hlb', #Hms, #HsP⟩
        · iunfold histRd; iframe; iframe #
        iunfold histW at Hlead
        icases Hlead with ⟨%xc, %Hx, Hg, Hl, Hc1, Hc2, Hc3⟩
        ihave %Hv := mono_list_auth_lb_valid γh.l _ _ _ $$ Hl Hlb'
        have hHs' : Hs' = Hs := Hv.2.eq_of_length (Nat.le_antisymm Hv.2.length_le Hpre.length_le)
        subst hHs'
        iunfold statesP at HsP
        icases HsP with ⟨%Hmsl, -⟩
        ihave %Hsl := ownSlice_len $$ Hms
        iunfold histRd at Hrd
        icases Hrd with ⟨-, Hrd⟩
        (try wp_auto)
        have hslen : sl.len = pv.rev' := by
          rw [Hrev', hPrev]
          obtain ⟨h1, h2⟩ := Hsl
          have : sint.nat sl.len = (sint.Z sl.len).toNat := rfl
          have hz : sint.Z sl.len = (Hs'.length : Int) := by omega
          have hl63 : (Hs'.length : Int) < 2 ^ 63 := by omega
          word
        wp_apply wp_check
        · ipureintro; simp [hslen]
        (try wp_auto)
        imod ownMap_persist _ _ _ $$ Hst with #Hst
        imod ownSlice_persist _ _ _ $$ Hchs with #Hchs
        ihave HW : histW γh Hs' Cs $$ [Hg Hl Hc1 Hc2 Hc3]
        · iunfold histW; iexists xc; iframe; ipureintro; exact Hx
        wp_apply wp_appendRev h γh Hs' Cs pv.st' P.st pv.changes' P.chs $$ [$Hh $HW $Hst $Hchs] as HW
        (try wp_auto)
        wp_apply_core sync.atomic.Int64.wp_Add (rF go!"revisions" x) (W64 1) $$ [] [-]
        · iPkgInit
        iinv Hctr with ⟨%a, >Ha⟩ Hclose
        iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑(readersN .@ "revisions") from
          Std.LawfulSet.empty_subset)
        iintro Hcl
        inext
        iexists a
        iframe
        iintro Ha
        imod Hcl with -
        imod Hclose $$ [Ha] with -
        · inext; iexists _; iframe
        imodintro
        (try wp_auto)
        have hA : histAfter Hs' P = Hs' ++ [(P.st, P.chs)] := by
          unfold histAfter; simp only [hc, ↓reduceIte]
        rw [hA]
        icases histW_lb γh _ _ $$ HW with ⟨HW, #Hlb2⟩
        iframe; iframe #
        try (ipureintro; rfl)
  iintro %v ⟨%hv, Hlead, #Hlb, Hrd, p, x, Hp⟩
  subst hv
  wp_auto
  -- `end()`
  wp_bind (App (Val #e) (Val #()))
  iunfold endCb at Hcb
  iapply Hcb $$ [$HincW $Hlb $HE]
  inext
  iintro ⟨HincW, Hrdr, HE'⟩
  -- the bounds' facts at the committed state
  imod incW_bndOk hpers ks γh i mp m ι kv qw (commitSt σ pend) b $$ HincW with ⟨HincW, %Hok0'⟩
  obtain ⟨Hl0, Hok0⟩ := Hok0'
  wp_auto
  -- `want`
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ want_ptr ↦ viewRev P ∗
      p_ptr ↦ p ∗ (p ↦ pv)))) $$ [want p Hp]
  · by_cases hc : P.chs = []
    · have h0 : ¬ (sint.Z (W64 0) < sint.Z pv.changes'.len) := fun h => hlenc.1 h hc
      simp only [h0, _root_.decide_false]
      wp_auto
      unfold viewRev; simp only [hc, ↓reduceIte, Hrev']
      iframe
    · have h0 : sint.Z (W64 0) < sint.Z pv.changes'.len := hlenc.2 hc
      simp only [h0, _root_.decide_true]
      wp_auto
      unfold viewRev; simp only [hc, ↓reduceIte, Hrev']
      iframe
  iintro %v ⟨%hv, want, p, Hp⟩
  subst hv
  have hc1 : 1 ≤ (commitSt σ pend).rev := by have := Hok0.1; have := Hok0.2.1; omega
  have h1 : 1 ≤ σ.log.length := by
    have hl := commitSt_log σ pend
    unfold MvccState.rev at hc1
    rw [hl] at hc1
    unfold commitLog at hc1
    split at hc1
    · omega
    · simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel] at hc1; omega
  rw [viewRev_commit ks σ Hs pend P hok hlen h1 (by unfold MvccState.rev at hσ; omega)]
  wp_auto
  -- `check(m.kv.Rev() == want)`: the state is the committed one, the writer's half pins it
  iunfold incW at HincW
  icases HincW with ⟨#Hinc, Hret, Hσw, Hbw⟩
  ihave #Hmv : isMvcc kv ι.kv $$ []
  · iunfold isInc at Hinc; icases Hinc with ⟨-, #H⟩; iexact H
  ihave %Hkvs := hsh.1 kv ι.kv $$ Hmv
  obtain ⟨kty, kvv, rfl, -, -, hKRev, -⟩ := Hkvs
  ihave Hau := read_au hpers ks γh i mp m ι (interface.mkOk kty kvv) qw (commitSt σ pend)
    $$ [Hret Hσw]
  · iframe #; iframe
  wp_apply (hKRev ι.kv (fun σ' => iprop(⌜σ' = commitSt σ pend⌝ ∗ ghostVar ι.ret qw () ∗
      ghostVar m.σ (1 : Qp).half (commitSt σ pend)))) $$ [Hrdr Hau]
    as %rv ⟨Hrdr, %σr, ⟨%Hσr, Hret, Hσw⟩, %Hrv⟩
  · iframe #; iframe
  subst Hσr Hrv
  (try wp_auto)
  wp_apply wp_check
  · ipureintro; simp
  (try wp_auto)
  -- `m.revLo.Store(want)`, `m.revHi.Store(want)`: the bounds at the committed revision
  have hr62 : ((commitSt σ pend).rev : Int) < 2 ^ 62 := by
    have := Hok0.2.2.1; have := Hok0.2.2.2.1; omega
  have hrZ : sint.Z (W64 ((commitSt σ pend).rev : Int)) = ((commitSt σ pend).rev : Int) := by word
  have hnl : ((commitSt σ pend).notifiedLog.length : Int) = (commitSt σ pend).rev + 1 := by
    rw [commitSt_notifiedLog_eq]
    have : (commitSt σ pend).rev = (commitSt σ pend).log.length - 1 := rfl
    omega
  wp_apply_core sync.atomic.Int64.wp_Store (mF go!"revLo" mp)
    (W64 ((commitSt σ pend).rev : Int)) $$ [] [-]
  · iPkgInit
  imod bnd_acc hpers ks γh i mp m ι (interface.mkOk kty kvv) qw (commitSt σ pend) b
    $$ [Hret Hσw Hbw] with ⟨%Hl1, %Hok1, Hrl, Hrh, Hcl, Hch, Hcls⟩
  · iframe #; iframe
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑(memberN i) from Std.LawfulSet.empty_subset)
  iintro Hcl2
  inext
  iexists _
  iframe Hrl
  iintro Hrl
  imod Hcl2 with -
  let b1 : Bnd := (W64 ((commitSt σ pend).rev : Int), b.2.1, b.2.2.1, b.2.2.2)
  have hok1 : bndOk ks (commitSt σ pend) b1 Hl1 := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := Hok1
    refine ⟨?_, ?_, h3, h4, h5, h6, h7, h8, h9, h10⟩
    · show 1 ≤ sint.Z (W64 ((commitSt σ pend).rev : Int)); rw [hrZ]; omega
    · show sint.Z (W64 ((commitSt σ pend).rev : Int)) ≤ ((commitSt σ pend).rev : Int)
      rw [hrZ]; exact Int.le_refl _
  imod Hcls $$ %b1 %hok1 Hrl Hrh Hcl Hch with ⟨Hret, Hσw, Hbw⟩
  imodintro
  (try wp_auto)
  wp_apply_core sync.atomic.Int64.wp_Store (mF go!"revHi" mp)
    (W64 ((commitSt σ pend).rev : Int)) $$ [] [-]
  · iPkgInit
  imod bnd_acc hpers ks γh i mp m ι (interface.mkOk kty kvv) qw (commitSt σ pend) b1
    $$ [Hret Hσw Hbw] with ⟨%Hl2, %Hok2, Hrl, Hrh, Hcl, Hch, Hcls⟩
  · iframe #; iframe
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑(memberN i) from Std.LawfulSet.empty_subset)
  iintro Hcl2
  inext
  iexists _
  iframe Hrh
  iintro Hrh
  imod Hcl2 with -
  let b2 : Bnd := (W64 ((commitSt σ pend).rev : Int), W64 ((commitSt σ pend).rev : Int), b.2.2.1,
    b.2.2.2)
  have hok2 : bndOk ks (commitSt σ pend) b2 Hl2 := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := Hok2
    refine ⟨h1, h2, ?_, ?_, ?_, h6, h7, h8, h9, h10⟩
    · show ((commitSt σ pend).rev : Int) ≤ sint.Z (W64 ((commitSt σ pend).rev : Int))
      rw [hrZ]; exact Int.le_refl _
    · show sint.Z (W64 ((commitSt σ pend).rev : Int)) < 2 ^ 62; rw [hrZ]; exact hr62
    · show ((commitSt σ pend).notifiedLog.length : Int) ≤ sint.Z (W64 ((commitSt σ pend).rev : Int)) + 1
      rw [hrZ, hnl]; exact Int.le_refl _
  imod Hcls $$ %b2 %hok2 Hrl Hrh Hcl Hch with ⟨Hret, Hσw, Hbw⟩
  imodintro
  (try wp_auto)
  iapply HΦ
  iframe
  isplitl [Hrd]
  · iunfold histRd; iframe; iframe #
  iunfold incW; iframe; iframe #

end proof

end mvccfull
end EtcdGrove
end Perennial
