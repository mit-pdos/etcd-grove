/- Lean-first (no Rocq counterpart). The proof of `runner.compact`: proved but for the two `ch ≠ nil` checks (a gap of the frozen mvcc API).

The outline: the three cases on `m.cmp`, `m.rev` (`σOf`'s, the writer's half); `cmpHi.Store`
(`incW`); `KV.Compact.contract` (its update at the incarnation's invariant, `compactTo`, the bounds
`cmpLo ≤ crev ≤ cmpHi`; the hook at `a`; the storage's commit request `True`); `compactChanOk`'s
receive; `cmpLo.Store`; `history.addComp` and the counter for the leader.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__compact
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.history__addComp
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.check
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.TODO
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.CompactLemmas
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

theorem runner.compact.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hev : mvcc.api.errVars.law (GF := GF) (hG := hG))
    (wp_traceTODO : traceutil.TODO.spec (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_addComp : history.addComp.spec (GF := GF) (hG := hG)) :
    runner.compact.spec (GF := GF) (hG := hG) := by
  intro x ks cfg wr h γh ops i mp m f v qw nw k p o lead a s hov hkind hlog h38 ha hsa
  haveI := isInc_persistent hpers
  haveI := hpers.1
  haveI := hpers.2.2.2.1
  haveI : ∀ ch, Persistent (compactChanOk (GF := GF) ch) := by
    intro ch; unfold compactChanOk; infer_instance
  haveI : ∀ N l, Persistent (ctrInv (GF := GF) N l) := by intro N l; unfold ctrInv; infer_instance
  wp_start as ⟨#Hctx, #Hop, Hc, Hpre, Hlead⟩
  ihave #Hctx2 := Hctx
  iunfold writerCtx at Hctx2
  icases Hctx2 with ⟨#Hrn, -, -, -, -, -, -, #Hpt, %Hkl, -, -, -, -, -, #Hccp, -, -, -⟩
  ihave #Hrn2 := Hrn
  iunfold rnCtx at Hrn2
  icases Hrn2 with ⟨#Hpkg, #Hpm, #Hrk, -, #HH, #Hhist, -⟩
  iunfold runnerH at HH
  iunfold ctrInv at Hccp
  iunfold opIs at Hop
  icases Hop with ⟨%ov, %subs, #Hov, -, -, -, -, -, -, %Hovs⟩
  obtain ⟨-, -, -, -, -, -, -, hrev, hwait⟩ := Hovs
  iunfold memCore at Hc
  icases Hc with ⟨Hid, Hhook, Hhok, Hpath, Hbe, Hle, Hkvf, Hrevf, Hcmpf, Hlsl, %Hvle, HincW,
    Hopen, Hmb, #Hhis, Hrds, Hbk, HlW, %HU⟩
  icases typedPointsto_split _ _ _ $$ Hov with #Hovf
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hovf
  ihave %Hsorted : ⌜ks.Pairwise go.GoStringLt⌝ $$ []
  · iunfold runnerKeys at Hrk; icases Hrk with ⟨%keys, -, -, %H, -⟩; ipureintro; exact H
  -- the model
  have hvo : v.ops < ops.length := (List.getElem?_eq_some_iff.1 hov).1
  obtain ⟨hS, hR, hC, hL, hG, hH, hCs⟩ := σOf_compact ks ops v.ops o hov hkind
  have hreach := (logOk_hist ks Hsorted ops hlog v.ops v.ops (Nat.le_refl _) (by omega)).2.2
  obtain ⟨-, hcr1, hcr2⟩ := reach_bounds _ hreach
  have hhl := runM_hs_len ks ops v.ops
  have hrv : ((σOf ks ops v.ops).rev : Int) = (revAfter ks ops v.ops : Int) := by rw [σOf_rev]
  have hrv38 : (revAfter ks ops v.ops : Int) < 2 ^ 39 := by
    unfold revAfter MSt.rev; omega
  have hcmpZ : sint.Z (W64 (cmpAfter ks ops v.ops)) = cmpAfter ks ops v.ops := by
    have : cmpAfter ks ops v.ops = (σOf ks ops v.ops).crev := rfl
    have : cmpAfter ks ops v.ops ≤ (revAfter ks ops v.ops : Int) := by omega
    word
  have hrevZ : sint.Z (W64 (revAfter ks ops v.ops : Int)) = (revAfter ks ops v.ops : Int) := by
    word
  have hc1 : 1 ≤ sint.Z o.rev := ((hlog v.ops o hov).2.2.2.2.2.2) hkind
  -- the store's handle
  iunfold incW at HincW
  icases HincW with ⟨#Hinc, Hret, Hσw, Hbw⟩
  ihave #Hmv : isMvcc v.kv v.ι.kv $$ []
  · iunfold isInc at Hinc; icases Hinc with ⟨-, #H⟩; iexact H
  ihave %Hkvs := hsh.1 v.kv v.ι.kv $$ Hmv
  obtain ⟨kty, kvv, hkv, -, -, -, -, -, -, -, hKC, -⟩ := Hkvs
  iunfold hookOk at Hhok
  icases Hhok with ⟨%Hfnil, #Hrun⟩
  ihave #Hreq : storageReq (etcdStorage v.bk) iprop(True) iprop(True) iprop(True) $$ []
  · rw [etcdStorage_req]; iapply backend.commitReq_true
  ihave Hinit := hev $$ Hpm
  icases Hinit with ⟨#HeCmp, #HeFut, -⟩
  iunfold errorsNewVar at HeFut
  icases HeFut with ⟨%xf, #HeFut, -⟩
  iunfold errorsNewVar at HeCmp
  icases HeCmp with ⟨%xc, #HeCmp, -⟩
  wp_auto
  rw [hrev]
  rw [hcmpZ]
  by_cases hA : sint.Z o.rev ≤ cmpAfter ks ops v.ops
  · -- at or below the compaction revision: `ErrCompacted`
    have hncok : ¬ ((σOf ks ops v.ops).crev < sint.Z o.rev ∧
        sint.Z o.rev ≤ ((σOf ks ops v.ops).rev : Int)) := fun h => by
      have : (σOf ks ops v.ops).crev = cmpAfter ks ops v.ops := rfl
      omega
    have hcab : (σOf ks ops v.ops).crev < sint.Z o.rev ∧
        sint.Z o.rev ≤ ((σOf ks ops v.ops).rev : Int) → sint.Z o.rev ≤ sint.Z v.b.2.2.2 :=
      fun h => absurd h hncok
    simp only [hA, _root_.decide_true]
    (try wp_auto)
    wp_apply wp_traceTODO $$ [$Hpt] as %trc ⟨%Htrc, Htrco⟩
    (try wp_auto)
    rw [hkv]
    (try wp_auto)
    ihave Hau := compact_au hpers ks γh i mp m v.ι (interface.mkOk kty kvv) qw (σOf ks ops v.ops) v.b (sint.Z o.rev)
      hcab $$ [Hret Hσw Hbw]
    · iframe #; iframe
    ihave Hrun1 := Hrun $$ %a %s
    wp_apply (hKC v.ι.kv trc true o.rev 1 (etcdStorage v.bk) iprop(True) f (hookPre mp a s)
        iprop(True ∗ hookPost mp a) (hookPost mp a) iprop(True) iprop(True)
        (fun σ' => iprop(⌜σ' = σOf ks ops v.ops⌝ ∗ ghostVar v.ι.ret qw () ∗
          ghostVar m.σ (1 : Qp).half
            (if (σOf ks ops v.ops).crev < sint.Z o.rev ∧ sint.Z o.rev ≤ ((σOf ks ops v.ops).rev : Int)
              then (σOf ks ops v.ops).compactTo (sint.Z o.rev) else σOf ks ops v.ops) ∗
          ghostVar m.bnd (1 : Qp).half v.b)))
      $$ [Hopen Htrco Hmb Hpre Hrun1 Hau]
      as %ch %err ⟨Hopen, Htrco, Hmb, %σr, ⟨%Hσr, Hret, Hσw, Hbw⟩, Hout⟩
    · iframe #; iframe
      isplitr
      · ipureintro; exact Htrc
      isplitr
      · ipureintro; exact hc1
      iintro ⟨-, Hq⟩; imodintro; iframe
    subst Hσr
    icases Hout with (⟨%Hc, -⟩ | ⟨%Hc, #Herr, Hpre, -, #Hch⟩ | ⟨%Hc, -⟩)
    · exfalso; exact hncok Hc.2
    rotate_left
    · exfalso; have : (σOf ks ops v.ops).crev = cmpAfter ks ops v.ops := rfl; omega
    ihave %Hag := typedPointsto_agree_wand _ _ _ _ _ $$ Herr HeCmp
    subst Hag
    (try wp_auto)
    have hchn : ch ≠ chan.nil := by
      -- SPEC GAP (frozen mvcc API): KV.Compact.contract gives no ch ≠ nil (notes/mvccfull-prove-writer.md)
      sorry
    wp_apply wp_check
    · ipureintro; simp [hchn]
    (try wp_auto)
    wp_bind (If _ _ _)
    iapply (wp_wand (Φ := fun w => iprop(⌜w = executeVal⌝ ∗ ch_ptr ↦ ch))) $$ [ch]
    · (try wp_auto)
      rcases Bool.eq_false_or_eq_true ov.wait' with hw | hw <;> rw [hw]
      · iunfold compactChanOk at Hch
        (try wp_auto)
        wp_apply Hch
        iintro %r -
        -- SPEC GAP (frozen mvcc API): `compactChanOk`'s receive returns any value, not the
        -- receive's pair, so `<-ch` (its `Fst`) is not provable (notes/mvccfull-prove-writer.md)
        sorry
      · (try wp_auto); iframe; ipureintro; rfl
    iintro %w ⟨%hw, ch⟩
    subst hw
    (try wp_auto)
    iapply HΦ
    isplitl [Hlead]
    · cases lead
      · unfold leadPost; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
      · irevert Hlead
        unfold leadPre leadPost
        simp only [↓reduceIte]
        rw [hH, hCs, if_neg hncok]
        iintro H; iexact H
    isplitl [Hpre]
    · iright; iexact Hpre
    iexists ⟨v.path, v.lp, v.kv, v.ops + 1, v.bk, v.ι, v.U, v.b⟩
    isplitr
    · ipureintro; exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
    iapply memCore_compact ks γh ops i mp m f v qw nw k o v.b hov hkind
    rw [hkv]
    rw [hC, hS]
    simp only [hncok, ↓reduceIte]
    rw [show (σOf ks ops v.ops).crev = cmpAfter ks ops v.ops from rfl]
    iframe Hid Hhook Hpath Hbe Hle Hkvf Hrevf Hcmpf Hlsl Hopen Hmb Hrds Hbk HlW
    iframe #
    isplitr
    · iunfold hookOk; iframe #; ipureintro; exact Hfnil
    isplitl [Hret Hσw Hbw]
    · iunfold incW; iframe #; iframe
      have hncok' : ¬ (cmpAfter ks ops v.ops < sint.Z o.rev ∧
          sint.Z o.rev ≤ ((σOf ks ops v.ops).rev : Int)) := hncok
      irevert Hσw
      simp only [hncok', hncok, ↓reduceIte]
      iintro H; iexact H
    ipureintro; exact HU
  rw [decide_eq_false hA]
  (try wp_auto)
  rw [hrevZ]
  by_cases hB : (revAfter ks ops v.ops : Int) < sint.Z o.rev
  · -- past the current revision: `ErrFutureRev`
      have hncok : ¬ ((σOf ks ops v.ops).crev < sint.Z o.rev ∧
          sint.Z o.rev ≤ ((σOf ks ops v.ops).rev : Int)) := fun h => by
        have : (σOf ks ops v.ops).crev = cmpAfter ks ops v.ops := rfl
        rw [hrv] at h
        omega
      have hcab : (σOf ks ops v.ops).crev < sint.Z o.rev ∧
          sint.Z o.rev ≤ ((σOf ks ops v.ops).rev : Int) → sint.Z o.rev ≤ sint.Z v.b.2.2.2 :=
        fun h => absurd h hncok
      simp only [hB, _root_.decide_true]
      (try wp_auto)
      wp_apply wp_traceTODO $$ [$Hpt] as %trc ⟨%Htrc, Htrco⟩
      (try wp_auto)
      rw [hkv]
      (try wp_auto)
      ihave Hau := compact_au hpers ks γh i mp m v.ι (interface.mkOk kty kvv) qw (σOf ks ops v.ops) v.b (sint.Z o.rev)
        hcab $$ [Hret Hσw Hbw]
      · iframe #; iframe
      ihave Hrun1 := Hrun $$ %a %s
      wp_apply (hKC v.ι.kv trc true o.rev 1 (etcdStorage v.bk) iprop(True) f (hookPre mp a s)
          iprop(True ∗ hookPost mp a) (hookPost mp a) iprop(True) iprop(True)
          (fun σ' => iprop(⌜σ' = σOf ks ops v.ops⌝ ∗ ghostVar v.ι.ret qw () ∗
            ghostVar m.σ (1 : Qp).half
              (if (σOf ks ops v.ops).crev < sint.Z o.rev ∧ sint.Z o.rev ≤ ((σOf ks ops v.ops).rev : Int)
                then (σOf ks ops v.ops).compactTo (sint.Z o.rev) else σOf ks ops v.ops) ∗
            ghostVar m.bnd (1 : Qp).half v.b)))
        $$ [Hopen Htrco Hmb Hpre Hrun1 Hau]
        as %ch %err ⟨Hopen, Htrco, Hmb, %σr, ⟨%Hσr, Hret, Hσw, Hbw⟩, Hout⟩
      · iframe #; iframe
        isplitr
        · ipureintro; exact Htrc
        isplitr
        · ipureintro; exact hc1
        iintro ⟨-, Hq⟩; imodintro; iframe
      subst Hσr
      icases Hout with (⟨%Hc, -⟩ | ⟨%Hc, -⟩ | ⟨%Hc, #Herr, Hpre, -⟩)
      · exfalso; exact hncok Hc.2
      · exfalso; have := hrv; omega
      obtain ⟨-, rfl⟩ := Hc
      ihave %Hag := typedPointsto_agree_wand _ _ _ _ _ $$ Herr HeFut
      subst Hag
      (try wp_auto)
      wp_apply wp_check
      · ipureintro; simp
      (try wp_auto)
      iapply HΦ
      isplitl [Hlead]
      · cases lead
        · unfold leadPost; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
        · irevert Hlead
          unfold leadPre leadPost
          simp only [↓reduceIte]
          rw [hH, hCs, if_neg hncok]
          iintro H; iexact H
      isplitl [Hpre]
      · iright; iexact Hpre
      iexists ⟨v.path, v.lp, v.kv, v.ops + 1, v.bk, v.ι, v.U, v.b⟩
      isplitr
      · ipureintro; exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
      iapply memCore_compact ks γh ops i mp m f v qw nw k o v.b hov hkind
      rw [hkv]
      rw [hC, hS]
      simp only [hncok, ↓reduceIte]
      rw [show (σOf ks ops v.ops).crev = cmpAfter ks ops v.ops from rfl]
      iframe Hid Hhook Hpath Hbe Hle Hkvf Hrevf Hcmpf Hlsl Hopen Hmb Hrds Hbk HlW
      iframe #
      isplitr
      · iunfold hookOk; iframe #; ipureintro; exact Hfnil
      isplitl [Hret Hσw Hbw]
      · iunfold incW; iframe #; iframe
        have hncok' : ¬ (cmpAfter ks ops v.ops < sint.Z o.rev ∧
            sint.Z o.rev ≤ ((σOf ks ops v.ops).rev : Int)) := hncok
        irevert Hσw
        simp only [hncok', hncok, ↓reduceIte]
        iintro H; iexact H
      ipureintro; exact HU
  -- above the compaction revision, at most the current one: the compaction
  rw [decide_eq_false hB]
  (try wp_auto)
  have hcr0 : (σOf ks ops v.ops).crev = cmpAfter ks ops v.ops := rfl
  have hcok : (σOf ks ops v.ops).crev < sint.Z o.rev ∧
      sint.Z o.rev ≤ ((σOf ks ops v.ops).rev : Int) := ⟨by omega, by rw [hrv]; omega⟩
  -- `m.cmpHi.Store(c)`
  wp_apply_core sync.atomic.Int64.wp_Store (mF go!"cmpHi" mp) o.rev $$ [] [-]
  · iPkgInit
  imod bnd_acc hpers ks γh i mp m v.ι v.kv qw (σOf ks ops v.ops) v.b
    $$ [Hret Hσw Hbw] with ⟨%Hl1, %Hok1, Hrl, Hrh, Hcl, Hchi, Hcls⟩
  · iframe #; iframe
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑(memberN i) from Std.LawfulSet.empty_subset)
  iintro Hcl2
  inext
  iexists _
  iframe Hchi
  iintro Hchi
  imod Hcl2 with -
  let b1 : Bnd := (v.b.1, v.b.2.1, v.b.2.2.1, o.rev)
  have hok1 : bndOk ks (σOf ks ops v.ops) b1 Hl1 := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := Hok1
    exact ⟨h1, h2, h3, h4, h5, h6, by show (σOf ks ops v.ops).crev ≤ sint.Z o.rev; omega, h8, h9, h10⟩
  imod Hcls $$ %b1 %hok1 Hrl Hrh Hcl Hchi with ⟨Hret, Hσw, Hbw⟩
  imodintro
  (try wp_auto)
  have hcab : (σOf ks ops v.ops).crev < sint.Z o.rev ∧
      sint.Z o.rev ≤ ((σOf ks ops v.ops).rev : Int) → sint.Z o.rev ≤ sint.Z b1.2.2.2 :=
    fun _ => Int.le_refl _
  wp_apply wp_traceTODO $$ [$Hpt] as %trc ⟨%Htrc, Htrco⟩
  (try wp_auto)
  rw [hkv]
  (try wp_auto)
  ihave Hau := compact_au hpers ks γh i mp m v.ι (interface.mkOk kty kvv) qw (σOf ks ops v.ops) b1
    (sint.Z o.rev) hcab $$ [Hret Hσw Hbw]
  · iframe #; iframe
  ihave Hrun1 := Hrun $$ %a %s
  wp_apply (hKC v.ι.kv trc true o.rev 1 (etcdStorage v.bk) iprop(True) f (hookPre mp a s)
      iprop(True ∗ hookPost mp a) (hookPost mp a) iprop(True) iprop(True)
      (fun σ' => iprop(⌜σ' = σOf ks ops v.ops⌝ ∗ ghostVar v.ι.ret qw () ∗
        ghostVar m.σ (1 : Qp).half
          (if (σOf ks ops v.ops).crev < sint.Z o.rev ∧ sint.Z o.rev ≤ ((σOf ks ops v.ops).rev : Int)
            then (σOf ks ops v.ops).compactTo (sint.Z o.rev) else σOf ks ops v.ops) ∗
        ghostVar m.bnd (1 : Qp).half b1)))
    $$ [Hopen Htrco Hmb Hpre Hrun1 Hau]
    as %ch %err ⟨Hopen, Htrco, Hmb, %σr, ⟨%Hσr, Hret, Hσw, Hbw⟩, Hout⟩
  · iframe #; iframe
    isplitr
    · ipureintro; exact Htrc
    isplitr
    · ipureintro; exact hc1
    iintro ⟨-, Hq⟩; imodintro; iframe
  subst Hσr
  icases Hout with (⟨%Hc, Hpost, -, #Hch⟩ | ⟨%Hc, -⟩ | ⟨%Hc, -⟩)
  rotate_left
  · exfalso; omega
  · exfalso; have := hrv; omega
  obtain ⟨rfl, -, -⟩ := Hc
  (try wp_auto)
  have hchn : ch ≠ chan.nil := by
    -- SPEC GAP (frozen mvcc API): KV.Compact.contract gives no ch ≠ nil (notes/mvccfull-prove-writer.md)
    sorry
  wp_apply wp_check
  · ipureintro; simp [hchn]
  (try wp_auto)
  -- `m.cmpLo.Store(c)`, at the compacted state
  let σc := (σOf ks ops v.ops).compactTo (sint.Z o.rev)
  have hcok' : cmpAfter ks ops v.ops < sint.Z o.rev := hcok.1
  irevert Hσw
  simp only [hcok, hcok', _root_.and_self, true_and, and_true, ↓reduceIte]
  iintro Hσw
  wp_apply_core sync.atomic.Int64.wp_Store (mF go!"cmpLo" mp) o.rev $$ [] [-]
  · iPkgInit
  imod bnd_acc hpers ks γh i mp m v.ι (interface.mkOk kty kvv) qw σc b1
    $$ [Hret Hσw Hbw] with ⟨%Hl2, %Hok2, Hrl, Hrh, Hcl, Hchi, Hcls⟩
  · iframe #; iframe
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑(memberN i) from Std.LawfulSet.empty_subset)
  iintro Hcl2
  inext
  iexists _
  iframe Hcl
  iintro Hcl
  imod Hcl2 with -
  let b2 : Bnd := (b1.1, b1.2.1, o.rev, o.rev)
  have hok2 : bndOk ks σc b2 Hl2 := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := Hok2
    exact ⟨h1, h2, h3, h4, h5, by show sint.Z o.rev ≤ sint.Z o.rev; exact Int.le_refl _, h7, h8,
      h9, h10⟩
  imod Hcls $$ %b2 %hok2 Hrl Hrh Hcl Hchi with ⟨Hret, Hσw, Hbw⟩
  imodintro
  (try wp_auto)
  -- the leader's compaction recorded
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun w => iprop(⌜w = executeVal⌝ ∗ leadPost γh ks ops v.ops lead ∗
      c_ptr ↦ o.rev ∗ x_ptr ↦ x))) $$ [Hlead c x]
  · cases lead
    · (try wp_auto)
      unfold leadPost; simp only [Bool.false_eq_true, ↓reduceIte]
      iframe
    · (try wp_auto)
      irevert Hlead
      unfold leadPre leadPost
      simp only [↓reduceIte]
      rw [hH, hCs, if_pos hcok]
      iintro Hlead
      (try wp_auto)
      wp_apply wp_addComp h γh (histAt ks ops v.ops) (compsAt ks ops v.ops) o.rev
        $$ [$Hhist $Hlead] as Hlead
      (try wp_auto)
      wp_apply_core sync.atomic.Int64.wp_Add (rF go!"compactions" x) (W64 1) $$ [] [-]
      · iPkgInit
      iinv Hccp with ⟨%av, >Ha⟩ Hclose
      iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑(readersN .@ "compactions") from
        Std.LawfulSet.empty_subset)
      iintro Hcl3
      inext
      iexists av
      iframe
      iintro Ha
      imod Hcl3 with -
      imod Hclose $$ [Ha] with -
      · inext; iexists _; iframe
      imodintro
      (try wp_auto)
      iframe; ipureintro; rfl
  iintro %w ⟨%hw, Hlead, c, x⟩
  subst hw
  (try wp_auto)
  -- the wait
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun w => iprop(⌜w = executeVal⌝ ∗ ch_ptr ↦ ch))) $$ [ch]
  · (try wp_auto)
    rcases Bool.eq_false_or_eq_true ov.wait' with hw | hw <;> rw [hw]
    · iunfold compactChanOk at Hch
      (try wp_auto)
      wp_apply Hch
      iintro %r -
      -- SPEC GAP (frozen mvcc API): `compactChanOk`'s receive returns any value, not the
      -- receive's pair, so `<-ch` (its `Fst`) is not provable (notes/mvccfull-prove-writer.md)
      sorry
    · (try wp_auto); iframe; ipureintro; rfl
  iintro %w ⟨%hw, ch⟩
  subst hw
  (try wp_auto)
  iapply HΦ
  iframe Hlead
  isplitl [Hpost]
  · ileft; iexact Hpost
  iexists ⟨v.path, v.lp, v.kv, v.ops + 1, v.bk, v.ι, v.U, b2⟩
  isplitr
  · ipureintro; exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  iapply memCore_compact ks γh ops i mp m f v qw nw k o b2 hov hkind
  rw [hkv]
  have hoZ : W64 (sint.Z o.rev) = o.rev := by word
  have hσ1 : σOf ks ops (v.ops + 1) = (σOf ks ops v.ops).compactTo (sint.Z o.rev) := by
    rw [hS, if_pos hcok]
  have hcc : W64 (((σOf ks ops v.ops).compactTo (sint.Z o.rev)).crev) = o.rev := hoZ
  rw [hC, hσ1, hcc]
  iframe Hid Hhook Hpath Hbe Hle Hkvf Hrevf Hcmpf Hlsl Hopen Hmb Hrds Hbk HlW
  iframe #
  isplitr
  · iunfold hookOk; iframe #; ipureintro; exact Hfnil
  isplitl [Hret Hσw Hbw]
  · iunfold incW; iframe #; iframe
  ipureintro; exact HU

end proof

end mvccfull
end EtcdGrove
end Perennial
