/-
mvccfull's restore (Probe): the follower's incarnation across `KV.Restore` and the bound stores
around it. Lean-first (no Rocq counterpart).

The follower's store is restored in place (its incarnation stays: its readers and streams run
throughout), so `Restore`'s update is the incarnation invariant's: the writer's halves of `m.σ` and
`m.bnd` pin the state (`σf`, nothing pending) and the bounds; the new state `σb` (the builder's, at
the leader's count) extends it; the bounds were raised first (`revHi`, `cmpHi` at the builder's), so
they hold at `σb`; the monotone counters grow (the log a prefix, the compaction revision not lower);
the history's lower bound is the writer's (covering `σb`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.WriterShares
public import Proof.go_etcd_io.etcd.server.v3.lease.GuardLaws

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- The bounds' facts of `memberState` at the state `σ`, the bounds `b` and the history's lower
bound `Hl`. -/
def bndOk (ks : List GoString) (σ : MvccState) (b : Bnd) (Hl : List HRev) : Prop :=
  1 ≤ sint.Z b.1 ∧ sint.Z b.1 ≤ σ.rev ∧ (σ.rev : Int) ≤ sint.Z b.2.1 ∧ sint.Z b.2.1 < 2 ^ 62 ∧
    (σ.notifiedLog.length : Int) ≤ sint.Z b.2.1 + 1 ∧
    sint.Z b.2.2.1 ≤ σ.crev ∧ σ.crev ≤ sint.Z b.2.2.2 ∧ -1 ≤ σ.crev ∧
    histOkM ks σ Hl ∧ onceUpToAll σ.notifiedLog

theorem memberInv_timeless (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (ks : List GoString) (γh : HistNames) (mp : Loc) (m : MemberNames) (ι : IncNames) :
    Timeless (memberInv (GF := GF) ks γh mp m ι) := by
  haveI := hpers.2.2.2.2.2.1
  haveI : Timeless (memberState (GF := GF) ks γh mp m ι.kv) := by
    unfold memberState
    refine @exists_timeless _ _ _ _ (fun σ => ?_)
    refine @exists_timeless _ _ _ _ (fun b => ?_)
    refine @exists_timeless _ _ _ _ (fun Hl => ?_)
    infer_instance
  unfold memberInv; infer_instance

/-- **`Restore`'s update at the follower's incarnation** (see the file header): the writer's live
share and halves, at `σf` and the bounds `b`, which hold at `σb`; the state becomes `σb`, the
writer's half of `m.σ` with it. -/
theorem restore_au (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG)) (ks : List GoString)
    (γh : HistNames) (i : Nat) (mp : Loc) (m : MemberNames) (ι : IncNames) (kv : GoInterface)
    (qw : Qp) (σf σb : MvccState) (b : Bnd) (Hl : List HRev)
    (hf : σf.pending = none) (hbp : σb.pending = none) (hok : bndOk ks σb b Hl)
    (hpre : σf.log <+: σb.log ∧ σf.crev ≤ σb.crev) :
    isInc (GF := GF) ks γh i mp m ι kv ∗ ghostVar ι.ret qw () ∗ ghostVar m.σ (1 : Qp).half σf ∗
        ghostVar m.bnd (1 : Qp).half b ∗ monoListLbOwn γh.l Hl ⊢
      AU <{ ∃∃ (σ : MvccState), mvccState ι.kv σ ∗ ⌜σ.log <+: σb.log ∧ σ.crev ≤ σb.crev⌝ }>
          @ ⊤ \ ↑mvccN, ∅
        <{ mvccState ι.kv σb ∗ ⧖ (logCh σb.log),
           COMM (fun (_ : MvccState) => iprop(ghostVar ι.ret qw () ∗
             ghostVar m.σ (1 : Qp).half σb ∗ ghostVar m.bnd (1 : Qp).half b)) σ }> := by
  haveI := memberInv_timeless hpers ks γh mp m ι
  have Hm := memberN_mask i
  unfold isInc
  iintro ⟨⟨#Hinv, -⟩, Hret, Hσw, Hbw, #Hlb⟩
  iauintro
  unfold atomic_acc
  iinv Hinv with >Hi Hclose
  iunfold memberInv at Hi
  icases Hi with (Hs | Hr)
  rotate_left
  · icombine Hret Hr gives %Hq0
    obtain ⟨Hq, -⟩ := Hq0
    exfalso
    have h := Qp.le_iff.mp Hq
    simp only [Qp.val_add, Qp.val_one] at h
    have := qw.2
    grind
  iunfold memberState at Hs
  icases Hs with ⟨%σ, %b', %Hl', Hs, Hσi, Hrl, Hrh, Hcl, Hch, Hbi, Hrev, Hcrev, Hnrev, Hlb', %Hp⟩
  ihave %Hag := ghostVar_agree m.σ _ _ _ _ $$ Hσi Hσw
  ihave %Hagb := ghostVar_agree m.bnd _ _ _ _ $$ Hbi Hbw
  subst Hag Hagb
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑mvccN) \ ↑(memberN i) from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ
  iframe Hs
  isplitr
  · ipureintro; exact hpre
  isplit
  · iintro ⟨Hs, -⟩
    imod Hclose2 with -
    imod Hclose $$ [Hs Hσi Hrl Hrh Hcl Hch Hbi Hrev Hcrev Hnrev Hlb'] with -
    · inext; iunfold memberInv; ileft; iunfold memberState; iexists σ, b', Hl'; iframe
      ipureintro; exact Hp
    imodintro
    iframe
  · iintro ⟨Hs, -⟩
    have hlen := hpre.1.length_le
    have hn1 : σ.notifiedLog = σ.log := by unfold MvccState.notifiedLog; rw [hf]
    have hn2 : σb.notifiedLog = σb.log := by unfold MvccState.notifiedLog; rw [hbp]
    imod ghostVar_update_halves σb m.σ _ _ $$ Hσi Hσw with ⟨Hσi, Hσw⟩
    imod mono_nat_own_update σb.rev (by unfold MvccState.rev; omega) $$ Hrev with ⟨Hrev, -⟩
    imod mono_nat_own_update (Int.toNat (σb.crev + 1)) (by have := hpre.2; omega) $$ Hcrev
      with ⟨Hcrev, -⟩
    imod mono_nat_own_update σb.notifiedLog.length (by rw [hn1, hn2]; exact hlen) $$ Hnrev
      with ⟨Hnrev, -⟩
    imod Hclose2 with -
    imod Hclose $$ [Hs Hσi Hrl Hrh Hcl Hch Hbi Hrev Hcrev Hnrev] with -
    · inext; iunfold memberInv; ileft; iunfold memberState; iexists σb, b', Hl; iframe
      iframe #
      ipureintro; exact hok
    imodintro
    iframe

/-- **The bounds' atomics, opened by the writer** (its live share and halves, at the state `σf` and
the bounds `b`): the four atomics, given back at any bounds `b'` that hold at `σf` (the invariant's
history lower bound `Hl` unchanged), the writer's half of `m.bnd` at `b'`. -/
theorem bnd_acc (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG)) (ks : List GoString)
    (γh : HistNames) (i : Nat) (mp : Loc) (m : MemberNames) (ι : IncNames) (kv : GoInterface)
    (qw : Qp) (σf : MvccState) (b : Bnd) :
    isInc (GF := GF) ks γh i mp m ι kv ∗ ghostVar ι.ret qw () ∗ ghostVar m.σ (1 : Qp).half σf ∗
        ghostVar m.bnd (1 : Qp).half b ⊢
      |={⊤, ⊤ \ ↑(memberN i)}=> ∃ Hl : List HRev, ⌜bndOk ks σf b Hl⌝ ∗
        sync.atomic.ownInt64 (mF go!"revLo" mp) (DFrac.own 1) b.1 ∗
        sync.atomic.ownInt64 (mF go!"revHi" mp) (DFrac.own 1) b.2.1 ∗
        sync.atomic.ownInt64 (mF go!"cmpLo" mp) (DFrac.own 1) b.2.2.1 ∗
        sync.atomic.ownInt64 (mF go!"cmpHi" mp) (DFrac.own 1) b.2.2.2 ∗
        (∀ b' : Bnd, ⌜bndOk ks σf b' Hl⌝ -∗
          sync.atomic.ownInt64 (mF go!"revLo" mp) (DFrac.own 1) b'.1 -∗
          sync.atomic.ownInt64 (mF go!"revHi" mp) (DFrac.own 1) b'.2.1 -∗
          sync.atomic.ownInt64 (mF go!"cmpLo" mp) (DFrac.own 1) b'.2.2.1 -∗
          sync.atomic.ownInt64 (mF go!"cmpHi" mp) (DFrac.own 1) b'.2.2.2 ={⊤ \ ↑(memberN i), ⊤}=∗
          ghostVar ι.ret qw () ∗ ghostVar m.σ (1 : Qp).half σf ∗ ghostVar m.bnd (1 : Qp).half b') := by
  haveI := memberInv_timeless hpers ks γh mp m ι
  unfold isInc
  iintro ⟨⟨#Hinv, -⟩, Hret, Hσw, Hbw⟩
  iinv Hinv with >Hi Hclose
  iunfold memberInv at Hi
  icases Hi with (Hs | Hr)
  rotate_left
  · icombine Hret Hr gives %Hq0
    obtain ⟨Hq, -⟩ := Hq0
    exfalso
    have h := Qp.le_iff.mp Hq
    simp only [Qp.val_add, Qp.val_one] at h
    have := qw.2
    grind
  iunfold memberState at Hs
  icases Hs with ⟨%σ, %b0, %Hl, Hs, Hσi, Hrl, Hrh, Hcl, Hch, Hbi, Hrev, Hcrev, Hnrev, #Hlb, %Hp⟩
  ihave %Hag := ghostVar_agree m.σ _ _ _ _ $$ Hσi Hσw
  ihave %Hagb := ghostVar_agree m.bnd _ _ _ _ $$ Hbi Hbw
  subst Hag Hagb
  imodintro
  iexists Hl
  isplitr
  · ipureintro; exact Hp
  iframe Hrl Hrh Hcl Hch
  iintro %b' %Hok' Hrl Hrh Hcl Hch
  imod ghostVar_update_halves b' m.bnd _ _ $$ Hbi Hbw with ⟨Hbi, Hbw⟩
  imod Hclose $$ [Hs Hσi Hrl Hrh Hcl Hch Hbi Hrev Hcrev Hnrev] with -
  · inext; iunfold memberInv; ileft; iunfold memberState; iexists σ, b', Hl; iframe
    iframe #; ipureintro; exact Hok'
  imodintro
  iframe

/-- **A read's update at a live incarnation** (`KV.Rev`, `KV.Read`): the state unchanged, the
writer's half pinning it. -/
theorem read_au (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG)) (ks : List GoString)
    (γh : HistNames) (i : Nat) (mp : Loc) (m : MemberNames) (ι : IncNames) (kv : GoInterface)
    (qw : Qp) (σf : MvccState) :
    isInc (GF := GF) ks γh i mp m ι kv ∗ ghostVar ι.ret qw () ∗ ghostVar m.σ (1 : Qp).half σf ⊢
      AU <{ ∃∃ (σ : MvccState), mvccState ι.kv σ }> @ ⊤ \ ↑mvccN, ∅
        <{ mvccState ι.kv σ,
           COMM (fun (σ : MvccState) => iprop(⌜σ = σf⌝ ∗ ghostVar ι.ret qw () ∗
             ghostVar m.σ (1 : Qp).half σf)) σ }> := by
  haveI := memberInv_timeless hpers ks γh mp m ι
  have Hm := memberN_mask i
  unfold isInc
  iintro ⟨⟨#Hinv, -⟩, Hret, Hσw⟩
  iauintro
  unfold atomic_acc
  iinv Hinv with >Hi Hclose
  iunfold memberInv at Hi
  icases Hi with (Hs | Hr)
  rotate_left
  · icombine Hret Hr gives %Hq0
    obtain ⟨Hq, -⟩ := Hq0
    exfalso
    have h := Qp.le_iff.mp Hq
    simp only [Qp.val_add, Qp.val_one] at h
    have := qw.2
    grind
  iunfold memberState at Hs
  icases Hs with ⟨%σ, %b0, %Hl, Hs, Hσi, Hrest⟩
  ihave %Hag := ghostVar_agree m.σ _ _ _ _ $$ Hσi Hσw
  subst Hag
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑mvccN) \ ↑(memberN i) from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ
  iframe Hs
  isplit
  · iintro Hs
    imod Hclose2 with -
    imod Hclose $$ [Hs Hσi Hrest] with -
    · inext; iunfold memberInv; ileft; iunfold memberState; iexists σ, b0, Hl; iframe
    imodintro
    iframe
  · iintro Hs
    imod Hclose2 with -
    imod Hclose $$ [Hs Hσi Hrest] with -
    · inext; iunfold memberInv; ileft; iunfold memberState; iexists σ, b0, Hl; iframe
    imodintro
    iframe
    ipureintro; rfl

/-- A persistent fact of every element of `U` holds of every key in `U` among `recs`. -/
theorem bigSepL_mem_or {A B : Type} [DecidableEq A] (U : List A) (key : B → A) (Φ : A → IProp GF)
    [∀ a, Persistent (Φ a)] : ∀ recs : List B,
    □ ([∗list] a ∈ U, Φ a) ⊢ □ ([∗list] x ∈ recs, iprop(⌜key x ∉ U⌝ ∨ Φ (key x)))
  | [] => by iintro -; imodintro; iapply BigSepL.bigSepL_nil.2; itrivial
  | x :: recs => by
    iintro #HU
    imodintro
    iapply BigSepL.bigSepL_cons.2
    isplitl
    · by_cases hx : key x ∈ U
      · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hx
        iright
        iapply (BigSepL.bigSepL_lookup (Φ := fun _ a => Φ a) hi)
        iexact HU
      · ileft; ipureintro; exact hx
    · ihave #H := bigSepL_mem_or U key Φ recs $$ HU
      iexact H

/-- **Every id is granted under the guard `True`** (`lease.leaseGranted_of_guard`). -/
theorem granted_list (γl : GName) : ∀ l : List w64,
    lease.lessorGuard (GF := GF) γl (fun _ => iprop(True)) ⊢
      □ ([∗list] id ∈ l, lease.leaseGranted γl id)
  | [] => by iintro -; imodintro; iapply BigSepL.bigSepL_nil.2; itrivial
  | x :: l => by
    iintro #Hg
    imodintro
    iapply BigSepL.bigSepL_cons.2
    isplitl
    · iapply lease.leaseGranted_of_guard γl (fun _ => iprop(True)) x
      iframe #
      imodintro; itrivial
    · ihave #H := granted_list γl l $$ Hg
      iexact H

end lemmas

end mvccfull
end EtcdGrove
end Perennial
