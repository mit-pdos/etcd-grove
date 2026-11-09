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

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

/- `Members.lean`'s ghost variables' instances (`Writer.lean`'s note). -/
attribute [local instance high] mvccfull.mvccState_countable mvccfull.change_api_countable

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

end lemmas

end mvccfull
end EtcdGrove
end Perennial
