/-
The writer's compaction (`runner.compact`): the model's step and the update at the member's
incarnation invariant. Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.WriterLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section model
variable [GooseExts]

/-- **A compaction's model step**: no revision, the leases and the grants unchanged; the
compaction revision and the compactions raised if it compacts (above the last, at most the
current revision). -/
theorem runM_compact (ks : List GoString) (ops : List OpM) (n : Nat) (o : OpM)
    (ho : ops[n]? = some o) (hk : o.kind = kCompact) :
    (runM ks ops (n + 1)).hs = (runM ks ops n).hs ∧
    (runM ks ops (n + 1)).leases = (runM ks ops n).leases ∧
    (runM ks ops (n + 1)).granted = (runM ks ops n).granted ∧
    (runM ks ops (n + 1)).crev =
      (if (runM ks ops n).crev < sint.Z o.rev ∧ sint.Z o.rev ≤ ((runM ks ops n).rev : Int)
        then sint.Z o.rev else (runM ks ops n).crev) ∧
    (runM ks ops (n + 1)).comps =
      (if (runM ks ops n).crev < sint.Z o.rev ∧ sint.Z o.rev ≤ ((runM ks ops n).rev : Int)
        then (runM ks ops n).comps ++ [o.rev] else (runM ks ops n).comps) := by
  rw [runM_succ ks ops n o ho]
  generalize runM ks ops n = s
  have hp : (opPend ks s o).chs = [] := by
    unfold opPend
    simp [hk]
  have hh : histAfter s.hs (opPend ks s o) = s.hs := by unfold histAfter; simp [hp]
  unfold opStep
  simp only [hh, hk]
  refine ⟨trivial, ?_, ?_, ?_, ?_⟩ <;> simp

theorem bndOk_compact (ks : List GoString) (σ : MvccState) (b : Bnd) (Hl : List HRev) (c : Int)
    (hok : bndOk ks σ b Hl) (hc : σ.crev < c) (hcb : c ≤ sint.Z b.2.2.2) :
    bndOk ks (σ.compactTo c) b Hl := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hok
  exact ⟨h1, h2, h3, h4, h5, by show sint.Z b.2.2.1 ≤ c; omega, hcb, by show -1 ≤ c; omega, h9, h10⟩

end model

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **`Compact`'s update at a live incarnation** (the writer's halves at `σf` and the bounds `b`,
`cmpHi` at least `c` if it compacts): the state compacted to `c` if `c` is above its compaction
revision and at most its revision, else unchanged; the writer's half with it. -/
theorem compact_au (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG)) (ks : List GoString)
    (γh : HistNames) (i : Nat) (mp : Loc) (m : MemberNames) (ι : IncNames) (kv : GoInterface)
    (qw : Qp) (σf : MvccState) (b : Bnd) (c : Int)
    (hb : σf.crev < c ∧ c ≤ (σf.rev : Int) → c ≤ sint.Z b.2.2.2) :
    isInc (GF := GF) ks γh i mp m ι kv ∗ ghostVar ι.ret qw () ∗ ghostVar m.σ (1 : Qp).half σf ∗
        ghostVar m.bnd (1 : Qp).half b ⊢
      AU <{ ∃∃ (σ : MvccState), mvccState ι.kv σ }> @ ⊤ \ ↑mvccN, ∅
        <{ mvccState ι.kv (if σ.crev < c ∧ c ≤ (σ.rev : Int) then σ.compactTo c else σ),
           COMM (fun (σ : MvccState) => iprop(⌜σ = σf⌝ ∗ ghostVar ι.ret qw () ∗
             ghostVar m.σ (1 : Qp).half
               (if σf.crev < c ∧ c ≤ (σf.rev : Int) then σf.compactTo c else σf) ∗
             ghostVar m.bnd (1 : Qp).half b)) σ }> := by
  haveI := memberInv_timeless hpers ks γh mp m ι
  have Hm := memberN_mask i
  unfold isInc
  iintro ⟨⟨#Hinv, -⟩, Hret, Hσw, Hbw⟩
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
  icases Hs with ⟨%σ, %b0, %Hl, Hs, Hσi, Hrl, Hrh, Hcl, Hch, Hbi, Hrev, Hcrev, Hnrev, #Hlb, %Hp⟩
  ihave %Hag := ghostVar_agree m.σ _ _ _ _ $$ Hσi Hσw
  ihave %Hagb := ghostVar_agree m.bnd _ _ _ _ $$ Hbi Hbw
  subst Hag Hagb
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑mvccN) \ ↑(memberN i) from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ
  iframe Hs
  isplit
  · iintro Hs
    imod Hclose2 with -
    imod Hclose $$ [Hs Hσi Hrl Hrh Hcl Hch Hbi Hrev Hcrev Hnrev] with -
    · inext; iunfold memberInv; ileft; iunfold memberState; iexists σ, b0, Hl; iframe; iframe #
      ipureintro; exact Hp
    imodintro
    iframe
  · iintro Hs
    imod Hclose2 with -
    by_cases hcok : σ.crev < c ∧ c ≤ (σ.rev : Int)
    · simp only [hcok, and_self, ↓reduceIte]
      have hok' := bndOk_compact ks σ b0 Hl c Hp hcok.1 (hb hcok)
      imod ghostVar_update_halves (σ.compactTo c) m.σ _ _ $$ Hσi Hσw with ⟨Hσi, Hσw⟩
      imod mono_nat_own_update (Int.toNat ((σ.compactTo c).crev + 1))
        (by show Int.toNat (σ.crev + 1) ≤ Int.toNat (c + 1); omega) $$ Hcrev with ⟨Hcrev, -⟩
      imod Hclose $$ [Hs Hσi Hrl Hrh Hcl Hch Hbi Hrev Hcrev Hnrev] with -
      · inext; iunfold memberInv; ileft; iunfold memberState; iexists σ.compactTo c, b0, Hl
        iframe; iframe #
        ipureintro; exact hok'
      imodintro
      iframe
    · simp only [hcok, ↓reduceIte]
      imod Hclose $$ [Hs Hσi Hrl Hrh Hcl Hch Hbi Hrev Hcrev Hnrev] with -
      · inext; iunfold memberInv; ileft; iunfold memberState; iexists σ, b0, Hl; iframe; iframe #
        ipureintro; exact Hp
      imodintro
      iframe

end lemmas

end mvccfull
end EtcdGrove
end Perennial
