/-
Lean-first (no Rocq counterpart). Stage U2 of `notes/raft-unified-plan.md` (2026-10-28): the
dynamic clause of a snapshot's configuration certificate (`raftSnapCert`, `Ghost.lean`) made from
a committed prefix.

The dynamic clause says that every full-log prefix with records (`logRecs γ base0 fp`) ending at the
snapshot's id (`FullOk k.sid fp`) folds to the snapshot's configuration (`D.fold fp = some
k.cfgM`). A committed prefix `L` of that length and last term is the only such prefix
(`committedRecs_full`): a committed log is the bootstrap log's prefix or a commit fact's log, which
has records (`isCommitted_recs`), and two full logs with records ending at one id are equal
(`FullOk_unique`). So a fold of `L` certifies the snapshot (`raftSnapCert_make_dyn`).
-/
module

public import Proof.go_etcd_io.raft.v3.Protocol.GhostState

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI GMap go_etcd_io.raft.v3

section ghost
variable [GooseExts]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]

/-- What a committed log is made of, persistently: a prefix of the bootstrap log, or a full log
with records. -/
def committedRecs (γ : RaftNames) (L : List EntryM) : IProp GF :=
  iprop(⌜L <+: γ.reBoot⌝ ∨ (⌜PlogWf base0 L⌝ ∗ logRecs γ base0 L))

instance committedRecs_persistent (γ : RaftNames) (L : List EntryM) :
    Persistent (committedRecs (GF := GF) γ L) := by
  unfold committedRecs; infer_instance

/-- A committed log is the bootstrap log's prefix or has records (the commit invariant's
justification of the global log: the bootstrap log, or a commit fact's log). -/
theorem isCommitted_recs (γ : RaftNames) (E : CoPset) (L : List EntryM) :
    ↑(raftLogN γ) ⊆ E →
    ⊢ raftCommitInv (GF := GF) γ -∗ isCommitted γ L ={E}=∗ committedRecs γ L := by
  intro HE
  iintro #Hinv #HL
  ihave #Hli := raftCommitInv_log γ $$ Hinv
  unfold raftLogInv raftLogInvBody logRest
  iinv Hli with ⟨%P, >HP, >#Hjs, >Htbl, >Hwt, >#Hds, >Hq1⟩ Hclose
  icases isCommitted_prefix γ L P $$ HL HP with %Hpre
  imod Hclose $$ [HP Htbl Hwt Hq1] with -
  · inext
    iexists P
    iframe HP Hjs Htbl Hwt Hds Hq1
  unfold committedRecs
  iunfold committedJust at Hjs
  icases Hjs with (%Hb | ⟨%t, %n, %G, %ldr, #Hq, %HPG, -, -⟩)
  · imodintro; ileft; ipureintro; rw [← Hb.1]; exact Hpre
  · icases cq_full γ t n G $$ Hq with ⟨%HwG, #HrG⟩
    have HLG : L <+: G := by
      rw [HPG] at Hpre; exact Hpre.trans (List.take_prefix _ G)
    obtain ⟨n0, Hn0⟩ : ∃ n0, n0 = L.length := ⟨_, rfl⟩
    have HLt : L = G.take n0 := by rw [Hn0]; exact List.prefix_iff_eq_take.mp HLG
    ihave #HrL := logRecs_take γ G n0 $$ HrG
    imodintro
    iright
    rw [HLt]
    iframe HrL
    ipureintro; exact PlogWf_take _ _ _ HwG

/-- A committed log of length `i` with last term `t` is the only full log with records ending at
`(t, i)`. -/
theorem committedRecs_full (γ : RaftNames) (L fp : List EntryM) (b : entryID) :
    FullOk b fp → (L.length : Int) = uint.Z b.index' →
    L.getLast?.map EntryM.Term' = some b.term' →
    ⊢ committedRecs (GF := GF) γ L -∗ logRecs γ base0 fp -∗ ⌜fp = L⌝ := by
  intro Hf HlL Hlast
  obtain ⟨Hlf, Hwf, -⟩ := id Hf
  have Hlen : fp.length = L.length := by omega
  unfold committedRecs
  iintro (%Hb | ⟨%HwL, #HrL⟩) #Hr
  · icases logRecs_boot_take γ fp Hwf $$ Hr with %Ht
    ipureintro
    have HbL := Hb.length_le
    have H1 := Ht fp.length (by omega) (Nat.le_refl _)
    rw [List.take_length] at H1
    rw [H1, Hlen, ← List.prefix_iff_eq_take.mp Hb]
  · -- `L` is a full log ending at `b`
    have HL0 : L ≠ [] := by intro h; subst h; simp at Hlast
    obtain ⟨e, He⟩ : ∃ e, L.getLast? = some e := Option.isSome_iff_exists.mp
      (by cases h : L.getLast? with
          | none => exact absurd (List.getLast?_eq_none_iff.mp h) HL0
          | some _ => rfl)
    rw [He] at Hlast
    simp only [Option.map_some, Option.some.injEq] at Hlast
    have Hk : L[L.length - 1]? = some e := by rw [← List.getLast?_eq_getElem?]; exact He
    have Hpos : 0 < L.length := List.length_pos_iff.mpr HL0
    have Ht : plogTermAt base0 L b.index' = some b.term' := by
      rw [plogTermAt_lookup base0 L b.index' (L.length - 1) e Hk
        (by rw [base0_index]; push_cast [Nat.sub_add_cancel Hpos]; omega), Hlast]
    have HfL := FullOk_take L b.term' b.index' HwL Ht
    have Htk : L.take (uint.Z b.index').toNat = L := List.take_of_length_le (by omega)
    rw [Htk] at HfL
    have Hb : (entryID.mk b.term' b.index') = b := by cases b; rfl
    rw [Hb] at HfL
    iapply FullOk_unique γ b fp L Hf HfL $$ Hr HrL

/-- **A dynamic snapshot certificate from a committed prefix** (stage U2): the snapshot `k` at the
id of the committed prefix `L` (its length and last term), whose lists are well formed
(`SnapListsOk`) and denote the mode's fold of `L` over decisions recorded (`decLb`), is certified. -/
theorem raftSnapCert_make_dyn (γ : RaftNames) (E : CoPset) (L : List EntryM) (k : SnapTrip)
    (D : DynCfg) (M : DecMap) :
    ↑(raftLogN γ) ⊆ E → γ.dyn = some D →
    L.length = uint.nat k.sid.index' → L.getLast?.map EntryM.Term' = some k.sid.term' →
    SnapListsOk k → D.fold M L = some k.cfgM →
    ⊢ raftCommitInv (GF := GF) γ -∗ isCommitted γ L -∗ decLb γ M ={E}=∗ raftSnapCert γ k := by
  intro HE HD HlenN Hlast Hok Hfold
  have Hlen : (L.length : Int) = uint.Z k.sid.index' := by rw [HlenN]
  iintro #Hinv #HL #HM
  imod isCommitted_recs γ E L HE $$ Hinv HL with #HR
  imodintro
  unfold raftSnapCert
  isplitr; · ipureintro; intro _ _; exact Hok
  isplitr
  · ipureintro; intro hn; rw [RaftNames.dyn_none hn] at HD; cases HD
  isplitr
  · imodintro
    iintro %x %_ %D' %HD' %fp #Hfp %Hfull
    icases committedRecs_full γ L fp k.sid Hfull Hlen Hlast $$ HR Hfp with %Heq
    subst Heq
    rw [HD] at HD'
    cases HD'
    iexists M
    iframe HM
    ipureintro; exact Hfold
  unfold snapAtOk
  iright
  iexists L, M
  iframe HL HM
  ipureintro
  refine ⟨HlenN, Hlast, Hok, fun D' HD' => ?_⟩
  rw [HD] at HD'; cases HD'; exact Hfold

end ghost

end EtcdGrove
end Perennial
