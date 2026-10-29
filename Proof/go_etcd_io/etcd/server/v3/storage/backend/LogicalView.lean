/-
**The batch lock over the logical view** (the backend-compaction stage, question 2, option (a), the
user's, 2026-10-29; `notes/backend-cmp-plan.md`, "Question 2's Draft round"). Lean-first.

Draft: the statements of question 2, stated as they will be, beside the ones they replace, so that
they are reviewed before any proof is switched. Nothing imports this module yet, and nothing in it
is a `sorry`.

* `relog P L st`: the logical view after a put session's `Unlock`: the session's writer's contents
  (`sData P st.S`) over the logical view `L`, falling back to `L` only at keys of safe-range buckets
  that the readers' physical view already lacked (keys compaction deleted before this session: they
  stay in mvcc's logical bucket; review round 5, R5-1). A key the session itself deleted is gone
  from the logical view too.
* `batchViewQ γ P st`: the batch lock's quarter of the readers' view, over the logical view `L`, the
  physical `vData P (st.C, st.R)` thin of it: what replaces `batchGhostAt`'s exact quarter (review
  round 4, R4-2). Today's exact quarter is its instance (`batchViewQ_of_exact`).
* `viewAtL γ vd`: D22's `viewAt` over the logical view (option (a)): `∃ L, viewQ γ ¼ vd L`. Today's
  `viewAt` is its instance (`viewAtL_of_viewAt`), and with nothing deletable it is today's
  (`viewAtL_noDel`, D22's users' backends never compact).
* `backend.batchTxBuffered.Unlock.specF`: the folded `Unlock` spec (one spec per function): the
  deleting session's branch (today's `specC`, whose `viewSame` instance is `spec`'s first branch,
  `viewSame_thin`) and the put session's branch, whose clients' view comes back at `relog P vd st`
  instead of `sData P st.S`. With nothing deletable the clients' view is the physical one
  (`batchLocked_thin` with `thinV_exact`) and `relog` gives `sData P st.S` back (`relog_exact`):
  today's `spec`, a corollary under `dlNoDel`, not a second spec.

`UnsafeDelete.specC` is already the folded `UnsafeDelete` spec (a safe-range delete takes `dlIs`);
the fold makes it `spec`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBatch
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.DelKeys
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvSnapshot
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__Unlock

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend

/-! ## The logical view after a put session -/

/-- **The logical view after a put session's `Unlock`** (see the file header): the writer's
contents over `L`, with `L`'s entries kept only at safe-range keys the readers' physical view
already lacked. -/
def relog (P : BParams) (L : VData) (st : BSess) : VData :=
  sData P st.S ∪
    GMap.filter (fun nk _ => P.SB nk.1 && decide ((vData P (st.C, st.R)).lookup nk = none)) L

theorem relog_lookup (P : BParams) (L : VData) (st : BSess) (nk : GoString × GoString) :
    (relog P L st).lookup nk =
      ((sData P st.S).lookup nk).or
        (if P.SB nk.1 = true ∧ (vData P (st.C, st.R)).lookup nk = none then L.lookup nk else none) := by
  unfold relog
  show ((sData P st.S).lookup nk).or ((L.lookup nk).filter _) = _
  congr 1
  cases hL : L.lookup nk <;>
    by_cases h : P.SB nk.1 = true ∧ (vData P (st.C, st.R)).lookup nk = none <;>
    simp_all [Option.filter]

/-- **With an exact logical view, `relog` is the writer's contents** (nothing kept from `L` but
what the physical view has). -/
theorem relog_exact (P : BParams) (st : BSess) :
    relog P (vData P (st.C, st.R)) st = sData P st.S := by
  apply GMap.ext
  intro nk
  rw [relog_lookup]
  by_cases h : P.SB nk.1 = true ∧ (vData P (st.C, st.R)).lookup nk = none
  · simp only [h, and_self, ↓reduceIte]; cases (sData P st.S).lookup nk <;> rfl
  · simp only [h, ↓reduceIte]; cases (sData P st.S).lookup nk <;> rfl

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **Thinness composes**: a view thin of one thin of `L` is thin of `L` (the deleting session's
commit: the new physical view thin of the old, the old thin of the logical). -/
theorem thinV_trans (γ : BNames) (a b c : VData) :
    thinV (GF := GF) γ a b ∗ thinV γ b c ⊢ thinV γ a c := by
  iunfold thinV
  iintro ⟨⟨%H1, #D1⟩, ⟨%H2, #D2⟩⟩
  isplitr
  · ipureintro; intro nk v h; exact H2 nk v (H1 nk v h)
  · iintro !> %nk %h
    cases hb : b.lookup nk with
    | none => iapply D2; ipureintro; exact ⟨h.1, hb⟩
    | some v => iapply D1; ipureintro; exact ⟨by simp [hb], h.2⟩

/-- **A put session keeps the physical view thin of the logical one** (the put branch of
`Unlock.specF`): the new physical view `sData P st.S` is thin of `relog P L st` whenever the old
physical view was thin of `L`. -/
theorem thinV_relog (γ : BNames) (P : BParams) (L : VData) (st : BSess) :
    thinV (GF := GF) γ (vData P (st.C, st.R)) L ⊢ thinV γ (sData P st.S) (relog P L st) := by
  iunfold thinV
  iintro ⟨-, #D⟩
  isplitr
  · ipureintro; intro nk v h; rw [relog_lookup, h]; rfl
  · iintro !> %nk %h
    obtain ⟨h1, h2⟩ := h
    rw [relog_lookup, h2] at h1
    by_cases hc : P.SB nk.1 = true ∧ (vData P (st.C, st.R)).lookup nk = none
    · simp only [hc, and_self, ↓reduceIte] at h1
      iapply D
      ipureintro
      exact ⟨by simpa using h1, hc.2⟩
    · simp only [hc, ↓reduceIte] at h1; exact absurd rfl h1

/-! ## The batch lock's quarter over the logical view -/

/-- **The batch lock's quarter of the readers' view, over the logical view** (Draft of
`batchGhostAt`'s first conjunct, R4-2): some logical view `L`, the physical `vData P (st.C, st.R)`
thin of it. -/
def batchViewQ (γ : BNames) (P : BParams) (st : BSess) : IProp GF :=
  iprop(∃ L : VData, viewQ γ (1 : Qp).half.half (vData P (st.C, st.R)) L)

/-- Today's exact quarter is an instance. -/
theorem batchViewQ_of_exact (γ : BNames) (P : BParams) (st : BSess) :
    ghostVar (GF := GF) γ.view (1 : Qp).half.half (vData P (st.C, st.R)) ⊢ batchViewQ γ P st := by
  unfold batchViewQ
  iintro H
  iexists vData P (st.C, st.R)
  iapply viewQ_exact $$ H

/-- **The clients' view is the logical one** (agreement of the shares of `γ.view`): the batch
lock's physical view is thin of what a client holds. -/
theorem batchViewQ_bView (γ : BNames) (P : BParams) (st : BSess) (q : Qp) (vd : VData) :
    batchViewQ (GF := GF) γ P st ∗ bView γ q vd ⊢
      batchViewQ γ P st ∗ bView γ q vd ∗ thinV γ (vData P (st.C, st.R)) vd := by
  unfold batchViewQ bView bViewC viewQ
  iintro ⟨⟨%L, Hq, #Ht⟩, ⟨%c, Hv, Hc, Hl⟩⟩
  icombine Hq Hv gives %Heq
  obtain ⟨-, rfl⟩ := Heq
  iframe Hc Hl Hq Hv
  iframe #

/-- **What the bridge reads of the batch lock: the clients' view is thin-over the physical one**
(today: equal; after the switch, from `batchViewQ_bView`). With `dlNoDel` (`thinV_exact`) the
clients' view is the physical view, so `relog` gives `sData P st.S` back (`relog_exact`). -/
theorem batchLocked_thin (γ : BNames) (P : BParams) (b : Loc) (st : BSess) (q : Qp) (vd : VData) :
    batchLocked (GF := GF) γ P b st ∗ bView γ q vd ⊢
      batchLocked γ P b st ∗ bView γ q vd ∗ thinV γ (vData P (st.C, st.R)) vd := by
  unfold batchLocked batchLockedAt batchGhost batchGhostAt bView bViewC
  iintro ⟨⟨%t, %db, #Ht, Hown, Hph, ⟨Hv, %n0, %w, %u, Hr, Ha, Hm, Hu, Ho, Hk, Hfk, %Hok⟩, %Hwf⟩,
    ⟨%c, Hc, Hcv, Hcl⟩⟩
  icombine Hv Hc gives %Heq
  obtain ⟨-, rfl⟩ := Heq
  isplitl [Hown Hph Hv Hr Ha Hm Hu Ho Hk Hfk]
  · iexists t, db
    iframe
    iframe #
    ipureintro; exact ⟨Hok, Hwf⟩
  isplitl [Hc Hcv Hcl]
  · iexists c; iframe
  iapply thinV_refl

/-! ## D22's `viewAt` over the logical view (option (a)) -/

/-- **`viewAt` over the logical view** (Draft of `InvSnapshot.lean`'s `viewAt`, option (a)): the
batch lock's quarter, at some logical view `L` the snapshot's physical view `vd` is thin of. -/
def viewAtL (γ : BNames) (vd : VData) : IProp GF :=
  iprop(∃ L : VData, viewQ γ (1 : Qp).half.half vd L)

/-- Today's `viewAt` is an instance (so `backend.Snapshot`'s axiom, its observation weaker, claims
no more). -/
theorem viewAtL_of_viewAt (γ : BNames) (vd : VData) : viewAt (GF := GF) γ vd ⊢ viewAtL γ vd := by
  unfold viewAt viewAtL
  iintro H
  iexists vd
  iapply viewQ_exact $$ H

/-- **With nothing deletable it is today's `viewAt`** (D22's users: their backends never compact). -/
theorem viewAtL_noDel (γ : BNames) (vd : VData) : dlNoDel (GF := GF) γ ∗ viewAtL γ vd ⊢ viewAt γ vd := by
  unfold viewAtL viewQ viewAt
  iintro ⟨#Hf, %L, Hv, #Ht⟩
  ihave %Heq := thinV_exact γ vd L $$ [$Hf $Ht]
  subst Heq
  iexact Hv

/-- **A no-change session is a deleting session with nothing deleted** (`spec`'s first branch,
`viewSame`, is `specF`'s first). -/
theorem viewSame_thin (γ : BNames) (P : BParams) (st : BSess) (h : viewSame P st) :
    ⊢ thinV (GF := GF) γ (sData P st.S) (vData P (st.C, st.R)) ∗
      ⌜∀ n i, P.BT.lookup n = some i → P.HB n = false → bkOf st.W.bks i = []⌝ := by
  rw [← h.1]
  isplitl
  · iapply thinV_refl
  · ipureintro; exact h.2

end laws

end backend

/-! ## The folded `Unlock` spec -/

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend backend

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **`t.Unlock()`, folded** (question 2's Draft; replaces `spec` and `specC` at the switch):
the session's writes written back into the read buffer, and committed if a delete is pending or the
batch limit reached (the pre-commit hook then runs, with `Pk`). Two kinds of session:
* **a deleting session** (the compaction job's; `spec`'s no-change sessions are its instance,
  `viewSame_thin`): it holds no clients' share of the view; the new physical view (the writer's
  contents) is thin of the old (`thinV`: what it deleted is registered as deletable), and its write
  buffer holds no puts to the non-hook buckets (review round 1, F8); it gives `W ∗ Pk`, and the
  logical view stays;
* **a put session**: it gives the clients' whole view `vd` (the logical view) and `Pk`, and gets the
  view back at `relog P vd st` (its writes over the logical view, compacted keys kept), from which it
  makes `W`.
A write-back's budget either way. Not in the hook's window, with room for the commit's hook. -/
abbrev backend.batchTxBuffered.Unlock.specF : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (t : Loc) (st : BSess) (Q : IProp GF),
  st.cnt.hw = false → sint.Z st.pend + P.hookMax < 2 ^ 58 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ P W Pk b ∗
      bF go!"batchTx" b ↦□ t ∗ batchLocked γ P b st ∗ wbTok γ ∗
      ((thinV γ (sData P st.S) (vData P (st.C, st.R)) ∗
         ⌜∀ n i, P.BT.lookup n = some i → P.HB n = false → bkOf st.W.bks i = []⌝ ∗ W ∗ Pk ∗ Q) ∨
       (∃ vd : VData, bView γ 1 vd ∗ Pk ∗ (bView γ 1 (relog P vd st) -∗ W ∗ Q))) }}
    (App (Val (t @!! go.GoType.PointerType batchTxBuffered.ty @!! go!"Unlock")) (Val #()))
  {{ RET #(); Q }}

/-- **Today's `spec` is a corollary of `specF` under `dlNoDel`** (one spec per function: the
variant only as a corollary): with nothing deletable the clients' view is the physical one
(`batchLocked_thin`, `thinV_exact`), so `relog` gives the writer's contents back (`relog_exact`), and a
no-change session is a deleting session that deleted nothing (`viewSame_thin`). -/
theorem backend.batchTxBuffered.Unlock.spec_of_specF
    (h : backend.batchTxBuffered.Unlock.specF (GF := GF) (hG := hG)) :
    ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (t : Loc) (st : BSess) (Q : IProp GF),
    st.cnt.hw = false → sint.Z st.pend + P.hookMax < 2 ^ 58 →
    {{ dlNoDel γ ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
        isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ∗ batchLocked γ P b st ∗ wbTok γ ∗
        ((⌜viewSame P st⌝ ∗ W ∗ Pk ∗ Q) ∨
         (∃ vd : VData, bView γ 1 vd ∗ Pk ∗ (bView γ 1 (sData P st.S) -∗ W ∗ Q))) }}
      (App (Val (t @!! go.GoType.PointerType batchTxBuffered.ty @!! go!"Unlock")) (Val #()))
    {{ RET #(); Q }} := by
  intro γ P W Pk b t st Q hw hroom
  iintro %Φ ⟨#Hf, #Hpkg, #Hb, #Ht, Hl, Hwb, Hbr⟩ HΦ
  icases Hbr with (⟨%Hsame, HW, HPk, HQ⟩ | ⟨%vd, Hv, HPk, Hwand⟩)
  · ihave ⟨#Hth, %Hnw⟩ := viewSame_thin (GF := GF) γ P st Hsame
    iapply (h γ P W Pk b t st Q hw hroom) $$ %Φ [Hl Hwb HW HPk HQ] HΦ
    iframe Hl Hwb
    iframe #
    ileft
    iframe HW HPk HQ
    iframe #
    ipureintro; exact Hnw
  · ihave ⟨Hl, Hv, #Hth⟩ := batchLocked_thin γ P b st 1 vd $$ [$Hl $Hv]
    ihave %Heq := thinV_exact γ (vData P (st.C, st.R)) vd $$ [$Hf $Hth]
    subst Heq
    iapply (h γ P W Pk b t st Q hw hroom) $$ %Φ [Hl Hwb Hv HPk Hwand] HΦ
    iframe Hl Hwb
    iframe #
    iright
    iexists vData P (st.C, st.R)
    iframe Hv HPk
    rw [relog_exact]
    iexact Hwand

end spec

end EtcdGrove
end Perennial
