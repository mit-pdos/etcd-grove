/-
**A snapshotter's registration** (backend-snapshot B4, 2026-11-21; `notes/backend-snapshot-plan.md`):
`backend.Snapshot` registers its `R` and observation `Q` in the commit invariant before its own
`Commit()` (`reg_register`: a fresh key of the registry map, made at the current commit count `n`), so
every commit point from then on arms it (`RegLemmas.lean`); its `Commit()` returns a lower bound
`n + 1` of the counter (`batchTxBuffered.Commit.specCnt`), so at bbolt's `Begin(false)`, whose update
reads the committed data `Dc` from the invariant's half, the registration is armed: `reg_take` removes
it, giving `R` back (the saved `R` agrees, up to a later a credit strips) and `Q` of `Dc`. Lean-first
(no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.RegLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ReadLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend

/-- A key not in a finite map of `Nat` keys: one past the largest. -/
theorem nat_key_fresh {V : Type} (M : GMap Nat V) : ∃ i : Nat, M.lookup i = none := by
  have hle : ∀ (l : List (Nat × V)) (p : Nat × V), p ∈ l → p.1 ≤ (l.map Prod.fst).foldr max 0 := by
    intro l
    induction l with
    | nil => intro p hp; cases hp
    | cons a l ih =>
      intro p hp
      simp only [List.map_cons, List.foldr_cons]
      rcases List.mem_cons.1 hp with rfl | hp
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih p hp) (Nat.le_max_right _ _)
  refine ⟨((Iris.Std.toList M).map Prod.fst).foldr max 0 + 1, ?_⟩
  cases h : M.lookup (((Iris.Std.toList M).map Prod.fst).foldr max 0 + 1) with
  | none => rfl
  | some v =>
    exfalso
    have hm := (Iris.Std.toList_get (m := M)).2 h
    exact Nat.not_succ_le_self _ (hle _ _ hm)

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

instance cmtNames_timeless (γ : BNames) (gm gc : GName) :
    Timeless (cmtNames (GF := GF) γ gm gc) := by
  unfold cmtNames; infer_instance

/-- A lower bound of the counter is at most its value, the authority kept. -/
theorem monoNat_lb_le (gc : GName) (c m : Nat) :
    monoNatAuthOwn (GF := GF) gc 1 c ∗ monoNatLbOwn gc m ⊢ monoNatAuthOwn gc 1 c ∗ ⌜m ≤ c⌝ := by
  refine (and_intro sep_elim_left ?_).trans persistent_and_sep_mp
  iintro ⟨Ha, Hl⟩
  ihave %H := monoNatLbOwn_valid gc 1 c m $$ Ha Hl
  ipureintro; exact H.2

theorem savedProp_halves (γ : GName) (R : IProp GF) :
    savedPropOwn γ (DFrac.own 1) R ⊢
      savedPropOwn γ (DFrac.own (1 : Qp).half) R ∗ savedPropOwn γ (DFrac.own (1 : Qp).half) R := by
  conv => lhs; rw [← Qp.half_add_half 1]
  exact (Fractional.fractional (Φ := fun q : Qp => savedPropOwn (GF := GF) γ (.own q) R) _ _).1

theorem savedPred_halves (γ : GName) (Φ : Data → IProp GF) :
    savedPredOwn γ (DFrac.own 1) Φ ⊢
      savedPredOwn γ (DFrac.own (1 : Qp).half) Φ ∗ savedPredOwn γ (DFrac.own (1 : Qp).half) Φ := by
  conv => lhs; rw [← Qp.half_add_half 1]
  exact (Fractional.fractional (Φ := fun q : Qp => savedPredOwn (GF := GF) γ (.own q) Φ) _ _).1

/-- **Registering an observation** (see the file header): with the backend open (so not stopped), `R`
and its observation's wand go into the commit invariant under a fresh key, at the current count `n`;
the registrant keeps the key's element and its halves of the saved `R` and observation
(`regTok`), and a lower bound `n` of the counter. -/
theorem reg_register (γ : BNames) (P : BParams) (W Pk : IProp GF) (qo : Qp) (R : IProp GF)
    (Q : ObsQ) :
    cmtInv γ P W Pk ∗ bOpen γ qo ∗ R ∗ obsWand γ P W Pk R Q ⊢
      |={⊤}=> bOpen γ qo ∗ ∃ i n : Nat, regTok γ P i n R Q ∗ cntLb γ n := by
  iintro ⟨#Hinv, Hopen, HR, #Hw⟩
  iunfold cmtInv at Hinv
  iinv Hinv with Hb Hclose
  iunfold cmtBody at Hb
  icases Hb with (⟨%Dc, >Hh, #Hfk0, Hregs⟩ | >#Hst)
  rotate_left
  · iexfalso
    iapply bOpen_stopped γ qo $$ [$Hopen $Hst]
  iunfold cmtRegs at Hregs
  icases Hregs with ⟨%gm, %gc, %c, %M, >#Hn, >Hc, >Hm, Hes⟩
  obtain ⟨i, hi⟩ := nat_key_fresh M
  imod saved_prop_alloc R (DFrac.own 1) DFrac.valid_own_one with ⟨%γR, HsR⟩
  imod saved_pred_alloc (fun D : Data => iprop(⌜obsAt P Q D⌝ : IProp GF)) (DFrac.own 1)
    DFrac.valid_own_one with ⟨%γΨ, HsQ⟩
  icases savedProp_halves γR R $$ HsR with ⟨HsR1, HsR2⟩
  icases savedPred_halves γΨ _ $$ HsQ with ⟨HsQ1, HsQ2⟩
  imod ghost_map_insert i ((γR, γΨ, c) : GName × GName × Nat) hi $$ Hm with ⟨Hm, Hel⟩
  ihave #Hlb := monoNatLbOwn_get gc 1 c $$ Hc
  imod Hclose $$ [Hh Hc Hm Hes HR HsR2 HsQ2] with -
  · inext
    iunfold cmtBody
    ileft
    iexists Dc
    iframe Hh Hfk0
    iunfold cmtRegs
    iexists gm, gc, c, M.insert i (γR, γΨ, c)
    iframe Hn Hc Hm
    iapply (BigSepM.bigSepM_insert hi).2
    iframe Hes
    iunfold regEntry
    iexists R, Q
    iframe HsR2 HsQ2 HR Hw
    ipureintro
    intro h
    exact absurd h (Nat.lt_irrefl c)
  imodintro
  iframe Hopen
  iexists i, c
  isplitl [Hel HsR1 HsQ1]
  · iunfold regTok
    iexists gm, gc, γR, γΨ
    iframe Hn Hel HsR1 HsQ1
  iunfold cntLb
  iright
  iexists gm, gc
  iframe Hn Hlb

/-- **Taking an armed registration out** (see the file header), at any mask, from the registry at the
committed data `Dc` (under the commit invariant's later): with the registrant's element and a lower
bound past its count (a commit point came after it), the entry goes, `R` comes back with `Q` of `Dc`
(two credits: one strips the invariant's later off the entry, one the saved `R`'s agreement). -/
theorem reg_take (γ : BNames) (P : BParams) (W Pk : IProp GF) (i n : Nat) (R : IProp GF) (Q : ObsQ)
    (Dc : Data) (E : CoPset) :
    regTok γ P i n R Q ∗ cntLb γ (n + 1) ∗ (£ 1 ∗ £ 1) ∗ ▷ cmtRegs γ P W Pk Dc ⊢
      |={E}=> ▷ cmtRegs γ P W Pk Dc ∗ R ∗ ⌜obsAt P Q Dc⌝ := by
  iintro ⟨Ht, #Hlb, ⟨Hlc1, Hlc2⟩, Hregs⟩
  iunfold regTok at Ht
  icases Ht with ⟨%gm', %gc', %γR, %γΨ, #Hn', Hel, HsR, HsQ⟩
  iunfold cmtRegs at Hregs
  icases Hregs with ⟨%gm, %gc, %c, %M, >#Hn, >Hc, >Hm, Hes⟩
  iunfold cmtNames at Hn Hn'
  ihave %Hg := dghostVar_agree γ.txb ((gm, gc) : GName × GName) _ ((gm', gc') : GName × GName) _
    $$ Hn Hn'
  simp only [Prod.mk.injEq] at Hg
  obtain ⟨rfl, rfl⟩ := Hg
  ihave %Hlk := ghost_map_lookup $$ Hm Hel
  -- a commit point came after the registration: `n < c`
  iunfold cntLb at Hlb
  icases Hlb with (%h0 | ⟨%gm2, %gc2, #Hn2, #Hl⟩)
  · omega
  iunfold cmtNames at Hn2
  ihave %Hg2 := dghostVar_agree γ.txb ((gm, gc) : GName × GName) _ ((gm2, gc2) : GName × GName) _
    $$ Hn Hn2
  simp only [Prod.mk.injEq] at Hg2
  obtain ⟨rfl, rfl⟩ := Hg2
  icases monoNat_lb_le gc c (n + 1) $$ [$Hc $Hl] with ⟨Hc, %Hle⟩
  have hnc : n < c := Hle
  -- the entry out
  ihave Hes := later_mono (BigSepM.bigSepM_delete Hlk).1 $$ Hes
  icases Hes with ⟨He, Hes⟩
  iunfold regEntry at He
  icases He with ⟨%R', %Q', HsR', HsQ', HR', #Hw', Hon⟩
  -- the invariant's later off the entry
  ihave Hall : iprop(▷ (R' ∗ savedPropOwn γR (DFrac.own (1 : Qp).half) R' ∗
      savedPredOwn γΨ (DFrac.own (1 : Qp).half) (fun D : Data => iprop(⌜obsAt P Q' D⌝ : IProp GF)) ∗
      ⌜n < c → obsAt P Q' Dc⌝)) $$ [HR' HsR' HsQ' Hon]
  · inext
    iframe HR' HsR' HsQ'
    iexact Hon
  imod lc_fupd_elim_later (E := E) $$ Hlc1 Hall with ⟨HR', HsR', HsQ', %Hon'⟩
  -- the saved `R` and observation agree, after a later
  ihave HeqR := saved_prop_agree γR _ _ R R' $$ HsR HsR'
  ihave HeqQ := saved_pred_agree γΨ _ _ (fun D : Data => iprop(⌜obsAt P Q D⌝ : IProp GF))
    (fun D : Data => iprop(⌜obsAt P Q' D⌝ : IProp GF)) Dc $$ HsQ HsQ'
  ihave Hall2 : iprop(▷ ((R ≡ R') ∗ (iprop(⌜obsAt P Q Dc⌝ : IProp GF) ≡ iprop(⌜obsAt P Q' Dc⌝)))) $$
      [HeqR HeqQ]
  · inext
    iframe HeqR HeqQ
  imod lc_fupd_elim_later (E := E) $$ Hlc2 Hall2 with ⟨#HeqR', #HeqQ'⟩
  have hQ' : obsAt P Q' Dc := Hon' hnc
  ihave Hir := internalEq_iff R R' $$ HeqR'
  ihave Hiq := internalEq_iff _ _ $$ HeqQ'
  icases Hir with ⟨-, Hb⟩
  icases Hiq with ⟨-, Hbq⟩
  ihave HR := Hb $$ HR'
  ihave %HQ := Hbq $$ %hQ'
  imod ghost_map_delete $$ Hm Hel with Hm
  imodintro
  iframe HR
  isplitl [Hc Hm Hes]
  · inext
    iunfold cmtRegs
    iexists gm, gc, c, M.delete i
    iunfold cmtNames
    iframe Hn Hc Hm Hes
  ipureintro; exact HQ

end lemmas

end backend
end EtcdGrove
end Perennial
