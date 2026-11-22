/-
# remote: node 0's pending writes (`notes/remote-port-plan.md`, §4)

Node 0 (`Run`) checks the history against the pending-writes model `linkv.pSeq R.B` (through the
instance's decoding of porcupine's operations: `S.M`, `PendDec`), as txnlin does
(`Proof/.../etcd/txnlin/Inv.lean`, without revisions): a write whose outcome is unknown is
committed as pending, and may take effect later, at most once, or never.

- **The invariant** `pendCtx R γ` (at `pendCtxN`, in `pendN`, global: allocated at the deployment's start, so that
  every node may use it): lintest's `libState` is half of a ghost variable `γ.s` holding the model
  state `S` (`pendLib`); the invariant holds the other half, the far side's base state
  `R.sysState st`, and the authority of the **pending writes** `M` (a ghost map at `γ.p` of model
  inputs, `pendTok`: a write committed as pending whose update has not fired). `PendOk`: some
  configuration of `S` is `st` with exactly `M`'s writes pending, `S` is closed under late effects,
  and `M`'s keys are below `nx`.
- **The updates** (`pend_choice`): given lintest's linearization point for the input `iv i`
  (`linAU`, the atomic triple's update) and a later credit, node 0's `apply` makes `Do`'s choice:
  * an answer will come (`known`), with bytes `bs` (`Do`'s second prophecy): for a write, the
    update `lin R i Φ` with `Φ o` lintest's continuation at `ov o`; at its firing (at the far side,
    at its linearization point), it opens the invariant, hands over `sysState st`, and commits
    lintest's update with `(i, ok o)` at the step (`pendOk_ok`, `pend_commit_core`). For a read, a
    persistent update (the far side may fire it several times): a read commit invariant at `readN`
    holds lintest's update and a credit until the first firing whose output's bytes are `bs`, which
    commits there and records the output (persistently, `dghostVar`) with the continuation; every
    firing gives `Φb o := (encOut (ov o) = bs → recorded o)` (the same output: `hinj`), and at
    `Do`'s return the answered output, whose bytes are `bs`, takes the continuation out (a token);
  * no answer will: lintest's update commits at once with `unk i`: as pending for a write
    (`pendOk_errW`, minting the write's token), as nothing for a read (`pendOk_errR`); the
    continuation is `Ψ`, and the update with no result fires the pending write (`pend_fire`,
    `pendOk_fire`) or, for a read, changes nothing (`readNoop`).
- `readNoop`: a read's update with no result, persistently (a read changes nothing).
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Defs
public import Proof.github_com.anishathalye.porcupine.Defs
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.DGhostVar

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote

open EtcdGrove

/-! ## Pure part -/

section pure
variable {St I O : Type} [DecidableEq I]

/-- The pending writes (in some order). -/
def pendIns (M : GMap Nat I) : List I := M.toList.map Prod.snd

theorem pendIns_insert (M : GMap Nat I) (n : Nat) (i : I) (h : M !! n = none) :
    (pendIns (GMap.insert n i M)).Perm (i :: pendIns M) := by
  unfold pendIns
  have hp := Iris.Std.LawfulFiniteMap.toList_insert (M := GMap Nat) (m := M) (k := n) (v := i) h
  exact hp.map Prod.snd

theorem pendIns_delete (M : GMap Nat I) (n : Nat) (i : I) (h : M !! n = some i) :
    (pendIns M).Perm (i :: pendIns (GMap.delete n M)) := by
  unfold pendIns
  have hp := Iris.Std.LawfulFiniteMap.toList_delete (M := GMap Nat) (m := M) (k := n) (v := i) h
  exact hp.map Prod.snd

/-- **The invariant's relation** (see the file header). -/
structure PendOk (B : linkv.PendSpec St I O) (S : linkv.PSet St I) (st : St) (M : GMap Nat I)
    (nx : Nat) : Prop where
  closed : linkv.PSet.Closed B S
  fresh : ∀ n, nx ≤ n → M !! n = none
  cfg : ∃ c, S c ∧ c.st = st ∧ (pendIns M).Perm c.pend

variable {B : linkv.PendSpec St I O}

theorem pendOk_init : PendOk B (linkv.pInit B) B.init (∅ : GMap Nat I) 0 :=
  ⟨linkv.pInit_closed, fun _ _ => rfl, ⟨⟨B.init, []⟩, rfl, rfl, by simp [pendIns]⟩⟩

/-- An operation answered at the real configuration: the state stepped. -/
theorem pendOk_ok {S : linkv.PSet St I} {st : St} {M : GMap Nat I} {nx : Nat}
    (H : PendOk B S st M nx) (i : I) (ho : B.isObs i = false) :
    ∃ S', (linkv.pSeq B).step S (i, .ok (B.step i st).2) = some S' ∧
      PendOk B S' (B.step i st).1 M nx := by
  obtain ⟨c, hc, hst, hp⟩ := H.cfg
  obtain ⟨S', hS', hc'⟩ := linkv.pSeq_ok (P := B) hc i ho
  rw [hst] at hS' hc'
  exact ⟨S', hS', linkv.pSeq_step_closed hS', H.fresh, ⟨_, hc', rfl, hp⟩⟩

/-- A write committed as pending, its token minted at `nx`. -/
theorem pendOk_errW {S : linkv.PSet St I} {st : St} {M : GMap Nat I} {nx : Nat}
    (H : PendOk B S st M nx) (i : I) (hw : B.isWrite i = true) (ho : B.isObs i = false) :
    ∃ S', (linkv.pSeq B).step S (i, .err) = some S' ∧
      PendOk B S' st (GMap.insert nx i M) (nx + 1) := by
  obtain ⟨c, hc, hst, hp⟩ := H.cfg
  obtain ⟨S', hS', hc'⟩ := linkv.pSeq_errW_pending (P := B) hc i hw ho
  refine ⟨S', hS', linkv.pSeq_step_closed hS', ?_, ⟨_, hc', hst, ?_⟩⟩
  · intro n hn
    show (GMap.insert nx i M) !! n = none
    rw [GMap.lookup_insert_ne _ _ (by omega)]
    exact H.fresh n (by omega)
  · exact (pendIns_insert M nx i (H.fresh nx (Nat.le_refl _))).trans (hp.cons _)

/-- A read committed with no answer. -/
theorem pendOk_errR {S : linkv.PSet St I} {st : St} {M : GMap Nat I} {nx : Nat}
    (H : PendOk B S st M nx) (i : I) (hw : B.isWrite i = false) (ho : B.isObs i = false) :
    ∃ S', (linkv.pSeq B).step S (i, .err) = some S' ∧ PendOk B S' st M nx := by
  obtain ⟨c, hc, hst, hp⟩ := H.cfg
  obtain ⟨S', hS', hc'⟩ := linkv.pSeq_errR (P := B) hc i hw ho
  exact ⟨S', hS', linkv.pSeq_step_closed hS', H.fresh, ⟨c, hc', hst, hp⟩⟩

/-- **A late effect**: the pending write `n ↦ i` takes effect, the model state unchanged. -/
theorem pendOk_fire {S : linkv.PSet St I} {st : St} {M : GMap Nat I} {nx : Nat}
    (H : PendOk B S st M nx) (n : Nat) (i : I) (hn : M !! n = some i) :
    PendOk B S (B.step i st).1 (GMap.delete n M) nx := by
  obtain ⟨c, hc, hst, hp⟩ := H.cfg
  have hd := pendIns_delete M n i hn
  have hmem : i ∈ c.pend := hp.subset (hd.symm.subset List.mem_cons_self)
  refine ⟨H.closed, ?_, ⟨_, H.closed.apply hc hmem, by rw [hst], ?_⟩⟩
  · intro m hm
    show (GMap.delete n M) !! m = none
    by_cases e : n = m
    · subst e; exact GMap.lookup_delete _ _
    · rw [GMap.lookup_delete_ne _ e]; exact H.fresh m hm
  · refine List.Perm.cons_inv ((hd.symm.trans hp).trans ?_)
    exact List.perm_cons_erase hmem

/-- `run` of a history extended by one operation. -/
theorem run_snoc {σ α : Type} (M : SeqModel σ α) (s0 : σ) (h : List α) (S S' : σ) (a : α)
    (h1 : run M s0 h = some S) (h2 : M.step S a = some S') : run M s0 (h ++ [a]) = some S' := by
  induction h generalizing s0 with
  | nil =>
    simp only [run] at h1
    cases h1
    simp only [List.nil_append, run, h2]
  | cons b l ih =>
    simp only [run] at h1
    simp only [List.cons_append, run]
    cases hb : M.step s0 b with
    | none => rw [hb] at h1; cases h1
    | some s1 => rw [hb] at h1; exact ih s1 h1

end pure

/-! ## The model on porcupine's operations -/

section dec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors}
variable {St I O : Type} [DecidableEq I]

/-- porcupine's model `S` is the pending-writes model of `R.B` on the operations `R`'s Go values
make: an answered operation `(iv i, ov o)` steps as `(i, ok o)`, an unknown one `(iv i, unk i)`
as `(i, err)`, and porcupine's `Step` may be applied to both (`ioOk`). -/
structure PendDec (R : RBase GF St I O) (S : ModelSpec GF (linkv.PSet St I)) : Prop where
  init : S.M.init = linkv.pInit R.B
  ok : ∀ s i o, S.M.step s (R.iv i, R.ov o) = (linkv.pSeq R.B).step s (i, .ok o)
  err : ∀ s i, S.M.step s (R.iv i, R.unk i) = (linkv.pSeq R.B).step s (i, .err)
  ioOk_ok : ∀ i o, ⊢ S.ioOk (R.iv i) (R.ov o)
  ioOk_err : ∀ i, ⊢ S.ioOk (R.iv i) (R.unk i)
  noObs : ∀ i, R.B.isObs i = false

end dec

/-! ## The ghost state and the invariant -/

/-- Node 0's ghost names: the model state's variable, the pending writes' map. -/
structure PendNames where
  s : GName
  p : GName

def pendN : Namespace := remoteN.@"pend"
/-- The invariant `pendCtx`'s namespace, and the read commits' (`pend_choice`), both in `pendN`:
lintest's update is over the mask `R.Eop ∪ pendN`, so it may be fired with both open. -/
def pendCtxN : Namespace := pendN.@"ctx"
def readN : Namespace := pendN.@"read"

theorem pendCtxN_sub (E : CoPset) (h : (↑pendN : CoPset) ⊆ E) : (↑pendCtxN : CoPset) ⊆ E :=
  fun p hp => h p (nclose_subseteq pendN "ctx" p hp)

theorem readN_sub (E : CoPset) (h : (↑pendN : CoPset) ⊆ E) :
    (↑readN : CoPset) ⊆ E \ ↑pendCtxN := by
  intro p hp
  rw [Std.LawfulSet.mem_diff]
  exact ⟨h p (nclose_subseteq pendN "read" p hp), fun h' =>
    (mask_ndot_ne' pendN "read" "ctx" (by decide) p hp |> (Std.LawfulSet.mem_diff).1).2 h'⟩

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF]

include Gg

attribute [local instance] GooseGlobalGS.gooseInvGS

variable {St I O : Type} [DecidableEq I] [Pos.Countable I] [Pos.Countable O]
variable (R : RBase GF St I O)

/-- lintest's `libState`: half of the history's variable, the model state `run` reaches from it
(a ghost variable needs a countable type, which a model state, a set of configurations, is not). -/
def pendLib (S : ModelSpec GF (linkv.PSet St I)) (γ : PendNames) (s : linkv.PSet St I) : IProp GF :=
  iprop(∃ h : List OpV, ghostVar γ.s (1 : Qp).half h ∗ ⌜run S.M S.M.init h = some s⌝)

/-- **A pending write's token** (exclusive): the write `i` committed as pending under `n`. -/
def pendTok (γ : PendNames) (n : Nat) (i : I) : IProp GF := ghostMapElem γ.p n (DFrac.own 1) i

/-- The invariant's contents (see the file header). -/
def pendBody (S : ModelSpec GF (linkv.PSet St I)) (γ : PendNames) : IProp GF :=
  iprop(∃ (h : List OpV) (s : linkv.PSet St I) (st : St) (M : GMap Nat I) (nx : Nat),
    ghostVar γ.s (1 : Qp).half h ∗ R.sysState st ∗ ghostMapAuth γ.p 1 M ∗
    ⌜run S.M S.M.init h = some s ∧ PendOk R.B s st M nx⌝)

/-- The invariant (persistent). -/
def pendCtx (S : ModelSpec GF (linkv.PSet St I)) (γ : PendNames) : IProp GF :=
  inv pendCtxN (pendBody R S γ)

instance pendCtx_persistent S γ : Persistent (pendCtx R S γ) := by unfold pendCtx; infer_instance

/-- lintest's linearization point for the input `x` (its atomic triple's update, the `▷`
stripped), over `pendLib`, with mask `Eapp`; `K o` is what committing with `o` gives. -/
def linAU (S : ModelSpec GF (linkv.PSet St I)) (γ : PendNames) (Eapp : CoPset) (x : GoInterface)
    (K : GoInterface → IProp GF) : IProp GF :=
  iprop(|={⊤ \ Eapp, ∅}=> ∃ s, pendLib S γ s ∗ ∀ s' o,
    (pendLib S γ s' ∗ ⌜S.M.step s (x, o) = some s'⌝) -∗ |={∅, ⊤ \ Eapp}=> K o)

end defs

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF]

include Gg

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [π : NetProtoGS]
variable {St I O : Type} [DecidableEq I] [Pos.Countable I] [Pos.Countable O]
variable (R : RBase GF St I O) [hT : ∀ st, Timeless (R.sysState st)]

include hT in
instance pendBody_timeless (S : ModelSpec GF (linkv.PSet St I)) (γ : PendNames) :
    Timeless (pendBody (Gg := Gg) R S γ) := by
  unfold pendBody; infer_instance

/-- The invariant at the deployment's start: the model's initial state, nothing pending. -/
theorem pend_alloc (E : CoPset) (S : ModelSpec GF (linkv.PSet St I))
    (hinit : S.M.init = linkv.pInit R.B) :
    ⊢ R.sysState R.B.init ={E}=∗ ∃ γ, pendCtx (Gg := Gg) R S γ ∗ pendLib (Gg := Gg) S γ S.M.init := by
  iintro Hs
  imod ghostVar_alloc (GF := GF) ([] : List OpV) with ⟨%γs, Hv⟩
  icases (ghostVar_split_half γs 1 ([] : List OpV)).mp $$ Hv with ⟨Hv1, Hv2⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := I) with ⟨%γp, Hm⟩
  imod inv_alloc pendCtxN E (pendBody (Gg := Gg) R S ⟨γs, γp⟩) $$ [Hv1 Hs Hm] with #Hinv
  · inext
    unfold pendBody
    iexists [], linkv.pInit R.B, R.B.init, ∅, 0
    iframe Hv1 Hs Hm
    ipureintro; exact ⟨by rw [hinit]; rfl, pendOk_init⟩
  imodintro
  iexists ⟨γs, γp⟩
  unfold pendCtx pendLib
  iframe Hinv
  iexists []
  iframe Hv2
  ipureintro; rfl

/-- **A read's update with no result**, persistently: it changes nothing. -/
theorem readNoop (hE : (↑pendN : CoPset) ⊆ ⊤ \ R.Eop) (S : ModelSpec GF (linkv.PSet St I))
    (γ : PendNames) (i : I) (hw : R.B.isWrite i = false) :
    pendCtx (Gg := Gg) R S γ ⊢ □ lin (Gg := Gg) R i (fun _ => iprop(True)) := by
  iintro #Hinv
  imodintro
  unfold lin pendCtx
  have hc := pendCtxN_sub _ hE
  iinv Hinv with >Hi Hclose
  iunfold pendBody at Hi
  icases Hi with ⟨%h, %s, %st, %M, %nx, Hv, Hs, Hm, %Hok⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose2
  iexists st
  iframe Hs
  iintro Hs
  imod Hclose2 with -
  rw [R.reads_stay i st hw]
  imod Hclose $$ [Hv Hs Hm] with -
  · inext
    unfold pendBody
    iexists h, s, st, M, nx
    iframe Hv Hs Hm
    ipureintro; exact Hok
  imodintro
  itrivial

/-- **A pending write's update with no result**: it takes effect (once: its token). -/
theorem pend_fire (hE : (↑pendN : CoPset) ⊆ ⊤ \ R.Eop) (S : ModelSpec GF (linkv.PSet St I))
    (γ : PendNames) (n : Nat) (i : I) :
    ⊢ pendCtx (Gg := Gg) R S γ -∗ pendTok (Gg := Gg) γ n i -∗
      lin (Gg := Gg) R i (fun _ => iprop(True)) := by
  iintro #Hinv Htok
  unfold lin pendCtx
  have hc := pendCtxN_sub _ hE
  iinv Hinv with >Hi Hclose
  iunfold pendBody at Hi
  icases Hi with ⟨%h, %s, %st, %M, %nx, Hv, Hs, Hm, %Hok⟩
  unfold pendTok
  icases ghost_map_lookup $$ Hm Htok with %hn
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose2
  iexists st
  iframe Hs
  iintro Hs
  imod Hclose2 with -
  imod ghost_map_delete $$ Hm Htok with Hm
  imod Hclose $$ [Hv Hs Hm] with -
  · inext
    unfold pendBody
    iexists h, s, (R.B.step i st).1, GMap.delete n M, nx
    iframe Hv Hs Hm
    ipureintro; exact ⟨Hok.1, pendOk_fire Hok.2 n i hn⟩
  imodintro
  itrivial

/-- lintest's update committed at the step of `i` from the invariant's state: the update `lin`
with lintest's continuation at the step's output. The core of `pend_choice`'s answered cases. -/
theorem pend_commit_core (hE : (↑pendN : CoPset) ⊆ ⊤ \ R.Eop) (S : ModelSpec GF (linkv.PSet St I))
    (hS : PendDec R S) (γ : PendNames) (i : I) (K : GoInterface → IProp GF) (E : CoPset)
    (hsub : ⊤ \ (R.Eop ∪ ↑pendN) ⊆ E) (st : St) (h : List OpV) (s0 : linkv.PSet St I)
    (M : GMap Nat I) (nx : Nat) (Hok : run S.M S.M.init h = some s0 ∧ PendOk R.B s0 st M nx) :
    ⊢ linAU (Gg := Gg) S γ (R.Eop ∪ ↑pendN) (R.iv i) K -∗ ghostVar γ.s (1 : Qp).half h -∗
      |={E, ∅}=> ∃ h' s', ghostVar γ.s (1 : Qp).half h' ∗
        ⌜run S.M S.M.init h' = some s' ∧ PendOk R.B s' (R.B.step i st).1 M nx⌝ ∗
        |={∅, E}=> K (R.ov (R.B.step i st).2) := by
  iintro HU Hv
  imod (fupd_mask_subseteq hsub) with Hclose3
  unfold linAU
  imod HU with ⟨%s, Hl, HU⟩
  unfold pendLib
  icases Hl with ⟨%h0, Hl, %Hr0⟩
  ihave %Heq := ghostVar_agree γ.s h (1 : Qp).half h0 (1 : Qp).half $$ Hv Hl
  subst Heq
  have Hs0 : s = s0 := Option.some.inj (Hr0.symm.trans Hok.1)
  subst Hs0
  obtain ⟨S', HS', Hok'⟩ := pendOk_ok Hok.2 i (hS.noObs i)
  have Hst : S.M.step s (R.iv i, R.ov (R.B.step i st).2) = some S' := by rw [hS.ok]; exact HS'
  have Hr' := run_snoc S.M S.M.init h s S' _ Hok.1 Hst
  imod ghostVar_update_halves (h ++ [(R.iv i, R.ov (R.B.step i st).2)]) γ.s h h $$ Hv Hl
    with ⟨Hv, Hl⟩
  imodintro
  iexists _, S'
  iframe Hv
  isplitr
  · ipureintro; exact ⟨Hr', Hok'⟩
  imod HU $$ %S' %(R.ov (R.B.step i st).2) [Hl] with HK
  · isplitl [Hl]
    · iexists _
      iframe Hl
      ipureintro; exact Hr'
    · ipureintro; exact Hst
  imod Hclose3 with -
  imodintro
  iexact HK

/-- **Node 0's choice** for `Do` (see the file header): from lintest's update for `iv i` (with a
later credit), and the bytes `bs` `Do`'s prophecy says the answer will have, a slot update
committing it at the far side's step if an answer will come (a write's at its one firing; a read's,
which may fire several times, at the first firing whose output's bytes are `bs`: the read commit
invariant at `readN`, with the continuation kept until `Do` returns), or a commit now and an update
with no result if none will. -/
theorem pend_choice (hE : (↑pendN : CoPset) ⊆ ⊤ \ R.Eop) (S : ModelSpec GF (linkv.PSet St I))
    (hS : PendDec R S) (hinj : ∀ o o', R.encOut (R.ov o) = R.encOut (R.ov o') → o = o')
    (γ : PendNames) (i : I) (K : GoInterface → IProp GF) :
    ⊢ pendCtx (Gg := Gg) R S γ -∗ £ 1 -∗ ▷ linAU (Gg := Gg) S γ (R.Eop ∪ ↑pendN) (R.iv i) K -∗
      ∀ (known : Bool) (bs : List w8), |={⊤}=> if known then
        (∃ Φb : O → IProp GF, slotUpd (Gg := Gg) R i Φb ∗
          (∀ o, ⌜R.encOut (R.ov o) = bs⌝ -∗ Φb o -∗ £ 1 ={⊤}=∗ K (R.ov o)))
        else (K (R.unk i) ∗ lin (Gg := Gg) R i (fun _ => iprop(True))) := by
  have hctx := pendCtxN_sub _ hE
  have hsub : ⊤ \ (R.Eop ∪ ↑pendN) ⊆ (⊤ \ R.Eop) \ ↑pendCtxN := by
    intro p hp
    rw [Std.LawfulSet.mem_diff] at hp ⊢
    rw [Std.LawfulSet.mem_union, not_or] at hp
    exact ⟨(Std.LawfulSet.mem_diff).2 ⟨hp.1, hp.2.1⟩,
      fun h => hp.2.2 (nclose_subseteq pendN "ctx" p h)⟩
  have hsub' : ⊤ \ (R.Eop ∪ ↑pendN) ⊆ ⊤ \ ↑pendCtxN := by
    intro p hp
    have := hsub p hp
    rw [Std.LawfulSet.mem_diff] at this ⊢
    exact ⟨CoPset.mem_full, this.2⟩
  have hsubR : ⊤ \ (R.Eop ∪ ↑pendN) ⊆ ((⊤ \ R.Eop) \ ↑pendCtxN) \ ↑readN := by
    intro p hp
    have h1 := hsub p hp
    rw [Std.LawfulSet.mem_diff] at hp ⊢
    rw [Std.LawfulSet.mem_union, not_or] at hp
    exact ⟨h1, fun h => hp.2.2 (nclose_subseteq pendN "read" p h)⟩
  have hreadN : (↑readN : CoPset) ⊆ (⊤ \ R.Eop) \ ↑pendCtxN := readN_sub _ hE
  have hreadT : (↑readN : CoPset) ⊆ ⊤ := fun p _ => CoPset.mem_full
  iintro #Hinv Hlc HU %known %bs
  cases known with
  | true =>
    simp only [↓reduceIte]
    cases hw : R.B.isWrite i with
    | true =>
      -- a write: its one firing commits lintest's update with its answer
      imod (lc_fupd_elim_later (GF := GF) (E := ⊤)
        (P := linAU (Gg := Gg) S γ (R.Eop ∪ ↑pendN) (R.iv i) K)) $$ Hlc HU with HU
      imodintro
      iexists (fun o => K (R.ov o))
      isplitl [HU]
      · rw [slotUpd_write R hw]
        unfold lin pendCtx
        iinv Hinv with >Hi Hclose
        try (exact hctx)
        iunfold pendBody at Hi
        icases Hi with ⟨%h, %s0, %st, %M, %nx, Hv, Hs, Hm, %Hok⟩
        imod pend_commit_core R hE S hS γ i K _ hsub st h s0 M nx Hok $$ HU Hv
          with ⟨%h', %s', Hv, %Hok', HK⟩
        imodintro
        iexists st
        iframe Hs
        iintro Hs
        imod HK with HK
        imod Hclose $$ [Hv Hs Hm] with -
        · inext
          unfold pendBody
          iexists h', s', (R.B.step i st).1, M, nx
          iframe Hv Hs Hm
          ipureintro; exact Hok'
        imodintro
        iexact HK
      · iintro %o - HK -
        imodintro
        iexact HK
    | false =>
      -- a read: it commits at the first firing whose output's bytes are `bs`
      imod dghostVar_alloc (GF := GF) (none : Option O) with ⟨%γc, Hγc⟩
      imod token_alloc (GF := GF) with ⟨%γt, Htok⟩
      imod inv_alloc readN ⊤ (iprop(
          (linAU (Gg := Gg) S γ (R.Eop ∪ ↑pendN) (R.iv i) K ∗ £ 1 ∗
            dghostVar γc (DFrac.own 1) (none : Option O)) ∨
          (∃ o : O, ⌜R.encOut (R.ov o) = bs⌝ ∗ dghostVar γc DFrac.discard (some o) ∗
            (K (R.ov o) ∨ token γt)))) $$ [HU Hlc Hγc]
        with #Hci
      · iintro !>
        ileft
        iframe HU Hlc Hγc
      imodintro
      iexists (fun o => iprop(⌜R.encOut (R.ov o) = bs⌝ → dghostVar γc DFrac.discard (some o)))
      isplitr [Htok]
      · rw [slotUpd_read R hw]
        imodintro
        unfold lin pendCtx
        iinv Hinv with >Hi Hclose
        try (exact hctx)
        iunfold pendBody at Hi
        icases Hi with ⟨%h, %s0, %st, %M, %nx, Hv, Hs, Hm, %Hok⟩
        iinv Hci with Hc Hclosec
        try (exact hreadN)
        have hst := R.reads_stay i st hw
        by_cases hb : R.encOut (R.ov (R.B.step i st).2) = bs
        · icases Hc with (⟨HU, >Hlc, >Hγc⟩ | Hc)
          · -- the first firing with the answer's bytes: commit here
            imod (lc_fupd_elim_later (GF := GF) (E := ((⊤ \ R.Eop) \ ↑pendCtxN) \ ↑readN)
              (P := linAU (Gg := Gg) S γ (R.Eop ∪ ↑pendN) (R.iv i) K)) $$ Hlc HU with HU
            imod pend_commit_core R hE S hS γ i K _ hsubR st h s0 M nx Hok $$ HU Hv
              with ⟨%h', %s', Hv, %Hok', HK⟩
            imodintro
            iexists st
            iframe Hs
            iintro Hs
            imod HK with HK
            imod dghostVar_update (some (R.B.step i st).2) γc none $$ Hγc with Hγc
            imod dghostVar_persist γc 1 (some (R.B.step i st).2) $$ Hγc with #Hγc
            imod Hclosec $$ [HK] with -
            · inext
              iright
              iexists (R.B.step i st).2
              iframe Hγc
              isplit
              · ipureintro; exact hb
              ileft; iexact HK
            imod Hclose $$ [Hv Hs Hm] with -
            · inext
              unfold pendBody
              iexists h', s', (R.B.step i st).1, M, nx
              iframe Hv Hs Hm
              ipureintro; exact Hok'
            imodintro
            iintro -
            iexact Hγc
          · -- committed before, with the same bytes: the same output
            imod (later_exists_except0 (PROP := IProp GF)) $$ Hc with ⟨%o', Hc⟩
            icases Hc with ⟨>%hbo', >#Hγo, HK⟩
            have ho : (R.B.step i st).2 = o' := hinj _ _ (hb.trans hbo'.symm)
            iapply fupd_mask_intro Std.LawfulSet.empty_subset
            iintro Hclose2
            iexists st
            iframe Hs
            iintro Hs
            imod Hclose2 with -
            imod Hclosec $$ [HK] with -
            · inext
              iright
              iexists o'
              iframe Hγo HK
              ipureintro; exact hbo'
            rw [hst]
            imod Hclose $$ [Hv Hs Hm] with -
            · inext
              unfold pendBody
              iexists h, s0, st, M, nx
              iframe Hv Hs Hm
              ipureintro; exact Hok
            imodintro
            iintro %hb'
            rw [ho]
            iexact Hγo
        · -- another output: nothing to commit
          iapply fupd_mask_intro Std.LawfulSet.empty_subset
          iintro Hclose2
          iexists st
          iframe Hs
          iintro Hs
          imod Hclose2 with -
          imod Hclosec $$ [Hc] with -
          · inext; iexact Hc
          rw [hst]
          imod Hclose $$ [Hv Hs Hm] with -
          · inext
            unfold pendBody
            iexists h, s0, st, M, nx
            iframe Hv Hs Hm
            ipureintro; exact Hok
          imodintro
          iintro %hb'
          exfalso; exact hb hb'
      · -- `Do`'s return: the answer's bytes are `bs`, so it is the committed output
        iintro %o %hbo HΦ Hlc
        ihave #Hγo := HΦ $$ %hbo
        iinv Hci with Hc Hclosec
        try (exact hreadT)
        icases Hc with (⟨-, -, >Hγc⟩ | Hc)
        · icases dghostVar_agree γc (none : Option O) (DFrac.own 1) (some o) DFrac.discard
            $$ Hγc Hγo with %h
          cases h
        · imod (later_exists_except0 (PROP := IProp GF)) $$ Hc with ⟨%o', Hc⟩
          icases Hc with ⟨>%hbo', >#Hγo', HK⟩
          icases dghostVar_agree γc (some o') DFrac.discard (some o) DFrac.discard
            $$ Hγo' Hγo with %h
          cases h
          icases HK with (HK | >Htok')
          · imod (lc_fupd_elim_later (GF := GF) (E := ⊤ \ ↑readN) (P := K (R.ov o))) $$ Hlc HK
              with HK
            imod Hclosec $$ [Htok] with -
            · inext
              iright
              iexists o
              iframe Hγo'
              isplit
              · ipureintro; exact hbo'
              iright; iexact Htok
            imodintro
            iexact HK
          · iexfalso
            iapply token_exclusive γt $$ Htok Htok'
  | false =>
    -- no answer will come: commit now, with the unknown output
    simp only [Bool.false_eq_true, ↓reduceIte]
    imod (lc_fupd_elim_later (GF := GF) (E := ⊤)
      (P := linAU (Gg := Gg) S γ (R.Eop ∪ ↑pendN) (R.iv i) K)) $$ Hlc HU with HU
    have htop : (↑pendCtxN : CoPset) ⊆ ⊤ := fun p _ => CoPset.mem_full
    unfold pendCtx
    iinv Hinv with >Hi Hclose
    try (exact htop)
    iunfold pendBody at Hi
    icases Hi with ⟨%h, %s0, %st, %M, %nx, Hv, Hs, Hm, %Hok⟩
    imod (fupd_mask_subseteq hsub') with Hclose3
    unfold linAU
    imod HU with ⟨%s, Hl, HU⟩
    unfold pendLib
    icases Hl with ⟨%h0, Hl, %Hr0⟩
    ihave %Heq := ghostVar_agree γ.s h (1 : Qp).half h0 (1 : Qp).half $$ Hv Hl
    subst Heq
    have Hs0 : s = s0 := Option.some.inj (Hr0.symm.trans Hok.1)
    subst Hs0
    cases hw : R.B.isWrite i with
    | true =>
      obtain ⟨S', HS', Hok'⟩ := pendOk_errW Hok.2 i hw (hS.noObs i)
      have Hst : S.M.step s (R.iv i, R.unk i) = some S' := by rw [hS.err]; exact HS'
      have Hr' := run_snoc S.M S.M.init h s S' _ Hok.1 Hst
      imod ghostVar_update_halves (h ++ [(R.iv i, R.unk i)]) γ.s h h $$ Hv Hl with ⟨Hv, Hl⟩
      imod ghost_map_insert nx i (Hok.2.fresh nx (Nat.le_refl _)) $$ Hm with ⟨Hm, Htok⟩
      imod HU $$ %S' %(R.unk i) [Hl] with HK
      · isplitl [Hl]
        · iexists _
          iframe Hl
          ipureintro; exact Hr'
        · ipureintro; exact Hst
      imod Hclose3 with -
      imod Hclose $$ [Hv Hs Hm] with -
      · inext
        unfold pendBody
        iexists _, S', st, GMap.insert nx i M, nx + 1
        iframe Hv Hs Hm
        ipureintro; exact ⟨Hr', Hok'⟩
      imodintro
      iframe HK
      iapply pend_fire R hE S γ nx i $$ [] [Htok]
      · unfold pendCtx; iexact Hinv
      · unfold pendTok; iexact Htok
    | false =>
      obtain ⟨S', HS', Hok'⟩ := pendOk_errR Hok.2 i hw (hS.noObs i)
      have Hst : S.M.step s (R.iv i, R.unk i) = some S' := by rw [hS.err]; exact HS'
      have Hr' := run_snoc S.M S.M.init h s S' _ Hok.1 Hst
      imod ghostVar_update_halves (h ++ [(R.iv i, R.unk i)]) γ.s h h $$ Hv Hl with ⟨Hv, Hl⟩
      imod HU $$ %S' %(R.unk i) [Hl] with HK
      · isplitl [Hl]
        · iexists _
          iframe Hl
          ipureintro; exact Hr'
        · ipureintro; exact Hst
      imod Hclose3 with -
      imod Hclose $$ [Hv Hs Hm] with -
      · inext
        unfold pendBody
        iexists _, S', st, M, nx
        iframe Hv Hs Hm
        ipureintro; exact ⟨Hr', Hok'⟩
      imodintro
      iframe HK
      ihave #Hr := readNoop R hE S γ i hw $$ [Hinv]
      · unfold pendCtx; iexact Hinv
      iexact Hr

end laws

end github_com.mit_pdos.etcd_grove.examples.lib.remote
end Perennial
