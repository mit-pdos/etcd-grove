/-
The client machine's linearization (dsv-swiftpaxos, notes/dsv-swiftpaxos.md, step 5; replaces the
lab's `ClientAU.lean`, whose update was the lab driver's atomic update over `ownState`): remote's
store is `swRK γ γk` (`KitModel.lean`'s `swR`), whose state `σ : St` (each key's value) is a ghost
variable `γk` of the kit's two keys' values (half `sysK γk σ`, remote's; half in the invariant
`linkInv`), which the invariant ties to the SwiftPaxos slot's abstract key-value state
`linOwn γ.lin σ'` (the half the clients' atomic specs take; the other half is in `sp.inv`) at
keys `0` and `1` (`lin.keyName`). `BufferClient.Write`'s and `Read`'s logically atomic specs need
an atomic update, which can abort; remote's base update `lin` cannot: so the update opens
`linkInv` (abortable: it gives `linOwn` back) and fires `lin` only at the commit, at the mask
`(⊤ \ ↑sp.spN) \ ↑linkN` (`⊤ \ Eop`).

Unlike the lab's `ownState`, the state does not require non-empty values: the kit's `op` returns a
get's value as it is (the lab's `Op` read `""` as "not found"), and the model's initial value is `""`.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.Interface
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.KitModel

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv
open github_com.mit_pdos.etcd_grove.examples.lib.remote
open github_com.imdea_software.swiftpaxos.examples.swiftnet

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp netShaExts_has
  netShaExts_hasSha256 GooseGlobalGS.gooseInvGS

namespace cnode

/-- The link invariant's namespace. -/
def linkN : Namespace := ndot nroot "swiftnet.link"

/-- The kit store's operations' mask: the slot's and the link invariant's namespaces (as a
complement, so that `⊤ \ swEop` is the mask inside both, `swEop_diff`). -/
def swEop : CoPset := ⊤ \ ((⊤ \ ↑sp.spN) \ ↑linkN)

theorem swEop_diff : (⊤ \ swEop : CoPset) = (⊤ \ ↑sp.spN) \ ↑linkN :=
  Iris.Std.LawfulSet.diff_self_diff_of_subset CoPset.subseteq_top

/-- The kit's two keys' values (a ghost variable's value). -/
def kpair (σ : St) : GoString × GoString := ((σ 0).1, (σ 1).1)

/-- The slot's key-value state `σ'` at the kit's keys has the values `p`. -/
def relP (p : GoString × GoString) (σ' : (kv GoString GoString).State) : Prop :=
  (σ' (lin.keyName (W64 0))).getD [] = p.1 ∧ (σ' (lin.keyName (W64 1))).getD [] = p.2

section defs
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF]

/-- **The far side's state** (remote's `sysState`): half of the ghost variable `γk`. -/
def sysK (γk : GName) (σ : St) : IProp netDistGF :=
  ghostVar γk (1 : Qp).half (kpair σ)

instance sysK_timeless (γk : GName) (σ : St) : Timeless (sysK γk σ) := by
  unfold sysK ghostVar; infer_instance

/-- **The link invariant**: the other half of `γk`, and the slot's state at those values. -/
def linkI (γ : SwiftNames netDistGF) (γk : GName) : IProp netDistGF :=
  iprop(∃ (p : GoString × GoString) (ps : List (GoString × GoString)),
    ghostVar γk (1 : Qp).half p ∗ ghostVar γ.lin (1 : Qp).half ps ∗ ⌜relP p (lin.stateOf ps)⌝)

def linkInv (γ : SwiftNames netDistGF) (γk : GName) : IProp netDistGF :=
  inv linkN (linkI γ γk)

instance linkInv_persistent (γ : SwiftNames netDistGF) (γk : GName) :
    Persistent (linkInv γ γk) := by
  unfold linkInv; infer_instance

/-- The kit's store over the slot. -/
abbrev swRK (γk : GName) : RBase netDistGF St KIn KIn BStr := swR (sysK γk) swEop

end defs

/-! ## The steps -/

/-- A put of `i` keeps the relation. -/
theorem relP_put (σ : St) (σ' : (kv GoString GoString).State) (i : KIn)
    (h : relP (kpair σ) σ') :
    relP (kpair (upd σ i.key i.bval))
      (sp.lin.apply (sp.Cmd.put (W64 (i.key : Int)) i.val) σ').1 := by
  have hk := i.key_lt
  obtain ⟨h0, h1⟩ := h
  simp only [relP, kpair, sp.lin.apply, sp.Cmd.put, sp.Cmd.isPut, beq_self_eq_true, ↓reduceIte]
  rcases (show i.key = 0 ∨ i.key = 1 by omega) with hk0 | hk1
  · rw [hk0]
    refine ⟨by simp [upd_same, KIn.bval, hk0], ?_⟩
    have hne : lin.keyName (W64 1) ≠ lin.keyName (W64 ((0 : Nat) : Int)) := by decide
    simp only [hne, ↓reduceIte, upd_ne σ _ (show (1 : Nat) ≠ i.key by omega)]
    exact h1
  · rw [hk1]
    have hne : lin.keyName (W64 0) ≠ lin.keyName (W64 ((1 : Nat) : Int)) := by decide
    simp only [hne, ↓reduceIte, upd_ne σ _ (show (0 : Nat) ≠ i.key by omega)]
    refine ⟨h0, by simp [upd_same, KIn.bval, hk1]⟩

/-- A get of `i` reads the relation's value. -/
theorem relP_get (σ : St) (σ' : (kv GoString GoString).State) (i : KIn)
    (h : relP (kpair σ) σ') :
    (σ' (lin.keyName (W64 (i.key : Int)))).getD [] = (σ i.key).1 := by
  have hk := i.key_lt
  obtain ⟨h0, h1⟩ := h
  rcases (show i.key = 0 ∨ i.key = 1 by omega) with hk0 | hk1
  · rw [hk0]; exact h0
  · rw [hk1]; exact h1

section au
variable [GoGlobalContext] [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [π : NetProtoGS] [ρ : RemoteGS]

theorem linkN_spN : (↑linkN : CoPset) ⊆ ⊤ \ ↑sp.spN := by
  unfold linkN sp.spN
  solve_ndisj

/-- A put through `Write`'s atomic triple (any expression `e` with `Write`'s spec shape, its
private postcondition `P`): remote's update committed at the triple's commit, with `swB`'s
output (`""`). -/
theorem put_of_lin (γ : SwiftNames netDistGF) (γk : GName) (i : KIn) (hput : i.put = true)
    (Φ : BStr → IProp netDistGF) (e : Expr) (P : IProp netDistGF) :
    (<<{ ∀∀ σ, linOwn γ.lin σ }>> e @ ↑sp.spN
      <<{ linOwn γ.lin (sp.lin.apply (sp.Cmd.put (W64 (i.key : Int)) i.val) σ).1 |
          RET #(); P }>>) ⊢
    linkInv (G := hG.goose_globalGS) γ γk -∗ lin (Gg := hG.goose_globalGS) (swRK γk) i Φ -∗
    WP e {{ r, ⌜r = #()⌝ ∗ P ∗ Φ bnil }} := by
  iintro Hwp #Hinv Hlin
  iunfold atomic_wp at Hwp
  iapply Hwp
  iauintro
  unfold atomic_acc
  iunfold linkInv at Hinv
  iinv Hinv with Hi Hclose
  · exact linkN_spN
  iunfold linkI at Hi
  icases Hi with ⟨%p, %ps, Hp, Hσ, Hrel⟩
  imod Hp
  imod Hσ
  imod Hrel with %Hrel
  ihave Hσ : linOwn γ.lin (lin.stateOf ps) $$ [Hσ]
  · iunfold linOwn; iexists ps; iframe Hσ; ipureintro; rfl
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists (⟨lin.stateOf ps, ⟨⟩⟩ : (Tele.cons fun _ : (kv GoString GoString).State => Tele.nil).Arg)
  dsimp only [Tele.lam, Tele.app, Tele.bind, BI.tforall_cons, BI.tforall_nil, BIBase.wandM]
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hmask with -
    imod Hclose $$ [Hσ Hp] with -
    · inext
      iunfold linkI
      iunfold linOwn at Hσ
      icases Hσ with ⟨%ps', Hσ, %Hps'⟩
      iexists p, ps'
      iframe Hσ Hp
      ipureintro; rw [← Hps']; exact Hrel
    imodintro
    iframe
  · iintro Hσ'
    imod Hmask with -
    iunfold lin at Hlin
    rw [show ((swRK (G := hG.goose_globalGS) γk).Eop) = swEop from rfl, swEop_diff]
    imod Hlin with ⟨%st, Hst, Hc⟩
    ihave Hst : ghostVar γk (1 : Qp).half (kpair st) $$ [Hst]
    · simp only [swRK, swR, sysK]; iexact Hst
    icombine Hst Hp gives %Hg
    have Hpe := Hg.2
    subst Hpe
    simp only [swRK, swR, swB_put i hput]
    imod ghostVar_update_halves (kpair (upd st i.key i.bval)) γk (kpair st) (kpair st) $$ Hst Hp
      with ⟨Hst, Hp⟩
    imod Hc $$ [Hst] with HΦ
    · unfold sysK; iexact Hst
    imod Hclose $$ [Hσ' Hp] with -
    · inext
      iunfold linkI
      iunfold linOwn at Hσ'
      icases Hσ' with ⟨%ps', Hσ', %Hps'⟩
      iexists _, ps'
      iframe Hσ' Hp
      ipureintro; rw [← Hps']; exact relP_put st _ i Hrel
    imodintro
    iintro HP
    iframe HP HΦ

/-- A get through `Read`'s atomic triple: remote's update committed at the triple's commit, the
returned slice holding the key's value. -/
theorem get_of_lin (γ : SwiftNames netDistGF) (γk : GName) (i : KIn) (hget : i.put = false)
    (Φ : BStr → IProp netDistGF) (e : Expr) (P : IProp netDistGF) :
    (<<{ ∀∀ σ, linOwn γ.lin σ }>> e @ ↑sp.spN
      <<{ linOwn γ.lin σ | (sl : GoSlice), RET #sl;
        sl ↦*□ (σ (lin.keyName (W64 (i.key : Int)))).getD [] ∗ P }>>) ⊢
    linkInv (G := hG.goose_globalGS) γ γk -∗ lin (Gg := hG.goose_globalGS) (swRK γk) i Φ -∗
    WP e {{ r, ∃ (sl : GoSlice) (o : BStr), ⌜r = #sl⌝ ∗ sl ↦*□ o.1 ∗ P ∗ Φ o }} := by
  iintro Hwp #Hinv Hlin
  iunfold atomic_wp at Hwp
  iapply Hwp
  iauintro
  unfold atomic_acc
  iunfold linkInv at Hinv
  iinv Hinv with Hi Hclose
  · exact linkN_spN
  iunfold linkI at Hi
  icases Hi with ⟨%p, %ps, Hp, Hσ, Hrel⟩
  imod Hp
  imod Hσ
  imod Hrel with %Hrel
  ihave Hσ : linOwn γ.lin (lin.stateOf ps) $$ [Hσ]
  · iunfold linOwn; iexists ps; iframe Hσ; ipureintro; rfl
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists (⟨lin.stateOf ps, ⟨⟩⟩ : (Tele.cons fun _ : (kv GoString GoString).State => Tele.nil).Arg)
  dsimp only [Tele.lam, Tele.app, Tele.bind, BI.tforall_cons, BI.tforall_nil, BIBase.wandM]
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hmask with -
    imod Hclose $$ [Hσ Hp] with -
    · inext
      iunfold linkI
      iunfold linOwn at Hσ
      icases Hσ with ⟨%ps', Hσ, %Hps'⟩
      iexists p, ps'
      iframe Hσ Hp
      ipureintro; rw [← Hps']; exact Hrel
    imodintro
    iframe
  · iintro Hσ'
    imod Hmask with -
    iunfold lin at Hlin
    rw [show ((swRK (G := hG.goose_globalGS) γk).Eop) = swEop from rfl, swEop_diff]
    imod Hlin with ⟨%st, Hst, Hc⟩
    ihave Hst : ghostVar γk (1 : Qp).half (kpair st) $$ [Hst]
    · simp only [swRK, swR, sysK]; iexact Hst
    icombine Hst Hp gives %Hg
    have Hpe := Hg.2
    subst Hpe
    simp only [swRK, swR, swB_get i hget]
    imod Hc $$ [Hst] with HΦ
    · unfold sysK; iexact Hst
    imod Hclose $$ [Hσ' Hp] with -
    · inext
      iunfold linkI
      iunfold linOwn at Hσ'
      icases Hσ' with ⟨%ps', Hσ', %Hps'⟩
      iexists _, ps'
      iframe Hσ' Hp
      ipureintro; rw [← Hps']; exact Hrel
    imodintro
    iintro %sl ⟨#Hsl, HP⟩
    iexists sl, st i.key
    rw [← relP_get st _ i Hrel]
    iframe HP HΦ
    isplitr
    · ipureintro; rfl
    unfold Option.getD
    iexact Hsl

end au

end cnode

end Perennial.github_com.imdea_software.swiftpaxos
