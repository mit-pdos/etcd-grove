/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/replica/Ghost.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension.
-/
/-
The ghost laws at the mask `⊤`, restated with the fancy update of the program logic (the one
`WP` eliminates): `VsrGhost`'s statements elaborate their fancy updates through
`GooseGlobalGS.gooseInvGS` (a local instance there), which is the same update up to unfolding
but not one the proof mode's `ElimModal` instances match. Each is the frozen law, by `exact`.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Wire.Basic

@[expose] public section

noncomputable section

namespace VsrReplica

open Perennial Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode VsrModel VsrGhost Net


theorem sysN_top : (↑sysN : CoPset) ⊆ ⊤ := CoPset.subseteq_top
theorem regN_top : (↑VsrGhost.regN : CoPset) ⊆ ⊤ := CoPset.subseteq_top

/-- `sysN` and `VsrGhost.regN` are disjoint. -/
theorem sys_reg_disj : (↑sysN : CoPset) ∩ ↑VsrGhost.regN = (∅ : CoPset) := by
  have h : (↑sysN : CoPset) ## ↑VsrGhost.regN :=
    ndot_ne_disjoint (ndot nroot "vsr") (x := "sys") (y := "reg") (by decide)
  exact LawfulSet.disjoint_intersection.mp h

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

theorem fact_plain' (γ : Names) (m : Msg) :
    sysInv γ -∗ fact γ (.msg m) -∗ (|={⊤}=> ⌜PlainMsg m⌝ : IProp GF) :=
  VsrGhost.fact_plain γ ⊤ sysN_top m

/-- What a writer needs of a valid message it sends (with its numbers bounded, from its Go
`uint64`s): plain strings and a short line (`VsrWire.line_bound`). -/
theorem fact_send' (γ : Names) (m : Msg) (hb : MsgBound m) :
    sysInv γ -∗ fact γ (.msg m) -∗
      (|={⊤}=> ⌜PlainMsg m ∧ (VsrWire.line m).length < 2 ^ 60⌝ : IProp GF) := by
  iintro #Hs #Hf
  ihave Hl : ([∗list] f ∈ [Fact.msg m], fact γ f) $$ [Hf]
  · iapply (BI.BigSepL.bigSepL_singleton (PROP := IProp GF)).2; iexact Hf
  iapply VsrGhost.ghost_pure γ ⊤ sysN_top [Fact.msg m] _ ?_ $$ Hs Hl
  intro s hs hf
  have hm : MsgValid s m := hf (.msg m) (by simp)
  exact ⟨msgValid_plain s hs m hm, VsrWire.line_bound s hs m hm hb⟩

theorem ghost_pure' (γ : Names) (fs : List Fact) (φ : Prop)
    (H : ∀ s, VsrModel.Inv s → (∀ f ∈ fs, Holds s f) → φ) :
    sysInv γ -∗ ([∗list] f ∈ fs, fact γ f) -∗ (|={⊤}=> ⌜φ⌝ : IProp GF) :=
  VsrGhost.ghost_pure γ ⊤ sysN_top fs φ H

/-- `ghost_pure_rep` with the system's size known (the fact `.size n` added to the facts held:
`H` gets `s.n = n`). -/
theorem ghost_pure_rep' (γ : Names) (n r : Nat) (p : Rep) (fs : List Fact) (φ : Prop)
    (H : ∀ s, VsrModel.Inv s → s.n = n → s.reps r = p → (∀ f ∈ fs, Holds s f) → φ) :
    fact γ (.size n) -∗ sysInv γ -∗ repOwn γ r p -∗ ([∗list] f ∈ fs, fact γ f) -∗
      (|={⊤}=> (repOwn γ r p ∗ ⌜φ⌝) : IProp GF) := by
  iintro #Hn #Hs Hr #Hfs
  ihave Hl : ([∗list] f ∈ (Fact.size n :: fs), fact γ f) $$ [Hn Hfs]
  · iapply (BI.BigSepL.bigSepL_cons (PROP := IProp GF)).2; iframe Hn Hfs
  iapply VsrGhost.ghost_pure_rep γ ⊤ sysN_top r p (Fact.size n :: fs) φ ?_ $$ Hs Hr Hl
  intro s hs hrp hf
  exact H s hs (hf (.size n) (by simp)) hrp (fun f hf' => hf f (by simp [hf']))

/-- Two size facts agree. -/
theorem size_agree' (γ : Names) (n m : Nat) :
    sysInv γ -∗ fact γ (.size n) -∗ fact γ (.size m) -∗ (|={⊤}=> ⌜n = m⌝ : IProp GF) := by
  iintro #Hs #Hn #Hm
  ihave Hl : ([∗list] f ∈ [Fact.size n, Fact.size m], fact γ f) $$ [Hn Hm]
  · iapply (BI.BigSepL.bigSepL_cons (PROP := IProp GF)).2; iframe Hn
    iapply (BI.BigSepL.bigSepL_singleton (PROP := IProp GF)).2; iexact Hm
  iapply VsrGhost.ghost_pure γ ⊤ sysN_top [Fact.size n, Fact.size m] _ ?_ $$ Hs Hl
  intro s _ hf
  have h1 : s.n = n := hf (.size n) (by simp)
  have h2 : s.n = m := hf (.size m) (by simp)
  omega

theorem ghost_fact' (γ : Names) (n r : Nat) (p : Rep) (fs : List Fact) (f : Fact)
    (H : ∀ s, VsrModel.Inv s → s.n = n → s.reps r = p → (∀ f' ∈ fs, Holds s f') → Holds s f) :
    fact γ (.size n) -∗ sysInv γ -∗ repOwn γ r p -∗ ([∗list] f' ∈ fs, fact γ f') -∗
      (|={⊤}=> (repOwn γ r p ∗ fact γ f) : IProp GF) :=
  VsrGhost.ghost_fact γ ⊤ sysN_top n r p fs f H

theorem ghost_step' (γ : Names) (n r : Nat) (p p' : Rep) (fs fs' : List Fact) (st : Sys → Sys)
    (H : ∀ s, VsrModel.Inv s → s.n = n → s.reps r = p → (∀ f ∈ fs, Holds s f) →
      VsrModel.Inv (st s) ∧ Le s (st s) ∧ (st s).reps r = p' ∧
      (∀ x, x ≠ r → (st s).reps x = s.reps x) ∧ (st s).lin = s.lin ∧ (st s).reg = s.reg ∧
      (∀ f ∈ fs', Holds (st s) f)) :
    fact γ (.size n) -∗ sysInv γ -∗ repOwn γ r p -∗ ([∗list] f ∈ fs, fact γ f) -∗
      (|={⊤}=> (repOwn γ r p' ∗ [∗list] f ∈ fs', fact γ f) : IProp GF) :=
  VsrGhost.ghost_step γ ⊤ sysN_top n r p p' fs fs' st H


theorem ghost_lin' (γ : Names) (l mine : List Entry) (k : Nat) (e : Entry)
    (hk : mine.length + 1 = k) (hml : mine <+: l) (he : l[k - 1]? = some e) (v w : Nat) :
    £ 1 -∗ sysInv γ -∗ regInv γ -∗ fact γ (.committedBy w l) -∗ fact γ (.linPrefix mine) -∗
      (|={⊤}=> (fact γ (.linPrefix (l.take k)) ∗
        fact γ (.msg (.reply e.req e.cid v (outOf (l.take k) (k - 1))))) : IProp GF) :=
  VsrGhost.ghost_lin γ ⊤ sysN_top regN_top CoPset.subseteq_top sys_reg_disj
    l mine k e hk hml he v w

end laws

end VsrReplica
