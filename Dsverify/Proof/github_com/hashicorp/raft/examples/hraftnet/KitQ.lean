/-
# The clients' state at the linearization frontier (notes/dsv-hraft.md, S5)

The FSMs' frontier (`service/FsmDefs.lean`: `frInv`, the longest committed prefix any server's FSM has
applied) carries the clients' state `kitQ γ g es` at the frontier `es`, and moving it past a command
fires that command's operation (`linStep`, proved here: `kitQ_linStep`):

* the model's state, the clients' half of the ghost variable `g.st` whose other half is the far side's
  store's (`Kit.lean`, `regR g.st`), at the register after `es` (`regOf es`), whose value is an
  input's (shorter than 256 bytes);
* gprot's authority over the commands' data `opsAuth γ M` (E1: a client creates its command's token
  `opTok` from it) and gprot's invariant;
* **the escrow**, one entry per datum a client registered (`g.esc`, a ghost map from the datum to the
  entry's names and its operation's input): the operation's update (`slotUpd`, remote's: a put's
  `lin`, a get's `□ lin`) while the datum is no command of `es` (pending); once it is (fired), the
  committed prefix `es1` ending at that command and either the operation's continuation `Φ` of the
  output (`firedOut`) or the client's token `γt` (it took `Φ` out). `Φ` is named by a saved predicate
  `γΦ`, so the client that registered the entry recognizes it.

A command first moves past the frontier at one index only (gprot's `cmd_unique`), and its datum is
registered (`cmd_committed_ops`), so its entry is pending when the frontier moves past it: the update
fires there, with the register after the frontier, which is the FSM's answer (`respAt_step`).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.Kit
public import Dsverify.Proof.github_com.hashicorp.raft.gprot.Ops
public import Perennial.Ghost.SavedProp
public import Perennial.Ghost.Token

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.hashicorp.raft.examples.hraftnet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote
open github_com.hashicorp.raft github_com.hashicorp.raft.proto github_com.hashicorp.raft.gprot
open service (regOf cIdxs isPut putVal)

/-! ## Pure -/

section pure
variable [GooseExts]

/-- The kit's ghost names: the model's state, the escrow's map. -/
structure KG where
  st : GName
  esc : GName

/-- The datum `d` is the command of an operation on input `i`: a put iff `i` is, with `i`'s value. -/
def datumOf (i : HIn) (d : List w8) : Prop :=
  (isPut d ↔ i.1.1 = true) ∧ (i.1.1 = true → putVal d = i.1.2.2)

/-- `d` is the datum of a command of `es`. -/
def cmdIn (d : List w8) (es : RLog) : Prop := ∃ e ∈ es, e.kind = kCommand ∧ e.data = d

/-- The register holds an input's value, if any. -/
def regShort (st : service.Reg) : Prop := ∀ v, st = some v → v.length < 256

/-- The output of the operation on `i` whose command ends `es1`: the store's step from the register
before it. -/
def firedOut (i : HIn) (es1 : RLog) : HOut := (regB.step i (regOf es1.dropLast)).2

theorem cmdIn_append (d : List w8) (es ns : RLog) (e : Entry) (h : ¬ cmdIn d es)
    (hns : ∀ x ∈ ns, x.kind ≠ kCommand) (he : e.data ≠ d) : ¬ cmdIn d (es ++ ns ++ [e]) := by
  rintro ⟨x, hx, hk, hd⟩
  simp only [List.mem_append, List.mem_singleton] at hx
  rcases hx with (hx | hx) | rfl
  · exact h ⟨x, hx, hk, hd⟩
  · exact hns x hx hk
  · exact he hd

/-- The register after a command of input `i` (with its datum) is the store's. -/
theorem regOf_fire (es ns : RLog) (e : Entry) (i : HIn) (hns : ∀ x ∈ ns, x.kind ≠ kCommand)
    (he : e.kind = kCommand) (hd : datumOf i e.data) :
    regOf (es ++ ns ++ [e]) = (regB.step i (regOf es)).1 := by
  rw [service.regOf_step es ns e hns]
  unfold service.applyEnt regB
  simp only
  by_cases hp : i.1.1 = true
  · have hpe : isPut e.data := hd.1.2 hp
    rw [if_pos ⟨he, hpe⟩, if_pos hp, hd.2 hp]
  · have hpe : ¬ isPut e.data := fun h => hp (hd.1.1 h)
    rw [if_neg (fun h => hpe h.2), if_neg hp]

theorem regShort_fire (st : service.Reg) (i : HIn) (h : regShort st) :
    regShort (regB.step i st).1 := by
  unfold regB
  simp only
  split
  · intro v hv; cases hv; exact i.2.2
  · exact h

theorem firedOut_eq (es ns : RLog) (e : Entry) (i : HIn) (hns : ∀ x ∈ ns, x.kind ≠ kCommand) :
    firedOut i (es ++ ns ++ [e]) = (regB.step i (regOf es)).2 := by
  unfold firedOut
  rw [show (es ++ ns ++ [e]).dropLast = es ++ ns by simp, service.regOf_noncmds es ns hns]

end pure

/-! ## The clients' state -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The escrow's entry of the datum `d`**, at the frontier `es` (see the file header). -/
def escEnt (γ : GNames) (g : KG) (es : RLog) (d : List w8) (γt γΦ : GName) (i : HIn) : IProp GF :=
  iprop(∃ Φ : HOut → IProp GF, savedPredOwn γΦ .discard Φ ∗
    ((⌜¬ cmdIn d es⌝ ∗ slotUpd (Gg := hG.goose_globalGS) (regR g.st) i Φ) ∨
     (∃ es1 : RLog, ⌜es1 <+: es ∧ ∃ e, es1.getLast? = some e ∧ e.kind = kCommand ∧ e.data = d⌝ ∗
        cIdxs γ es1 ∗ (Φ (firedOut i es1) ∨ token γt))))

/-- **The clients' state at the frontier `es`** (see the file header). -/
def kitQ (γ : GNames) (g : KG) (es : RLog) : IProp GF :=
  iprop(∃ (M : GMap (List w8) Nat) (E : GMap (List w8) (GName × GName × HIn)),
    Inv γ ∗ opsAuth γ M ∗ ghostMapAuth g.esc 1 E ∗
    ghostVar (A := service.Reg) g.st (1 : Qp).half (regOf es) ∗
    ⌜(∀ d n, M.lookup d = some n → ∃ x, E.lookup d = some x) ∧ regShort (regOf es)⌝ ∗
    [∗map] d ↦ x ∈ E, ⌜datumOf x.2.2 d⌝ ∗ escEnt γ g es d x.1 x.2.1 x.2.2)

/-- The FSMs' context of the kit: the frontier `fr`, the clients' state. -/
def kitFC (γ : GNames) (g : KG) (fr : GName) : service.FCtx GF := ⟨fr, kitQ γ g⟩

end defs

/-! ## Moving the frontier fires the command's update -/

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem frN_gprotN : ↑gprotN ⊆ (⊤ \ ↑service.frN : CoPset) := by
  unfold service.frN gprotN; solve_ndisj

/-- The datum of the command after `es` and `ns` is no command of `es` (it is committed at one index
only). -/
theorem not_cmdIn_es (γ : GNames) (es ns : RLog) (e : Entry) (he : e.kind = kCommand) :
    Inv (GF := GF) γ ∗ cIdxs γ (es ++ ns ++ [e]) ⊢ |={⊤ \ ↑service.frN}=> ⌜¬ cmdIn e.data es⌝ := by
  iintro ⟨#Hinv, #Hc⟩
  by_cases h : cmdIn e.data es
  · obtain ⟨x, hx, hk, hd⟩ := h
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
    have hjl : j < es.length := (List.getElem?_eq_some_iff.1 hj).1
    have hj' : (es ++ ns ++ [e])[j]? = some x := by
      rw [List.append_assoc, List.getElem?_append_left hjl]
      exact hj
    have hk' : (es ++ ns ++ [e])[(es ++ ns).length]? = some e := by simp
    ihave #Hx := service.cIdxs_lookup γ _ j x hj' $$ Hc
    ihave #He := service.cIdxs_lookup γ _ _ e hk' $$ Hc
    imod cmd_unique γ _ frN_gprotN _ _ x e $$ [$Hinv $Hx $He] with %Hu
    have := Hu hk he hd
    simp at this; omega
  · imodintro; ipureintro; exact h

/-- An operation's update gives its one-shot form (a write's `lin`, a read's `□ lin`). -/
theorem slotUpd_linF (st : GName) (i : HIn) (Φ : HOut → IProp GF) :
    slotUpd (Gg := hG.goose_globalGS) (regR st) i Φ ⊢ linF (Gg := hG.goose_globalGS) (regR st) i Φ := by
  refine Entails.trans ?_ (lin_linF (Gg := hG.goose_globalGS) (regR st) i Φ)
  unfold slotUpd
  split
  · exact .rfl
  · exact intuitionistically_elim

/-- **The kit's clients' law** (`linStep`, which the FSMs' context asks for). -/
theorem kitQ_linStep (γ : GNames) (g : KG) (fr : GName) :
    ⊢ service.linStep (GF := GF) γ (kitFC γ g fr) := by
  unfold service.linStep kitFC
  iintro !> %es %ns %e %h #Hc HQ
  obtain ⟨hns, he⟩ := h
  simp only
  unfold kitQ
  icases HQ with ⟨%M, %E, #Hinv, Hops, HE, Hst, %hME, Hents⟩
  obtain ⟨hME, hsh⟩ := hME
  have hk : (es ++ ns ++ [e])[(es ++ ns).length]? = some e := by simp
  ihave #He := service.cIdxs_lookup γ _ _ e hk $$ Hc
  imod cmd_committed_ops γ _ frN_gprotN M _ e $$ [$Hinv $Hops $He] with ⟨Hops, %hM⟩
  obtain ⟨n, hn, -⟩ := hM he
  obtain ⟨⟨γt, γΦ, i⟩, hx⟩ := hME _ _ hn
  imod not_cmdIn_es γ es ns e he $$ [$Hinv $Hc] with %hnot
  ihave ⟨⟨%hd, Hent⟩, Hrest⟩ := BI.BigSepM.bigSepM_lookup_acc_impl hx $$ Hents
  unfold escEnt
  icases Hent with ⟨%Φ, #HΦ, Hent⟩
  icases Hent with (⟨%-, Hupd⟩ | ⟨%es1, ⟨%hpre, %e1, %hl, %hk1, %hd1⟩, -, -⟩)
  · -- pending: fire the update
    ihave HF := slotUpd_linF (GF := GF) g.st i Φ $$ Hupd
    unfold linF
    simp only [regR]
    have hmask : (⊤ \ kitE : CoPset) ⊆ ⊤ \ ↑service.frN := by unfold kitE; solve_ndisj
    imod fupd_mask_subseteq (PROP := IProp GF) hmask with Hclose
    imod HF with ⟨%st, Hs, Hc2⟩
    ihave %Hag := ghostVar_agree g.st _ _ _ _ $$ Hs Hst
    subst Hag
    imod ghostVar_update_halves (regB.step i (regOf es)).1 g.st _ _ $$ Hs Hst with ⟨Hs, Hst⟩
    imod Hc2 $$ Hs with HΦo
    imod Hclose
    imodintro
    iexists M, E
    iframe Hinv Hops HE
    rw [regOf_fire es ns e i hns he hd]
    iframe Hst
    isplitr
    · ipureintro
      exact ⟨hME, regShort_fire _ i hsh⟩
    iapply Hrest
    · imodintro
      iintro %d %x %_ %hne ⟨%hdx, Hd⟩
      iframe %hdx
      icases Hd with ⟨%Ψ, #HΨ, Hd⟩
      iexists Ψ
      iframe HΨ
      icases Hd with (⟨%hnd, Hu⟩ | ⟨%es2, ⟨%hp2, %hl2⟩, #Hc2, Hr⟩)
      · ileft
        iframe Hu
        ipureintro
        refine cmdIn_append d es ns e hnd hns ?_
        intro hed
        -- the datum of `e` is `e.data`'s entry: `d = e.data` contradicts `d ≠ e.data`
        exact hne hed.symm
      · iright
        iexists es2
        iframe Hc2 Hr
        ipureintro
        refine ⟨hp2.trans ?_, hl2⟩
        rw [List.append_assoc]
        exact List.prefix_append es (ns ++ [e])
    · iframe %hd
      iexists Φ
      iframe HΦ
      iright
      iexists es ++ ns ++ [e]
      iframe Hc
      isplitr
      · ipureintro
        exact ⟨List.prefix_refl _, e, by simp, he, rfl⟩
      ileft
      rw [firedOut_eq es ns e i hns]
      iexact HΦo
  · -- fired: its command is in `es`, a contradiction
    exfalso
    apply hnot
    obtain ⟨t, rfl⟩ := hpre
    exact ⟨e1, List.mem_append_left _ (List.mem_of_getLast? hl), hk1, hd1⟩

end proof

end github_com.hashicorp.raft.examples.hraftnet
end Perennial
