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
  `γΦ`, so the client that registered the entry recognizes it;
* **the read escrow** (S6, `rdsQ`; `g.rd`, a mono list): per read outside the log registered at the
  frontier of length `n0` (`KitRead.lean`), its persistent update `□ lin`, and the outputs it got at every
  command-ending frontier position `k ≥ n0` since (`rdEnt`), or the reader's token once it took one. Moving
  the frontier fires every registered read at the new state (`rds_step`: helping).

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

/-- The kit's ghost names: the model's state, the escrow's map, the clients' operation counters, the
operation ids the clients reserved (`idInv`), the read escrow's list (S6). -/
structure KG where
  st : GName
  esc : GName
  seq : GName
  ids : GName
  rd : GName

/-- A read escrow entry's names and data: the reader's token, its saved continuation, its input, the
frontier's length at its registration. -/
abbrev RdX := GName × GName × HIn × Nat

/-- The operation id a datum carries (its bytes 1 to 8, big-endian, `opID`'s): the client (the top byte)
and the client's count (the other 56 bits). A function of the datum, so two data with different ids
differ (the clients' freshness, `kit_register`). -/
def idOf (d : List w8) : Nat × Nat :=
  let x := ((d.drop 1).take 8).foldl (fun a b => a * 256 + uint.nat b) 0
  (x / 2 ^ 56, x % 2 ^ 56)

/-- Every put command of `es` has a value shorter than 256 bytes (an input's). -/
def putsShort (es : RLog) : Prop :=
  ∀ e ∈ es, e.kind = kCommand → isPut e.data → (putVal e.data).length < 256

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

theorem regShort_foldl : ∀ (es : RLog) (st : service.Reg), regShort st → putsShort es →
    regShort (es.foldl service.applyEnt st)
  | [], _, h, _ => h
  | e :: es, st, h, hp => by
    rw [List.foldl_cons]
    apply regShort_foldl es _ _ (fun x hx => hp x (List.mem_cons_of_mem _ hx))
    unfold service.applyEnt
    split
    · rename_i hc
      intro v hv; cases hv
      exact hp e List.mem_cons_self hc.1 hc.2
    · exact h

/-- The register after puts with short values is short. -/
theorem regShort_of_putsShort (es : RLog) (h : putsShort es) : regShort (service.regOf es) :=
  regShort_foldl es none (fun _ hv => by cases hv) h

theorem putsShort_prefix {a b : RLog} (h : a <+: b) (hb : putsShort b) : putsShort a :=
  fun e he => hb e (h.subset he)

theorem putsShort_fire (es ns : RLog) (e : Entry) (i : HIn) (h : putsShort es)
    (hns : ∀ x ∈ ns, x.kind ≠ kCommand) (hd : datumOf i e.data) : putsShort (es ++ ns ++ [e]) := by
  intro x hx hk hp
  simp only [List.mem_append, List.mem_singleton] at hx
  rcases hx with (hx | hx) | rfl
  · exact h x hx hk hp
  · exact absurd hk (hns x hx)
  · rw [hd.2 (hd.1.1 hp)]; exact i.2.2

theorem firedOut_eq (es ns : RLog) (e : Entry) (i : HIn) (hns : ∀ x ∈ ns, x.kind ≠ kCommand) :
    firedOut i (es ++ ns ++ [e]) = (regB.step i (regOf es)).2 := by
  unfold firedOut
  rw [show (es ++ ns ++ [e]).dropLast = es ++ ns by simp, service.regOf_noncmds es ns hns]

/-- A frontier position strictly inside the step `es ++ ns ++ [e]` ends with a non-command. -/
theorem not_lastCmd_mid (es ns : RLog) (e : Entry) (hns : ∀ x ∈ ns, x.kind ≠ kCommand) (k : Nat)
    (h1 : es.length < k) (h2 : k < (es ++ ns ++ [e]).length) :
    ¬ service.lastCmd ((es ++ ns ++ [e]).take k) := by
  intro hl
  simp only [List.length_append, List.length_cons, List.length_nil] at h2
  have hk : (es ++ ns ++ [e]).take k = es ++ ns.take (k - es.length) := by
    rw [List.append_assoc, List.take_append, List.take_of_length_le (by omega),
      List.take_append_of_le_length (by omega)]
  rw [hk] at hl
  have hne : ns.take (k - es.length) ≠ [] := by
    intro h; rw [List.take_eq_nil_iff] at h
    rcases h with h | rfl
    · omega
    · simp at h2; omega
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1 (mt List.getLast?_eq_none_iff.1 hne)
  have hx' : (es ++ ns.take (k - es.length)).getLast? = some x := by
    rw [List.getLast?_append, hx]; rfl
  exact hns x (List.mem_of_mem_take (List.mem_of_getLast? hx)) (hl x hx')

theorem take_step (es ns : RLog) (e : Entry) (k : Nat) (h : k ≤ es.length) :
    (es ++ ns ++ [e]).take k = es.take k := by
  rw [List.append_assoc, List.take_append_of_le_length h]

end pure

/-! ## The clients' state -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The reservation of the operation id `p`** (client, count): exclusive; the client takes it from
`idInv` (`id_reserve`) and the escrow keeps it with the entry of a datum of that id, so a datum is
registered at most once (`kit_register`). -/
def idTok (g : KG) (p : Nat × Nat) : IProp GF := ghostMapElem (K := Nat × Nat) (V := Unit) g.ids p (DFrac.own 1) ()

/-- **The escrow's entry of the datum `d`**, at the frontier `es` (see the file header). -/
def escEnt (γ : GNames) (g : KG) (es : RLog) (d : List w8) (γt γΦ : GName) (i : HIn) : IProp GF :=
  iprop(∃ Φ : HOut → IProp GF, savedPredOwn γΦ .discard Φ ∗
    ((⌜¬ cmdIn d es⌝ ∗ slotUpd (Gg := hG.goose_globalGS) (regR g.st) i Φ) ∨
     (∃ es1 : RLog, ⌜es1 <+: es ∧ ∃ e, es1.getLast? = some e ∧ e.kind = kCommand ∧ e.data = d⌝ ∗
        cIdxs γ es1 ∗ (Φ (firedOut i es1) ∨ token γt))))

/-- **A read's escrow entry** `x = (γt, γΦ, i, n0)` at the frontier `es` (S6): the saved continuation
`Φ`, the read's persistent update, the positions `ks` it was fired at (every command-ending position of
`es` from `n0` on, none past `es`), and the outputs there, or the reader's token (it took one). -/
def rdEnt (g : KG) (es : RLog) (x : RdX) : IProp GF :=
  iprop(∃ (Φ : HOut → IProp GF) (ks : List Nat), savedPredOwn x.2.1 .discard Φ ∗
    □ lin (Gg := hG.goose_globalGS) (regR g.st) x.2.2.1 Φ ∗
    ⌜x.2.2.1.1.1 = false ∧ (∀ k ∈ ks, k ≤ es.length) ∧
      ∀ k, x.2.2.2 ≤ k → k ≤ es.length → service.lastCmd (es.take k) → k ∈ ks⌝ ∗
    (token x.1 ∨ [∗list] k ∈ ks, Φ (regB.step x.2.2.1 (regOf (es.take k))).2))

/-- **The read escrow** at the frontier `es` (S6). -/
def rdsQ (g : KG) (es : RLog) : IProp GF :=
  iprop(∃ RS : List RdX, monoListAuthOwn g.rd 1 RS ∗ [∗list] x ∈ RS, rdEnt g es x)

/-- **The clients' state at the frontier `es`** (see the file header). -/
def kitQ (γ : GNames) (g : KG) (es : RLog) : IProp GF :=
  iprop(∃ (M : GMap (List w8) Nat) (E : GMap (List w8) (GName × GName × HIn)),
    Inv γ ∗ opsAuth γ M ∗ ghostMapAuth g.esc 1 E ∗
    ghostVar (A := service.Reg) g.st (1 : Qp).half (regOf es) ∗
    ⌜(∀ d n, M.lookup d = some n → ∃ x, E.lookup d = some x) ∧ putsShort es⌝ ∗
    ([∗map] d ↦ x ∈ E, ⌜datumOf x.2.2 d⌝ ∗ idTok g (idOf d) ∗ escEnt γ g es d x.1 x.2.1 x.2.2) ∗
    rdsQ g es)

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

/-- **A read fires at the model's state** (its update persistent; the state unchanged). -/
theorem read_fire (st : GName) (i : HIn) (Φ : HOut → IProp GF) (s : service.Reg) (hw : i.1.1 = false) :
    □ lin (Gg := hG.goose_globalGS) (regR st) i Φ ∗ ghostVar (A := service.Reg) st (1 : Qp).half s ⊢
      |={⊤ \ kitE}=> ghostVar (A := service.Reg) st (1 : Qp).half s ∗ Φ (regB.step i s).2 := by
  iintro ⟨#Hlin, Hst⟩
  ihave HF := lin_linF (Gg := hG.goose_globalGS) (regR st) i Φ $$ Hlin
  unfold linF
  simp only [regR]
  imod HF with ⟨%st', Hs, Hc⟩
  ihave %Hag := ghostVar_agree st _ _ _ _ $$ Hs Hst
  subst Hag
  have hst : (regB.step i st').1 = st' := regB_reads_stay i st' (by simp only [regB]; exact hw)
  rw [hst]
  imod Hc $$ Hs with HΦ
  imodintro
  iframe Hst HΦ

/-- **A read's entry follows a frontier step** (fired at the new state, `read_fire`). -/
theorem rdEnt_step (g : KG) (es ns : RLog) (e : Entry) (hns : ∀ x ∈ ns, x.kind ≠ kCommand)
    (x : RdX) :
    ghostVar (A := service.Reg) g.st (1 : Qp).half (regOf (es ++ ns ++ [e])) ∗ rdEnt g es x ⊢
      |={⊤ \ kitE}=> ghostVar (A := service.Reg) g.st (1 : Qp).half (regOf (es ++ ns ++ [e])) ∗
        rdEnt g (es ++ ns ++ [e]) x := by
  iintro ⟨Hst, Hx⟩
  unfold rdEnt
  icases Hx with ⟨%Φ, %ks, #HΦ, #Hlin, %hp, Hr⟩
  obtain ⟨hw, hks, hall⟩ := hp
  have hp' : x.2.2.1.1.1 = false ∧ (∀ k ∈ ks ++ [(es ++ ns ++ [e]).length], k ≤ (es ++ ns ++ [e]).length) ∧
      ∀ k, x.2.2.2 ≤ k → k ≤ (es ++ ns ++ [e]).length →
        service.lastCmd ((es ++ ns ++ [e]).take k) → k ∈ ks ++ [(es ++ ns ++ [e]).length] := by
    refine ⟨hw, ?_, ?_⟩
    · intro k hk
      simp only [List.mem_append, List.mem_singleton] at hk
      rcases hk with hk | rfl
      · have := hks k hk; simp only [List.length_append, List.length_cons, List.length_nil]; omega
      · exact Nat.le_refl _
    · intro k h0 hle hl
      simp only [List.mem_append, List.mem_singleton]
      by_cases hk : k ≤ es.length
      · left; rw [take_step es ns e k hk] at hl; exact hall k h0 hk hl
      · by_cases hk2 : k = (es ++ ns ++ [e]).length
        · right; exact hk2
        · exfalso; exact not_lastCmd_mid es ns e hns k (by omega) (by omega) hl
  icases Hr with (Ht | Hks)
  · imodintro
    iframe Hst
    iexists Φ, ks ++ [(es ++ ns ++ [e]).length]
    iframe HΦ Hlin
    isplitr
    · ipureintro; exact hp'
    ileft; iexact Ht
  · imod read_fire g.st x.2.2.1 Φ _ hw $$ [$Hlin $Hst] with ⟨Hst, HΦo⟩
    imodintro
    iframe Hst
    iexists Φ, ks ++ [(es ++ ns ++ [e]).length]
    iframe HΦ Hlin
    isplitr
    · ipureintro; exact hp'
    iright
    iapply BigSepL.bigSepL_snoc.2
    isplitl [Hks]
    · iapply BigSepL.bigSepL_mono ?_ $$ Hks
      intro j k hj
      rw [take_step es ns e k (hks k (List.mem_of_getElem? hj))]
    · rw [List.take_length]
      iexact HΦo

/-- **The read escrow follows a frontier step** (`rdEnt_step` for every entry). -/
theorem rds_step (g : KG) (es ns : RLog) (e : Entry) (hns : ∀ x ∈ ns, x.kind ≠ kCommand) :
    ∀ RS : List RdX,
    ghostVar (A := service.Reg) g.st (1 : Qp).half (regOf (es ++ ns ++ [e])) ∗
      ([∗list] x ∈ RS, rdEnt g es x) ⊢
      |={⊤ \ kitE}=> ghostVar (A := service.Reg) g.st (1 : Qp).half (regOf (es ++ ns ++ [e])) ∗
        [∗list] x ∈ RS, rdEnt g (es ++ ns ++ [e]) x
  | [] => by
    iintro ⟨Hst, -⟩
    imodintro
    iframe Hst
    iapply BigSepL.bigSepL_nil.2
    itrivial
  | x :: RS => by
    iintro ⟨Hst, Hl⟩
    icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Hx, Hl⟩
    imod rdEnt_step g es ns e hns x $$ [$Hst $Hx] with ⟨Hst, Hx⟩
    imod rds_step g es ns e hns RS $$ [$Hst $Hl] with ⟨Hst, Hl⟩
    imodintro
    iframe Hst
    iapply BigSepL.bigSepL_cons.2
    iframe Hx Hl

/-- **The kit's clients' law** (`linStep`, which the FSMs' context asks for). -/
theorem kitQ_linStep (γ : GNames) (g : KG) (fr : GName) :
    ⊢ service.linStep (GF := GF) γ (kitFC γ g fr) := by
  unfold service.linStep kitFC
  iintro !> %es %ns %e %h #Hc HQ
  obtain ⟨hns, he⟩ := h
  simp only
  unfold kitQ
  icases HQ with ⟨%M, %E, #Hinv, Hops, HE, Hst, %hME, Hents, HR⟩
  iunfold rdsQ at HR
  icases HR with ⟨%RS, HRa, HRs⟩
  obtain ⟨hME, hsh⟩ := hME
  have hk : (es ++ ns ++ [e])[(es ++ ns).length]? = some e := by simp
  ihave #He := service.cIdxs_lookup γ _ _ e hk $$ Hc
  imod cmd_committed_ops γ _ frN_gprotN M _ e $$ [$Hinv $Hops $He] with ⟨Hops, %hM⟩
  obtain ⟨n, hn, -⟩ := hM he
  obtain ⟨⟨γt, γΦ, i⟩, hx⟩ := hME _ _ hn
  imod not_cmdIn_es γ es ns e he $$ [$Hinv $Hc] with %hnot
  ihave ⟨⟨%hd, Hid, Hent⟩, Hrest⟩ := BI.BigSepM.bigSepM_lookup_acc_impl hx $$ Hents
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
    rw [← regOf_fire es ns e i hns he hd]
    imod rds_step g es ns e hns RS $$ [$Hst $HRs] with ⟨Hst, HRs⟩
    ihave HR : rdsQ g (es ++ ns ++ [e]) $$ [HRa HRs]
    · unfold rdsQ; iexists RS; iframe HRa HRs
    imod Hclose
    imodintro
    iexists M, E
    iframe Hinv Hops HE HR
    iframe Hst
    isplitr
    · ipureintro
      exact ⟨hME, putsShort_fire es ns e i hsh hns hd⟩
    iapply Hrest
    · imodintro
      iintro %d %x %_ %hne ⟨%hdx, Hidd, Hd⟩
      iframe %hdx Hidd
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
    · iframe %hd Hid
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

/-! ## The answer a fired operation gets -/

section pure2
variable [GooseExts]

/-- **The output of a fired operation is the FSM's answer** to its command (`respAt`, which `API.Apply`'s
reply carries): nothing found for a put, the register for a get. -/
theorem firedOut_respAt (i : HIn) (es : RLog) (e : Entry) (hl : es.getLast? = some e)
    (hd : datumOf i e.data) (hs : putsShort es) :
    (firedOut i es).1 =
      if i.1.1 then (false, []) else ((service.respAt es).found', (service.respAt es).value') := by
  unfold firedOut service.respAt
  rw [hl]
  simp only [regB, service.respOf]
  by_cases hp : i.1.1 = true
  · simp only [hp, ↓reduceIte]
    rw [bndO_of (by simp)]
  · have hpe : ¬ service.isPut e.data := fun h => hp (hd.1.1 h)
    simp only [hp, hpe, Bool.false_eq_true, ↓reduceIte, service.resOf]
    have hsh := regShort_of_putsShort _ (putsShort_prefix (List.dropLast_prefix es) hs)
    have hlen : (regOut (service.regOf es.dropLast)).2.length < 256 := by
      unfold regOut
      cases h : service.regOf es.dropLast with
      | none => simp
      | some v => exact hsh v h
    rw [bndO_of hlen]
    rfl

end pure2

/-! ## The clients' registration and claim -/

section client
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **Client `c`'s operation counter** at `m`: the ids `(c, s)` it reserved have `s < m` (exclusive;
the client's system keeps it). -/
def seqOwn (g : KG) (c m : Nat) : IProp GF := c ↪[g.seq] m

def idN : Namespace := nroot.@"hraftids"

/-- **The ids' invariant** (allocated at the deployment's start, `kit_start`, so the clients, which do
not know the drawn protocol, can reserve ids): every reserved id `(c, s)` has `s` below client `c`'s
counter. -/
def idInv (g : KG) : IProp GF :=
  inv idN iprop(∃ (S : GMap Nat Nat) (I : GMap (Nat × Nat) Unit), ghostMapAuth g.seq 1 S ∗
    ghostMapAuth g.ids 1 I ∗ ⌜∀ c s, I.lookup (c, s) = some () → ∃ m, S.lookup c = some m ∧ s < m⌝)

instance idInv_persistent (g : KG) : Persistent (idInv (GF := GF) g) := by
  unfold idInv; infer_instance

/-- **A registered operation's claim** on its datum `d` (input `i`, continuation `Φ`): the escrow's
entry (persistent), the saved continuation and the client's token, which `kit_claim` swaps for `Φ` of
the output once the frontier has passed the command. -/
def kitTicket (g : KG) (d : List w8) (i : HIn) (Φ : HOut → IProp GF) : IProp GF :=
  iprop(∃ γt γΦ : GName, d ↪[g.esc]□ (γt, γΦ, i) ∗ savedPredOwn γΦ .discard Φ ∗ token γt)

/-- The clients' state's ghost state before the draw: the escrow's map (empty), the model's half and
the read escrow's list (empty). -/
def kitPre (g : KG) : IProp GF :=
  iprop(ghostMapAuth (K := List w8) (V := GName × GName × HIn) g.esc 1 ∅ ∗
    ghostVar (A := service.Reg) g.st (1 : Qp).half none ∗ monoListAuthOwn (A := RdX) g.rd 1 [])

/-- **The kit's ghost state at the deployment's start**: `kitPre` (for the draw, `kitQ_init`), the
model's other half (for the far side's store), the ids' invariant and the clients' counters `S`. -/
theorem kit_start (S : GMap Nat Nat) :
    ⊢ |={⊤}=> ∃ g : KG, kitPre (GF := GF) g ∗ ghostVar (A := service.Reg) g.st (1 : Qp).half none ∗
      idInv g ∗ [∗map] c ↦ m ∈ S, seqOwn g c m := by
  imod ghostVar_alloc (GF := GF) (none : service.Reg) with ⟨%γs, Hs⟩
  imod ghost_map_alloc_empty (GF := GF) (K := List w8) (V := GName × GName × HIn) with ⟨%γe, HE⟩
  imod ghost_map_alloc (GF := GF) S with ⟨%γq, HS, Hfr⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat × Nat) (V := Unit) with ⟨%γi, HI⟩
  imod mono_list_own_alloc (GF := GF) (A := RdX) [] with ⟨%γr, Hrd, -⟩
  icases (ghostVar_split_half (GF := GF) γs 1 (none : service.Reg)).1 $$ Hs with ⟨Hs1, Hs2⟩
  imod inv_alloc idN ⊤ iprop(∃ (S' : GMap Nat Nat) (I : GMap (Nat × Nat) Unit),
      ghostMapAuth (GF := GF) γq 1 S' ∗ ghostMapAuth γi 1 I ∗
      ⌜∀ c s, I.lookup (c, s) = some () → ∃ m, S'.lookup c = some m ∧ s < m⌝) $$ [HS HI] with #Hinv
  · inext
    iexists S, ∅
    iframe HS HI
    ipureintro
    intro c s h; cases h
  imodintro
  iexists ⟨γs, γe, γq, γi, γr⟩
  iframe Hs2
  isplitl [HE Hs1 Hrd]
  · iunfold kitPre; iframe HE Hs1 Hrd
  isplitr [Hfr]
  · unfold idInv; iexact Hinv
  unfold seqOwn
  iexact Hfr

/-- **The clients' state at the draw** (the empty frontier), from the drawn protocol's invariant and its
commands' authority. -/
theorem kitQ_init (γ : GNames) (g : KG) :
    Inv (GF := GF) γ ∗ opsAuth γ ∅ ∗ kitPre g ⊢ kitQ γ g [] := by
  iintro ⟨#Hinv, Hops, Hpre⟩
  iunfold kitPre at Hpre
  icases Hpre with ⟨HE, Hs1, Hrd⟩
  unfold kitQ
  iexists ∅, ∅
  iframe Hinv Hops HE
  isplitl [Hs1]
  · have h0 : service.regOf ([] : RLog) = none := rfl
    rw [h0]
    iexact Hs1
  isplitr
  · ipureintro
    refine ⟨?_, ?_⟩
    · intro d n h; cases h
    · intro e he; cases he
  isplitr [Hrd]
  · iapply BI.BigSepM.bigSepM_empty.2
    itrivial
  unfold rdsQ
  iexists []
  iframe Hrd
  iapply BigSepL.bigSepL_nil.2
  itrivial

/-- **The frontier's invariant at the draw**: the empty frontier (its ghost list `fr` allocated empty at
the start), the clients' state at it. -/
theorem frInv_init (γ : GNames) (g : KG) (fr : GName) :
    Inv (GF := GF) γ ∗ opsAuth γ ∅ ∗ kitPre g ∗ monoListAuthOwn (A := Entry) fr 1 [] ⊢
      |={⊤}=> service.frInv γ (kitFC γ g fr) := by
  iintro ⟨#Hinv, Hops, Hpre, Hfr⟩
  ihave HQ := kitQ_init γ g $$ [$Hinv $Hops $Hpre]
  unfold service.frInv
  dsimp only [kitFC]
  imod inv_alloc service.frN ⊤ iprop(∃ es : RLog, monoListAuthOwn (A := Entry) fr 1 es ∗
      service.cIdxs γ es ∗ ⌜service.lastCmd es⌝ ∗ service.frDur γ es ∗ kitQ γ g es) $$ [Hfr HQ] with #H
  · inext
    iexists []
    iframe Hfr HQ
    isplitr
    · unfold service.cIdxs
      iapply BigSepL.bigSepL_nil.2
      itrivial
    isplitr
    · ipureintro
      intro e he; cases he
    unfold service.frDur; ileft; ipureintro; rfl
  imodintro
  iexact H

/-- **Client `c` reserves the id `(c, m)`** (its counter at `m`, moved past it). -/
theorem id_reserve (g : KG) (c m : Nat) :
    idInv (GF := GF) g ∗ seqOwn g c m ⊢ |={⊤}=> seqOwn g c (m + 1) ∗ idTok g (c, m) := by
  iintro ⟨#Hi, Hseq⟩
  unfold idInv
  iinv Hi with ⟨%S, %I, >HS, >HI, >%h⟩ Hclose
  unfold seqOwn
  ihave %hS := ghost_map_lookup $$ HS Hseq
  have hI : I.lookup (c, m) = none := by
    cases hx : I.lookup (c, m) with
    | none => rfl
    | some u =>
      obtain ⟨m', hm', hlt⟩ := h c m (by cases u; exact hx)
      rw [hS] at hm'; cases hm'
      omega
  imod ghost_map_insert (c, m) () hI $$ HI with ⟨HI, Hel⟩
  imod ghost_map_update (m + 1) $$ HS Hseq with ⟨HS, Hseq⟩
  imod Hclose $$ [HS HI] with -
  · inext
    iexists S.insert c (m + 1), I.insert (c, m) ()
    iframe HS HI
    ipureintro
    intro c' s' h'
    by_cases hcs : (c', s') = (c, m)
    · cases hcs
      exact ⟨m + 1, GMap.lookup_insert_eq _ _ _, by omega⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hcs)] at h'
      obtain ⟨m', hm', hlt⟩ := h c' s' h'
      by_cases hc : c' = c
      · subst hc
        rw [hS] at hm'; cases hm'
        exact ⟨m + 1, GMap.lookup_insert_eq _ _ _, by omega⟩
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hc)]
        exact ⟨m', hm', hlt⟩
  imodintro
  iframe Hseq
  unfold idTok
  iexact Hel

/-- The datum of an unregistered operation is no command of a committed prefix. -/
theorem not_cmdIn_ops (γ : GNames) (es : RLog) (M : GMap (List w8) Nat) (d : List w8)
    (hM : M.lookup d = none) :
    Inv (GF := GF) γ ∗ opsAuth γ M ∗ cIdxs γ es ⊢ |={⊤ \ ↑service.frN}=> opsAuth γ M ∗ ⌜¬ cmdIn d es⌝ := by
  iintro ⟨#Hinv, Hops, #Hc⟩
  by_cases h : cmdIn d es
  · obtain ⟨x, hx, hk, hd⟩ := h
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
    ihave #Hx := service.cIdxs_lookup γ es j x hj $$ Hc
    imod cmd_committed_ops γ _ frN_gprotN M _ x $$ [$Hinv $Hops $Hx] with ⟨Hops, %hM'⟩
    obtain ⟨n, hn, -⟩ := hM' hk
    rw [hd, hM] at hn
    cases hn
  · imodintro; iframe Hops; ipureintro; exact h

/-- **An operation is registered** on input `i` (its datum `d`, whose id the client reserved,
`id_reserve`), giving the update `slotUpd` of `i` with the continuation `Φ` to the escrow: the
command's token `opTok` (for `API.Apply`'s deposit) and the claim. (On the server's thread: the
client's deposit, `ClientDeps.lean`.) -/
theorem kit_register (γ : GNames) (g : KG) (fr : GName) (d : List w8) (i : HIn)
    (Φ : HOut → IProp GF) (hd : datumOf i d) :
    service.frInv γ (kitFC γ g fr) ∗ £ 1 ∗ idTok g (idOf d) ∗
      slotUpd (Gg := hG.goose_globalGS) (regR g.st) i Φ ⊢
      |={⊤}=> ∃ n, opTok γ d n ∗ kitTicket g d i Φ := by
  iintro ⟨#Hfr, Hlc, Hid, Hupd⟩
  unfold service.frInv
  iinv Hfr with ⟨%es, >Hauth, >#Hc, >%Hlast, >#Hfd, HQ⟩ Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑service.frN) $$ Hlc HQ with HQ
  simp only [kitFC]
  unfold kitQ
  icases HQ with ⟨%M, %E, #Hinv, Hops, HE, Hst, %hpure, Hents, HR⟩
  obtain ⟨hME, hsh⟩ := hpure
  ihave %hE : ⌜E.lookup d = none⌝ $$ [Hents Hid]
  · cases hx : E.lookup d with
    | none => ipureintro; rfl
    | some x =>
      ihave ⟨⟨-, Hid2, -⟩, -⟩ := (BI.BigSepM.bigSepM_lookup_acc hx).1 $$ Hents
      unfold idTok
      ihave %hv := ghostMapElem_valid_2 _ _ _ _ _ _ $$ Hid Hid2
      exfalso
      have := DFrac.valid_op_own hv.1
      simp at this
  have hM : M.lookup d = none := by
    cases hx : M.lookup d with
    | none => rfl
    | some n =>
      obtain ⟨x, hx'⟩ := hME d n hx
      rw [hE] at hx'
      cases hx'
  imod not_cmdIn_ops γ es M d hM $$ [$Hinv $Hops $Hc] with ⟨Hops, %hnot⟩
  imod CLb_get γ _ frN_gprotN $$ Hinv with ⟨%L, #HL⟩
  imod opTok_new γ M d L hM $$ [$Hops $HL] with ⟨Hops, Htok⟩
  imod token_alloc (GF := GF) with ⟨%γt, Ht⟩
  imod saved_pred_alloc (GF := GF) Φ DFrac.discard DFrac.valid_discard with ⟨%γΦ, #HΦ⟩
  imod ghost_map_insert_persist d (γt, γΦ, i) hE $$ HE with ⟨HE, #Hel⟩
  imod Hclose $$ [Hauth Hops HE Hst Hents Hupd Hid HR] with -
  · inext
    iexists es
    iframe Hauth Hc Hfd
    isplitr
    · ipureintro; exact Hlast
    iexists M.insert d L.length, E.insert d (γt, γΦ, i)
    iframe Hinv Hops HE Hst HR
    isplitr
    · ipureintro
      refine ⟨?_, hsh⟩
      intro d' n' h'
      by_cases hdd : d' = d
      · subst hdd; exact ⟨_, GMap.lookup_insert_eq _ _ _⟩
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hdd)] at h' ⊢
        exact hME d' n' h'
    iapply (BI.BigSepM.bigSepM_insert hE).2
    iframe Hents
    isplitr
    · ipureintro; exact hd
    iframe Hid
    unfold escEnt
    iexists Φ
    iframe HΦ
    ileft
    iframe Hupd
    ipureintro; exact hnot
  imodintro
  iexists L.length
  iframe Htok
  unfold kitTicket
  iexists γt, γΦ
  iframe Hel HΦ Ht

theorem kit_internal_eq_rewrite {P Q : IProp GF} : ⊢ (P ≡ Q) -∗ Q -∗ P := by
  iintro #H HQ
  ihave #Hiff := internalEq_iff P Q $$ H
  icases Hiff with ⟨-, H2⟩
  iapply H2
  iexact HQ

/-- The last entry of a committed prefix of length `k` is its entry at `k`. -/
theorem cIdxs_last (γ : GNames) (es : RLog) (k : Nat) (e : Entry) (hlen : es.length = k) :
    cIdxs (GF := GF) γ es ∗ CIdx γ k e ⊢ ⌜es.getLast? = some e⌝ := by
  iintro ⟨#Hc, #He⟩
  ihave %hpos : ⌜1 ≤ k⌝ $$ [He]
  · iunfold CIdx at He
    icases He with ⟨%h, -⟩
    ipureintro; exact h
  obtain ⟨e', he'⟩ : ∃ e', es[k - 1]? = some e' := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  ihave #He' := service.cIdxs_lookup γ es (k - 1) e' he' $$ Hc
  rw [show k - 1 + 1 = k by omega]
  ihave %Heq := service.cidx_agree γ k e e' $$ [He He']
  · iframe #
  ipureintro
  subst Heq
  rw [List.getLast?_eq_getElem?, hlen]
  exact he'

/-- **A client claims its operation's output** once `API.Apply` answered done: the command `e` (its datum
`d`) committed at `k`, the committed prefix `es'` ending there, which the frontier has passed. The
escrow's entry fired at `es'` (a command first passes the frontier at one index, `cmd_unique`), so the
claim gets `Φ` of its output (`firedOut`, the FSM's answer: `firedOut_respAt`). -/
theorem kit_claim (γ : GNames) (g : KG) (fr : GName) (d : List w8) (i : HIn) (Φ : HOut → IProp GF)
    (k : Nat) (e : Entry) (es' : RLog) (he : e.kind = kCommand ∧ e.data = d ∧ es'.length = k) :
    service.frInv γ (kitFC γ g fr) ∗ £ 1 ∗ £ 1 ∗ kitTicket g d i Φ ∗ CIdx γ k e ∗ cIdxs γ es' ∗
      service.frLb (kitFC γ g fr) es' ⊢
      |={⊤}=> Φ (firedOut i es') ∗ ⌜datumOf i d ∧ es'.getLast? = some e ∧ putsShort es'⌝ := by
  iintro ⟨#Hfr, Hlc1, Hlc2, Htk, #He, #Hc', #Hlb⟩
  obtain ⟨hk, hed, hlen⟩ := he
  unfold kitTicket
  icases Htk with ⟨%γt, %γΦ, #Hel, #HΦ, Ht⟩
  ihave %hlast' := cIdxs_last γ es' k e hlen $$ [Hc' He]
  · iframe #
  unfold service.frInv
  iinv Hfr with ⟨%es, >Hauth, >#Hc, >%Hlast, >#Hfd, HQ⟩ Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑service.frN) $$ Hlc1 HQ with HQ
  unfold service.frLb
  simp only [kitFC]
  ihave %Hpre := mono_list_auth_lb_valid fr 1 es es' $$ Hauth Hlb
  obtain ⟨-, hpre'⟩ := Hpre
  unfold kitQ
  icases HQ with ⟨%M, %E, #Hinv, Hops, HE, Hst, %hpure, Hents, HR⟩
  obtain ⟨hME, hsh⟩ := hpure
  ihave %hx := ghost_map_lookup $$ HE Hel
  icases (BI.BigSepM.bigSepM_lookup_acc hx).1 $$ Hents with ⟨⟨%hd, Hid, Hent⟩, Hback⟩
  unfold escEnt
  icases Hent with ⟨%Φ', #HΦ', Hent⟩
  icases Hent with (⟨%hnot, -⟩ | ⟨%es1, ⟨%hpre1, %e1, %hl1, %hk1, %hd1⟩, #Hc1, Hr⟩)
  · -- pending: the command of `d` is in the frontier, a contradiction
    exfalso
    apply hnot
    exact ⟨e, hpre'.subset (List.mem_of_getLast? hlast'), hk, hed⟩
  -- fired: at `es'`
  have hne1 : es1 ≠ [] := by intro h; subst h; simp at hl1
  have hl1' : es1[es1.length - 1]? = some e1 := by rw [← List.getLast?_eq_getElem?]; exact hl1
  ihave #He1 := service.cIdxs_lookup γ es1 (es1.length - 1) e1 hl1' $$ Hc1
  have hpos1 : 0 < es1.length := by
    cases es1 with
    | nil => exact absurd rfl hne1
    | cons _ _ => simp
  rw [show es1.length - 1 + 1 = es1.length by omega]
  imod cmd_unique γ _ frN_gprotN es1.length k e1 e $$ [$Hinv $He1 $He] with %Hu
  have hkk : es1.length = k := Hu hk1 hk (by rw [hd1, hed])
  have hes : es1 = es' := by
    rw [List.prefix_iff_eq_take] at hpre1 hpre'
    rw [hpre1, hpre', hkk, hlen]
  subst hes
  icases Hr with (HΦo | Ht')
  · imod Hclose $$ [Hauth Hops HE Hst Hback Ht Hid HR] with -
    · inext
      iexists es
      iframe Hauth Hc Hfd
      isplitr
      · ipureintro; exact Hlast
      iexists M, E
      iframe Hinv Hops HE Hst HR
      isplitr
      · ipureintro; exact ⟨hME, hsh⟩
      iapply Hback
      isplitr
      · ipureintro; exact hd
      iframe Hid
      iexists Φ'
      iframe HΦ'
      iright
      iexists es1
      iframe Hc1
      isplitr
      · ipureintro; exact ⟨hpre1, e1, hl1, hk1, hd1⟩
      iright
      iexact Ht
    ihave Heq := saved_pred_agree γΦ _ _ Φ Φ' (firedOut i es1) $$ HΦ HΦ'
    ihave HΦ1 : (▷ Φ (firedOut i es1) : IProp GF) $$ [Heq HΦo]
    · inext
      iapply kit_internal_eq_rewrite $$ Heq
      iexact HΦo
    imod lc_fupd_elim_later $$ Hlc2 HΦ1 with HΦ1
    imodintro
    iframe HΦ1
    ipureintro
    exact ⟨hed ▸ hd, hlast', putsShort_prefix hpre1 hsh⟩
  · iexfalso
    iapply token_exclusive $$ Ht Ht'

end client

end github_com.hashicorp.raft.examples.hraftnet
end Perennial
