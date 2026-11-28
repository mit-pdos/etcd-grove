/-
The vocabulary of the hraft kit's state machine (`service.Store`, notes/dsv-hraft.md, S5): the
register, raft's FSM contract's predicates for it (`fsmOwn`, `respP`, `snapP`), and the
**linearization frontier**.

Adapted from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/examples/hr3/
ServerDefs.lean (241f27e): hr3's register (`regOf`, `respVal`, `storeInv`, `snapBytes`), its
committed-prefix facts (`cIdxs`) and `restore_forward`. What changed:

* the command format is the kit's (`service.go`): a put is `P`, an 8-byte operation id and the value
  (`putVal`); anything else, a command shorter than 9 bytes included, is a get;
* the snapshot's index is written with Perennial's `strconv.Itoa` (`fmtInt`), not the lab's `kitstd`;
* hr3 linearized its history offline (`LinPure`, over the committed log's prefixes in every
  response). remote's clients take online linearization points instead, so the FSMs keep a
  **frontier** (`frInv`): the longest committed prefix any server's FSM has applied, ending with a
  command. An FSM that applies the command right after the frontier moves it, and with it the
  clients' state (`FCtx.Q`) by the client's law `linStep` (where the clients fire the operation's
  atomic update: helping); an FSM behind the frontier applies the same entries (the committed log
  is one) and moves nothing. Every response (`respP`) and snapshot (`snapP`) says the frontier
  has passed its prefix (`frLb`): the operation it answers was linearized before the answer.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.service.Base
public import Dsverify.Proof.github_com.hashicorp.raft.iface.FSM
public import Perennial.Proof.internal.strconv.FormatBasics

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.hashicorp.raft.examples.hraftnet.service

open github_com.hashicorp.raft proto gprot

/-! ## The register, pure -/

section pure
variable [GooseExts]

/-- The register: absent, or a value. -/
abbrev Reg := Option (List w8)

/-- The command `d` is a put (`Store.Apply`'s test: at least `CmdHdr` (9) bytes, the first `P`). -/
def isPut (d : List w8) : Prop := 9 ≤ d.length ∧ d[0]? = some (W8 80)

instance isPut_dec (d : List w8) : Decidable (isPut d) := by unfold isPut; infer_instance

/-- A put's value: what follows its kind and its operation id. -/
def putVal (d : List w8) : List w8 := d.drop 9

/-- The register after the entry `e` (a put sets it; a get or an entry that is no command leaves it). -/
def applyEnt (st : Reg) (e : Entry) : Reg :=
  if e.kind = kCommand ∧ isPut e.data then some (putVal e.data) else st

/-- The register after the entries `es`. -/
def regOf (es : RLog) : Reg := es.foldl applyEnt none

/-- The FSM's `result` for the register `st`. -/
def resOf (st : Reg) : result := result.mk st.isSome (st.getD [])

/-- The FSM's answer to the command `e` applied after the entries `es`: nothing for a put, the
register for a get. -/
def respOf (es : RLog) (e : Entry) : result :=
  if isPut e.data then result.mk false [] else resOf (regOf es)

/-- The answer to the last entry of `es` (a command: `lastCmd`). -/
def respAt (es : RLog) : result :=
  match es.getLast? with
  | some e => respOf es.dropLast e
  | none => result.mk false []

/-- The prefix ends with a command (or is empty). -/
def lastCmd (es : RLog) : Prop := ∀ e, es.getLast? = some e → e.kind = kCommand

theorem regOf_noncmds (es ns : RLog) (h : ∀ e ∈ ns, e.kind ≠ kCommand) :
    regOf (es ++ ns) = regOf es := by
  have key : ∀ (ns : RLog) (st : Reg), (∀ e ∈ ns, e.kind ≠ kCommand) →
      ns.foldl applyEnt st = st := by
    intro ns
    induction ns with
    | nil => intros; rfl
    | cons e ns ih =>
      intro st h
      have he : e.kind ≠ kCommand := h e (by simp)
      simp only [List.foldl_cons]
      rw [show applyEnt st e = st by simp [applyEnt, he]]
      exact ih st (fun e' he' => h e' (by simp [he']))
  simp only [regOf, List.foldl_append]
  exact key ns _ h

/-- The register after a command `e` following `es` and non-commands `ns`. -/
theorem regOf_step (es ns : RLog) (e : Entry) (h : ∀ e ∈ ns, e.kind ≠ kCommand) :
    regOf (es ++ ns ++ [e]) = applyEnt (regOf es) e := by
  rw [show regOf (es ++ ns ++ [e]) = applyEnt (regOf (es ++ ns)) e by
    simp [regOf, List.foldl_append], regOf_noncmds es ns h]

/-- The answer to a command `e` following `es` and non-commands `ns`. -/
theorem respAt_step (es ns : RLog) (e : Entry) (h : ∀ e ∈ ns, e.kind ≠ kCommand) :
    respAt (es ++ ns ++ [e]) = respOf es e := by
  unfold respAt
  have h1 : (es ++ ns ++ [e]).getLast? = some e := by simp
  have h2 : (es ++ ns ++ [e]).dropLast = es ++ ns := by simp
  rw [h1]
  simp only
  rw [h2]
  unfold respOf
  rw [regOf_noncmds es ns h]

theorem lastCmd_snoc (es : RLog) (e : Entry) (h : e.kind = kCommand) : lastCmd (es ++ [e]) := by
  intro e' he'; simp at he'; subst he'; exact h

theorem lastCmd_nil : lastCmd [] := by intro e h; simp at h

/-! ## The snapshot's bytes, pure -/

/-- `encodeState`'s string of the register: `"0"`, or `"1"` and the value. -/
def encodeReg (st : Reg) : List w8 :=
  match st with
  | none => go!"0"
  | some v => go!"1" ++ v

/-- The bytes `snapshot.Persist` writes for the register after the commands `es`: the index of the
last command applied (`strconv.Itoa`), `|`, the encoded register. -/
def snapBytes (es : RLog) : List w8 :=
  _root_.Perennial.internal.strconv.fmtInt (W64 (es.length : Int)) (W64 10) ++ go!"|" ++ encodeReg (regOf es)

end pure

/-! ## The FSM's ghost context -/

/-- The linearization frontier's namespace. -/
def frN : Namespace := nroot.@"hraftfr"

/-- **The FSMs' ghost context** (one for the deployment): the frontier's mono list `fr` and the
clients' state `Q es` at the frontier `es` (the clients' choice: the model state, the operations'
updates). -/
structure FCtx (GF : BundledGFunctors) where
  fr : GName
  Q : RLog → IProp GF

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The committed log's entries `1..|es|` are `es` (index facts only). -/
def cIdxs (γ : GNames) (es : RLog) : IProp GF :=
  iprop([∗list] x ↦ e ∈ es, CIdx γ (x + 1) e)

instance cIdxs_persistent γ es : Persistent (cIdxs (GF := GF) γ es) := by
  unfold cIdxs; infer_instance

instance CIdx_timeless' γ k e : Timeless (CIdx (GF := GF) γ k e) := by
  unfold CIdx; infer_instance

instance cIdxs_timeless γ es : Timeless (cIdxs (GF := GF) γ es) := by
  unfold cIdxs; infer_instance

/-- The frontier has passed the prefix `es` (persistent). -/
def frLb (fc : FCtx GF) (es : RLog) : IProp GF := monoListLbOwn fc.fr es

instance frLb_persistent fc es : Persistent (frLb (GF := GF) fc es) := by
  unfold frLb; infer_instance

/-- **The frontier's invariant**: the frontier `es` is a committed prefix ending with a command,
with the clients' state at it. -/
def frInv (γ : GNames) (fc : FCtx GF) : IProp GF :=
  inv frN iprop(∃ es : RLog, monoListAuthOwn fc.fr 1 es ∗ cIdxs γ es ∗ ⌜lastCmd es⌝ ∗ fc.Q es)

instance frInv_persistent γ fc : Persistent (frInv (GF := GF) γ fc) := by
  unfold frInv; infer_instance

/-- **The clients' law**: moving the frontier past the command `e` (after `es` and the
non-commands `ns`, all committed) moves their state (persistent; the clients prove it: there
they fire the update of `e`'s operation). -/
def linStep (γ : GNames) (fc : FCtx GF) : IProp GF :=
  iprop(□ ∀ (es ns : RLog) (e : Entry), ⌜(∀ x ∈ ns, x.kind ≠ kCommand) ∧ e.kind = kCommand⌝ -∗
    cIdxs γ (es ++ ns ++ [e]) -∗ fc.Q es ={⊤ \ ↑frN}=∗ fc.Q (es ++ ns ++ [e]))

instance linStep_persistent γ fc : Persistent (linStep (GF := GF) γ fc) := by
  unfold linStep; infer_instance

/-- Server `i`'s durable prefix stays below `2^62` (persistent; the server's machine proves it
from gprot's receipt bound): the store's index is then an `int` (`Persist`'s `Itoa(int(index))`). -/
def durBound (γ : GNames) (i : SID) : IProp GF :=
  iprop(□ ∀ k : Nat, durLb γ i k ={⊤}=∗ ⌜k < 2 ^ 62⌝)

instance durBound_persistent γ i : Persistent (durBound (GF := GF) γ i) := by
  unfold durBound; infer_instance

/-- The FSM goroutine's state of a store whose applied-index ghost is `alb`: its half of the index
of the last command applied (`0`: none). -/
def fsmOwn (alb : GName) (k : Nat) : IProp GF := monoNatAuthOwn alb (1 : Qp).half k

/-- The store's mutex invariant: the register (`present`, `value`) is the one after the committed
prefix `es`, which ends with a command at `index` (below `2^62`), which the frontier has passed,
with the store's half of `alb` at `|es|`. -/
def storeInv (γ : GNames) (fc : FCtx GF) (alb : GName) (s : Loc) : IProp GF :=
  iprop(∃ es : RLog, cIdxs γ es ∗ frLb fc es ∗ monoNatAuthOwn alb (1 : Qp).half es.length ∗
    structFieldRef Store go!"present" s ↦ (regOf es).isSome ∗
    structFieldRef Store go!"value" s ↦ (regOf es).getD [] ∗
    structFieldRef Store go!"index" s ↦ W64 es.length ∗ ⌜es.length < 2 ^ 62 ∧ lastCmd es⌝)

/-- **Server `i`'s store `s`** (persistent): its mutex (the register, `storeInv`), the frontier
and the clients' law, the bound on `i`'s durable prefix. -/
def isStore (γ : GNames) (fc : FCtx GF) (alb : GName) (i : SID) (s : Loc) : IProp GF :=
  iprop(sync.isMutex (structFieldRef Store go!"mu" s) (storeInv γ fc alb s) ∗ frInv γ fc ∗
    linStep γ fc ∗ durBound γ i)

instance isStore_persistent γ fc alb i s : Persistent (isStore (GF := GF) γ fc alb i s) := by
  unfold isStore; infer_instance

/-- The store has applied the command at `k` or a later one (persistent). -/
def appliedLb (alb : GName) (k : Nat) : IProp GF := monoNatLbOwn alb k

instance appliedLb_persistent alb k : Persistent (appliedLb (GF := GF) alb k) := by
  unfold appliedLb; infer_instance

/-- **The meaning of the store's response `r` to the command at `k`** (persistent): the committed
prefix `es` of length `k` determines it (`respAt`), the frontier has passed it, and the store has
applied `k`. -/
def respP (γ : GNames) (fc : FCtx GF) (alb : GName) (k : Nat) (r : GoInterface) : IProp GF :=
  iprop(∃ es : RLog, ⌜es.length = k ∧ r = interface.mkOk result.ty #(respAt es)⌝ ∗
    cIdxs γ es ∗ frLb fc es ∗ appliedLb alb k)

instance respP_persistent γ fc alb k r : Persistent (respP (GF := GF) γ fc alb k r) := by
  unfold respP; infer_instance

/-- **The meaning of a snapshot's bytes** (the same at every server): `b` is the snapshot of the
committed log up to `s`: the register after the committed prefix `es` ending with a command at
`|es| ≤ s`, no command in `(|es|, s]`, and the frontier has passed `es`. -/
def snapP (γ : GNames) (fc : FCtx GF) (s : Nat) (b : List w8) : IProp GF :=
  iprop(∃ es : RLog, ⌜es.length ≤ s ∧ b = snapBytes es ∧ es.length < 2 ^ 62 ∧ lastCmd es⌝ ∗
    cIdxs γ es ∗ frLb fc es ∗ noCmdBetween γ es.length (s + 1))

instance snapP_persistent γ fc s b : Persistent (snapP (GF := GF) γ fc s b) := by
  unfold snapP; infer_instance

/-- **A snapshot value** `sn` (what `Store.Snapshot` returns) of the committed log up to `x`:
read-only fields holding the register after the committed prefix `es` and its last command's index,
whose bytes are a snapshot of `x`. -/
def snapVal (γ : GNames) (fc : FCtx GF) (sn : Loc) (x : Nat) : IProp GF :=
  iprop(∃ es : RLog, sn ↦□ snapshot.mk (W64 es.length) (regOf es).isSome ((regOf es).getD []) ∗
    snapP γ fc x (snapBytes es) ∗ ⌜es.length < 2 ^ 62⌝)

instance snapVal_persistent γ fc sn x : Persistent (snapVal (GF := GF) γ fc sn x) := by
  unfold snapVal; infer_instance

/-! ## Lemmas -/

/-- The two halves of a `mono_nat` authority make the whole. -/
theorem monoNat_halves (γm : GName) (n : Nat) :
    monoNatAuthOwn (GF := GF) γm (1 : Qp).half n ∗ monoNatAuthOwn γm (1 : Qp).half n ⊢
      monoNatAuthOwn γm 1 n := by
  have h := (monoNatAuthOwn_fractional (GF := GF) γm n).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  exact h.2

/-- The whole of a `mono_nat` authority splits in halves. -/
theorem monoNat_split (γm : GName) (n : Nat) :
    monoNatAuthOwn (GF := GF) γm 1 n ⊢
      monoNatAuthOwn γm (1 : Qp).half n ∗ monoNatAuthOwn γm (1 : Qp).half n := by
  have h := (monoNatAuthOwn_fractional (GF := GF) γm n).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  exact h.1

/-- `CIdx` agreement (gprot's `CIdx_agree`, which carries the receipt bound's instance, inlined). -/
theorem cidx_agree (γ : GNames) (k : Nat) (e1 e2 : Entry) :
    CIdx (GF := GF) γ k e1 ∗ CIdx γ k e2 ⊢ ⌜e1 = e2⌝ := by
  unfold CIdx
  iintro ⟨⟨_, #H1⟩, ⟨_, #H2⟩⟩
  iapply mono_list_idx_agree γ.C (k - 1) e1 e2 $$ H1 H2

/-- One index fact of a prefix. -/
theorem cIdxs_lookup (γ : GNames) (es : RLog) (j : Nat) (e : Entry) (h : es[j]? = some e) :
    cIdxs (GF := GF) γ es ⊢ CIdx γ (j + 1) e := by
  unfold cIdxs
  iintro #H
  iapply BigSepL.bigSepL_lookup h $$ H

theorem cIdxs_prefix_aux (γ : GNames) : ∀ (o : Nat) (a b : RLog), a.length ≤ b.length →
    ([∗list] x ↦ e ∈ a, CIdx (GF := GF) γ (o + x + 1) e) ∗
      ([∗list] x ↦ e ∈ b, CIdx γ (o + x + 1) e) ⊢ ⌜a <+: b⌝
  | _, [], _, _ => by iintro -; ipureintro; exact List.nil_prefix
  | _, _ :: _, [], h => by simp at h
  | o, x :: xs, y :: ys, h => by
    iintro ⟨Ha, Hb⟩
    icases BigSepL.bigSepL_cons.1 $$ Ha with ⟨Hx, Ha⟩
    icases BigSepL.bigSepL_cons.1 $$ Hb with ⟨Hy, Hb⟩
    ihave %Hxy := cidx_agree γ (o + 0 + 1) x y $$ [Hx Hy]
    · iframe
    ihave %Hp := cIdxs_prefix_aux γ (o + 1) xs ys (by simp at h; omega) $$ [Ha Hb]
    · isplitl [Ha]
      · iapply BigSepL.bigSepL_mono_of_forall ?_ $$ Ha
        intro j e
        rw [show o + (j + 1) + 1 = o + 1 + j + 1 by omega]
      · iapply BigSepL.bigSepL_mono_of_forall ?_ $$ Hb
        intro j e
        rw [show o + (j + 1) + 1 = o + 1 + j + 1 by omega]
    ipureintro
    subst Hxy
    exact (List.prefix_cons_inj x).2 Hp

/-- **Two committed prefixes agree**: the shorter is a prefix of the longer. -/
theorem cIdxs_prefix (γ : GNames) (a b : RLog) (h : a.length ≤ b.length) :
    cIdxs (GF := GF) γ a ∗ cIdxs γ b ⊢ ⌜a <+: b⌝ := by
  iintro ⟨Ha, Hb⟩
  unfold cIdxs
  iapply cIdxs_prefix_aux γ 0 a b h
  isplitl [Ha]
  · iapply BigSepL.bigSepL_mono_of_forall ?_ $$ Ha
    intro j e
    rw [Nat.zero_add]
  · iapply BigSepL.bigSepL_mono_of_forall ?_ $$ Hb
    intro j e
    rw [Nat.zero_add]

/-- Extending a committed prefix's index facts. -/
theorem cIdxs_append (γ : GNames) (es ns : RLog) :
    cIdxs (GF := GF) γ es ∗ ([∗list] j ↦ e ∈ ns, CIdx γ (es.length + 1 + j) e) ⊢
      cIdxs γ (es ++ ns) := by
  unfold cIdxs
  iintro ⟨H1, H2⟩
  iapply BigSepL.bigSepL_append.2
  iframe H1
  iapply BigSepL.bigSepL_mono_of_forall ?_ $$ H2
  intro j x
  rw [show es.length + 1 + j = j + es.length + 1 by omega]

/-- The committed entries strictly between `k0` and `k` (non-commands), as a list. -/
theorem noCmds_list (γ : GNames) : ∀ (m st : Nat),
    ([∗list] x ∈ List.range' st m, ∃ e' : Entry, CIdx (GF := GF) γ x e' ∗ ⌜e'.kind ≠ kCommand⌝) ⊢
      ∃ ns : RLog, ⌜ns.length = m ∧ ∀ e ∈ ns, e.kind ≠ kCommand⌝ ∗
        [∗list] j ↦ e ∈ ns, CIdx γ (st + j) e
  | 0, st => by
    iintro -
    iexists []
    isplitr
    · ipureintro; simp
    · iapply BigSepL.bigSepL_nil.2; itrivial
  | m + 1, st => by
    iintro H
    rw [List.range'_succ]
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨⟨%e0, H0, %h0⟩, H⟩
    icases noCmds_list γ m (st + 1) $$ H with ⟨%ns, %hns, Hns⟩
    iexists e0 :: ns
    isplitr
    · ipureintro
      refine ⟨by simp [hns.1], ?_⟩
      intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact h0
      · exact hns.2 e he
    iapply BigSepL.bigSepL_cons.2
    isplitl [H0]
    · rw [Nat.add_zero]; iexact H0
    iapply BigSepL.bigSepL_mono_of_forall ?_ $$ Hns
    intro j x
    rw [show st + 1 + j = st + (j + 1) by omega]

theorem noCmdBetween_list (γ : GNames) (k0 k : Nat) :
    noCmdBetween (GF := GF) γ k0 k ⊢
      ∃ ns : RLog, ⌜ns.length = k - (k0 + 1) ∧ ∀ e ∈ ns, e.kind ≠ kCommand⌝ ∗
        [∗list] j ↦ e ∈ ns, CIdx γ (k0 + 1 + j) e := by
  unfold noCmdBetween
  exact noCmds_list γ _ _

/-- **A command past the prefix `es0` is not in a stretch without commands**: if `es0` ends with a
command and no command lies in `(|es|, x]`, then `|es0| ≤ |es|` (when `|es0| ≤ x`). -/
theorem cmd_not_between (γ : GNames) (es0 : RLog) (n x : Nat) (hlast : lastCmd es0)
    (hx : es0.length ≤ x) :
    cIdxs (GF := GF) γ es0 ∗ noCmdBetween γ n (x + 1) ⊢ ⌜es0.length ≤ n⌝ := by
  iintro ⟨#Hpre, #Hnc⟩
  by_cases hle : es0.length ≤ n
  · ipureintro; exact hle
  obtain ⟨e0, he0⟩ : ∃ e0, es0.getLast? = some e0 := by
    cases h : es0.getLast? with
    | none => simp at h; subst h; simp at hle
    | some e0 => exact ⟨e0, rfl⟩
  have hk : es0[es0.length - 1]? = some e0 := by
    rw [List.getLast?_eq_getElem?] at he0; exact he0
  have hcmd := hlast e0 he0
  ihave #Hc0 := cIdxs_lookup γ es0 (es0.length - 1) e0 hk $$ Hpre
  unfold noCmdBetween
  have hmem : es0.length ∈ List.range' (n + 1) (x + 1 - (n + 1)) := by
    simp only [List.mem_range']; exact ⟨es0.length - (n + 1), by omega, by omega⟩
  icases BigSepL.bigSepL_mem hmem $$ Hnc with ⟨%e', #Hc', %hk'⟩
  rw [show es0.length - 1 + 1 = es0.length by omega]
  ihave %Heq := cidx_agree γ es0.length e0 e' $$ [Hc0 Hc']
  · iframe #
  subst Heq
  exact absurd hcmd hk'

/-- **The frontier passes an applied command** (an FSM's `Apply`): the FSM's prefix `es` (which the
frontier has passed) followed by the non-commands `ns` and the command `e`, all committed. If the
frontier is at `es` (it cannot be strictly between `es` and `e`: no command is), it moves to
`es ++ ns ++ [e]`, and the clients' state with it (`linStep`); else it is already past. -/
theorem frontier_apply (γ : GNames) (fc : FCtx GF) (es ns : RLog) (e : Entry)
    (hns : ∀ x ∈ ns, x.kind ≠ kCommand) (he : e.kind = kCommand) :
    £ 1 ∗ frInv γ fc ∗ linStep γ fc ∗ frLb fc es ∗ cIdxs γ (es ++ ns ++ [e]) ∗
      noCmdBetween γ es.length (es ++ ns ++ [e]).length ⊢ |={⊤}=> frLb fc (es ++ ns ++ [e]) := by
  iintro ⟨Hlc, #Hfr, #Hls, #Hlb, #Hpre, #Hnc⟩
  unfold frInv
  iinv Hfr with ⟨%esf, >Hauth, >#Hpf, >%Hlf, HQ⟩ Hclose
  unfold frLb
  ihave %Hle := mono_list_auth_lb_valid fc.fr 1 esf es $$ Hauth Hlb
  imod monoListAuthOwn_update esf (List.prefix_refl _) $$ Hauth with ⟨Hauth, #Hlbf⟩
  by_cases hge : (es ++ ns ++ [e]).length ≤ esf.length
  · ihave %Hp := cIdxs_prefix γ _ _ hge $$ [Hpre Hpf]
    · iframe #
    ihave #Hlb' := monoListLbOwn_le (es ++ ns ++ [e]) Hp $$ Hlbf
    imod Hclose $$ [Hauth HQ]
    · inext; iexists esf; iframe; iframe #; ipureintro; exact Hlf
    imodintro
    iexact Hlb'
  · have hk : (es ++ ns ++ [e]).length = es.length + ns.length + 1 := by simp; omega
    have hlef : es.length ≤ esf.length := Hle.2.length_le
    ihave %Hle2 := cmd_not_between γ esf es.length ((es ++ ns ++ [e]).length - 1) Hlf (by omega)
      $$ [Hpf Hnc]
    · iframe #
      rw [show (es ++ ns ++ [e]).length - 1 + 1 = (es ++ ns ++ [e]).length by omega]
      iexact Hnc
    have Heq : esf = es := (Hle.2.eq_of_length (by omega)).symm
    subst Heq
    have hh : (∀ x ∈ ns, x.kind ≠ kCommand) ∧ e.kind = kCommand := ⟨hns, he⟩
    imod lc_fupd_elim_later (E := ⊤ \ ↑frN) $$ Hlc HQ with HQ
    unfold linStep
    imod Hls $$ %esf %ns %e %hh Hpre HQ with HQ
    imod monoListAuthOwn_update (esf ++ ns ++ [e]) (by simp [List.append_assoc]) $$ Hauth
      with ⟨Hauth, #Hlb'⟩
    imod Hclose $$ [Hauth HQ]
    · inext; iexists esf ++ ns ++ [e]; iframe; iframe #; ipureintro; exact lastCmd_snoc _ e he
    imodintro
    iexact Hlb'

end defs

end github_com.hashicorp.raft.examples.hraftnet.service
end Perennial
