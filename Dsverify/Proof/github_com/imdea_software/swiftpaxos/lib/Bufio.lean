/-
The vocabulary of the lab's `bufio` specs (dsverify-lab `harness/lean/Harness/Proof/bufio/Defs.lean`,
`ReadFull.lean`, copied: definitions only) and the statements of the lab's `bufio` theorems the
swiftpaxos proof uses (`*.labSpec`, hypotheses here: notes/dsv-swiftpaxos.md, "Hypotheses"; the
main tree's own `bufio` vocabulary is `EtcdGrove.bufio`, a different one). The definitions are over
the real `bufio` structs (the main tree's translation, whose fields are the lab's); errors with a
message are `models_lab.errAny` (`Net/`'s, the lab's `net.rpc.errAny`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Base
public import Net.Proof.models_lab.Errors

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net

namespace bufio

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `Q` holds of every prefix of a stream it holds of (persistent). -/
def prefixClosed (Q : List w8 → IProp GF) : IProp GF :=
  iprop(□ (∀ (x y : List w8), Q (x ++ y) -∗ Q x))

/-- The prefix closure of a stream predicate: `W` is a prefix of a stream `ext` with
`□ Q ext` (`W` empty included). -/
def prefixClose (Q : List w8 → IProp GF) (W : List w8) : IProp GF :=
  iprop(⌜W = []⌝ ∨ ∃ ext : List w8, ⌜W <+: ext⌝ ∗ □ Q ext)

/-- A non-nil error of a pointer type holds a pointer (true of every error Go code makes; what
comparing it with an `errors.New` error, e.g. `err == io.EOF`, needs). -/
def errWf (err : GoInterface) : Prop :=
  ∀ e : GoInterfaceOk, err = interface.ok e → ∀ T : go.GoType, e.ty = go.GoType.PointerType T →
    ∃ l : Loc, e.v = #l

/-- An error result: `nil`, or an error with some message (and `errWf`). -/
def errOrNil (err : GoInterface) : IProp GF :=
  iprop(⌜err = interface.nil⌝ ∨ (models_lab.errAny err ∗ ⌜errWf err⌝))

/-- The underlying `io.Reader` `rd`: see the file header (persistent). -/
def readerOk (rd : GoInterface) (I : List w8 → IProp GF) : IProp GF :=
  iprop(∃ e : GoInterfaceOk,
    ⌜rd = interface.ok e ∧ e.ty ≠ go.GoType.PointerType bufio.Reader.ty⌝ ∗
    □ ∀ (b : GoSlice) (bs : List w8) (R : List w8) (Φ : val → IProp GF),
      I R -∗ b ↦* bs -∗
      ▷ (∀ (data : List w8) (err : GoInterface), ⌜data.length ≤ bs.length⌝ -∗
          b ↦* (data ++ bs.drop data.length) -∗ I (R ++ data) -∗ errOrNil err -∗
          Φ (PairV #(W64 data.length) #err)) -∗
      WP (App (Val #(methods e.ty go!"Read" e.v)) (Val #b)) {{ Φ }})

/-- The underlying `io.Writer` `wr`: see the file header (persistent). -/
def writerOk (wr : GoInterface) (J : List w8 → IProp GF) (Q : List w8 → IProp GF) :
    IProp GF :=
  iprop(∃ e : GoInterfaceOk,
    ⌜wr = interface.ok e ∧ e.ty ≠ go.GoType.PointerType bufio.Writer.ty⌝ ∗
    prefixClosed Q ∗
    □ ∀ (b : GoSlice) (dq : DFrac) (bs : List w8) (W : List w8) (Φ : val → IProp GF),
      J W -∗ □ Q (W ++ bs) -∗ b ↦*{dq} bs -∗
      ▷ (∀ (k : Nat) (err : GoInterface),
          ⌜k ≤ bs.length ∧ (err = interface.nil → k = bs.length)⌝ -∗
          b ↦*{dq} bs -∗ J (W ++ bs.take k) -∗ errOrNil err -∗
          Φ (PairV #(W64 k) #err)) -∗
      WP (App (Val #(methods e.ty go!"Write" e.v)) (Val #b)) {{ Φ }})

instance prefixClosed_persistent (Q : List w8 → IProp GF) :
    Persistent (prefixClosed (GF := GF) Q) := by
  unfold prefixClosed; infer_instance
instance errOrNil_persistent (err : GoInterface) : Persistent (errOrNil (GF := GF) err) := by
  unfold errOrNil; infer_instance
instance readerOk_persistent (rd : GoInterface) (I : List w8 → IProp GF) :
    Persistent (readerOk (GF := GF) rd I) := by
  unfold readerOk; infer_instance
instance writerOk_persistent (wr : GoInterface) (J Q : List w8 → IProp GF) :
    Persistent (writerOk (GF := GF) wr J Q) := by
  unfold writerOk; infer_instance

/-- The `*bufio.Reader` `br` over `rd` buffers `pend` and has the pending error `perr`: its
fields, its buffer `buf` (`len(buf) > 0`) holding `pend` at `[r, w)`. -/
def readerRep (br : Loc) (rd : GoInterface) (pend : List w8) (perr : GoInterface) :
    IProp GF :=
  iprop(∃ (buf : GoSlice) (r w lb lrs : w64) (pre post : List w8),
    br ↦ bufio.Reader.mk buf rd r w perr lb lrs ∗ buf ↦* (pre ++ pend ++ post) ∗
    ⌜sint.Z r = pre.length ∧ sint.Z w = pre.length + pend.length ∧
      0 < (pre ++ pend ++ post).length⌝ ∗ errOrNil perr)

/-- The `*bufio.Reader` `br` over `rd` (with `I`) has returned `R`: see the file header. -/
def ownReader (br : Loc) (rd : GoInterface) (I : List w8 → IProp GF) (R : List w8) :
    IProp GF :=
  iprop(∃ (pend : List w8) (perr : GoInterface), I (R ++ pend) ∗ readerRep br rd pend perr)

/-- The `*bufio.Writer` `bw` over `wr` buffers `pend` and has the error `err`: its fields, its
buffer `buf` (`len(buf) > 0`) holding `pend` at `[0, n)`. -/
def writerRep (bw : Loc) (wr : GoInterface) (pend : List w8) (err : GoInterface) : IProp GF :=
  iprop(∃ (buf : GoSlice) (n : w64) (rest : List w8),
    bw ↦ bufio.Writer.mk err buf n wr ∗ buf ↦* (pend ++ rest) ∗
    ⌜sint.Z n = pend.length ∧ 0 < (pend ++ rest).length⌝ ∗ errOrNil err)

/-- The `*bufio.Writer` `bw` over `wr` (with `J`, `Q`) has sent `sent` and buffers `pend`;
its sticky error is `err`: see the file header. -/
def ownWriter (bw : Loc) (wr : GoInterface) (J Q : List w8 → IProp GF)
    (sent pend : List w8) (err : GoInterface) : IProp GF :=
  iprop(J sent ∗ □ Q (sent ++ pend) ∗ writerRep bw wr pend err)

/-- The `Read` spec of the `io.Reader` `rd` over `I`: see the file header (persistent). -/
def readsOk (rd : GoInterface) (I : List w8 → IProp GF) : IProp GF :=
  iprop(∃ e : GoInterfaceOk, ⌜rd = interface.ok e⌝ ∗
    □ ∀ (b : GoSlice) (bs : List w8) (R : List w8) (Φ : val → IProp GF),
      I R -∗ b ↦* bs -∗
      ▷ (∀ (data : List w8) (err : GoInterface), ⌜data.length ≤ bs.length⌝ -∗
          b ↦* (data ++ bs.drop data.length) -∗ I (R ++ data) -∗ errOrNil err -∗
          Φ (PairV #(W64 data.length) #err)) -∗
      WP (App (Val #(methods e.ty go!"Read" e.v)) (Val #b)) {{ Φ }})

instance readsOk_persistent (rd : GoInterface) (I : List w8 → IProp GF) :
    Persistent (readsOk (GF := GF) rd I) := by
  unfold readsOk; infer_instance

theorem readerOk_readsOk (rd : GoInterface) (I : List w8 → IProp GF) :
    readerOk (GF := GF) rd I ⊢ readsOk rd I := by
  unfold readerOk readsOk
  iintro ⟨%e, %He, #H⟩
  iexists e
  isplitr
  · ipureintro; exact He.1
  iexact H

end defs

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [bufio.Assumptions] [io.Assumptions]

/-- lab `Harness/Proof/bufio/Reader.lean` `bufio.wp_NewReader`'s statement (a hypothesis here). -/
abbrev NewReader.labSpec : Prop :=
  ∀ (rd : GoInterface) (I : List w8 → IProp GF) (R : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ readerOk rd I ∗ I R }}
      (App (Val (@! bufio.NewReader)) (Val #rd))
    {{ (br : Loc), RET #br; ownReader br rd I R }}

/-- lab `Harness/Proof/bufio/Reader.lean` `bufio.wp_ReadByte`'s statement (a hypothesis here). -/
abbrev Reader.ReadByte.labSpec : Prop :=
  ∀ (br : Loc) (rd : GoInterface) (I : List w8 → IProp GF) (R : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ readerOk rd I ∗ ownReader br rd I R }}
      (App (Val (br @!! go.GoType.PointerType bufio.Reader.ty @!! go!"ReadByte")) (Val #()))
    {{ (c : w8) (err : GoInterface), RET (PairV #c #err);
        (⌜err = interface.nil⌝ ∗ ownReader br rd I (R ++ [c])) ∨
        (⌜err ≠ interface.nil⌝ ∗ models_lab.errAny err ∗ ownReader br rd I R) }}

/-- lab `Harness/Proof/bufio/Reader.lean` `bufio.wp_Read`'s statement (a hypothesis here). -/
abbrev Reader.Read.labSpec : Prop :=
  ∀ (br : Loc) (rd : GoInterface) (I : List w8 → IProp GF) (R : List w8)
    (p : GoSlice) (ps : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ readerOk rd I ∗ ownReader br rd I R ∗
        p ↦* ps }}
      (App (Val (br @!! go.GoType.PointerType bufio.Reader.ty @!! go!"Read")) (Val #p))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ∃ data : List w8, ⌜n = W64 data.length ∧ data.length ≤ ps.length⌝ ∗
        p ↦* (data ++ ps.drop data.length) ∗ ownReader br rd I (R ++ data) ∗ errOrNil err }}

/-- lab `Harness/Proof/bufio/Writer.lean` `bufio.wp_NewWriter`'s statement (a hypothesis here). -/
abbrev NewWriter.labSpec : Prop :=
  ∀ (wr : GoInterface) (J Q : List w8 → IProp GF) (W : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗ J W ∗ □ Q W }}
      (App (Val (@! bufio.NewWriter)) (Val #wr))
    {{ (bw : Loc), RET #bw; ownWriter bw wr J Q W [] interface.nil }}

/-- lab `Harness/Proof/bufio/Writer.lean` `bufio.wp_Flush`'s statement (a hypothesis here). -/
abbrev Writer.Flush.labSpec : Prop :=
  ∀ (bw : Loc) (wr : GoInterface) (J Q : List w8 → IProp GF)
    (sent pend : List w8) (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err }}
      (App (Val (bw @!! go.GoType.PointerType bufio.Writer.ty @!! go!"Flush")) (Val #()))
    {{ (e : GoInterface), RET #e; ∃ k : Nat,
        ⌜k ≤ pend.length ∧ (e = interface.nil → k = pend.length) ∧
          (err ≠ interface.nil → e = err ∧ k = 0)⌝ ∗
        ownWriter bw wr J Q (sent ++ pend.take k) (pend.drop k) e }}

/-- lab `Harness/Proof/bufio/Writer.lean` `bufio.wp_WriteByte`'s statement (a hypothesis here). -/
abbrev Writer.WriteByte.labSpec : Prop :=
  ∀ (bw : Loc) (wr : GoInterface) (J Q : List w8 → IProp GF)
    (sent pend : List w8) (err : GoInterface) (c : w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ [c]) }}
      (App (Val (bw @!! go.GoType.PointerType bufio.Writer.ty @!! go!"WriteByte")) (Val #c))
    {{ (e : GoInterface), RET #e; ∃ sent' pend' : List w8,
        ⌜sent <+: sent' ∧ (e = interface.nil → sent' ++ pend' = sent ++ pend ++ [c]) ∧
          (e ≠ interface.nil → sent' ++ pend' = sent ++ pend) ∧
          (err ≠ interface.nil → e = err)⌝ ∗
        ownWriter bw wr J Q sent' pend' e }}

/-- lab `Harness/Proof/bufio/Writer.lean` `bufio.wp_Write`'s statement (a hypothesis here). -/
abbrev Writer.Write.labSpec : Prop :=
  ∀ (bw : Loc) (wr : GoInterface) (J Q : List w8 → IProp GF)
    (sent pend : List w8) (err : GoInterface) (p : GoSlice) (dq : DFrac) (ps : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ writerOk wr J Q ∗
        ownWriter bw wr J Q sent pend err ∗ □ Q (sent ++ pend ++ ps) ∗ p ↦*{dq} ps }}
      (App (Val (bw @!! go.GoType.PointerType bufio.Writer.ty @!! go!"Write")) (Val #p))
    {{ (nn : w64) (e : GoInterface), RET (PairV #nn #e); ∃ (k : Nat) (sent' pend' : List w8),
        ⌜nn = W64 k ∧ k ≤ ps.length ∧ sent' ++ pend' = sent ++ pend ++ ps.take k ∧
          sent <+: sent' ∧ (e = interface.nil → k = ps.length) ∧
          (err ≠ interface.nil → e = err ∧ k = 0)⌝ ∗
        p ↦*{dq} ps ∗ ownWriter bw wr J Q sent' pend' e }}

/-- lab `Harness/Proof/bufio/ReadFull.lean` `bufio.wp_ReadAtLeast`'s statement (a hypothesis here). -/
abbrev io.ReadAtLeast.labSpec : Prop :=
  ∀ (rd : GoInterface) (I : List w8 → IProp GF) (R : List w8)
    (buf : GoSlice) (bs : List w8) (min : w64) (_hmin : sint.Z min ≤ bs.length),
  {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗ readsOk rd I ∗ I R ∗ buf ↦* bs }}
      (App (App (App (Val (@! io.ReadAtLeast)) (Val #rd)) (Val #buf)) (Val #min))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ∃ data : List w8, ⌜n = W64 data.length ∧ data.length ≤ bs.length ∧
          (err = interface.nil ↔ sint.Z min ≤ data.length)⌝ ∗
        buf ↦* (data ++ bs.drop data.length) ∗ I (R ++ data) ∗ errOrNil err }}

/-- lab `Harness/Proof/bufio/ReadFull.lean` `bufio.wp_ReadFull`'s statement (a hypothesis here). -/
abbrev io.ReadFull.labSpec : Prop :=
  ∀ (rd : GoInterface) (I : List w8 → IProp GF) (R : List w8)
    (buf : GoSlice) (bs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗ readsOk rd I ∗ I R ∗ buf ↦* bs }}
      (App (App (Val (@! io.ReadFull)) (Val #rd)) (Val #buf))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ∃ data : List w8, ⌜n = W64 data.length ∧ data.length ≤ bs.length ∧
          (err = interface.nil ↔ data.length = bs.length)⌝ ∗
        buf ↦* (data ++ bs.drop data.length) ∗ I (R ++ data) ∗ errOrNil err }}

end specs

end bufio

end Perennial
