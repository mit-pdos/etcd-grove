/-
The vocabulary of the lab's `bufio` specs (dsverify-lab `harness/lean/Harness/Proof/bufio/Defs.lean`,
`ReadFull.lean`, copied: definitions only) and the statements of the lab's `bufio` theorems the
swiftpaxos proof uses (`*.labSpec`, hypotheses here: notes/dsv-swiftpaxos.md, "Hypotheses"; the
main tree's own `bufio` vocabulary is `EtcdGrove.bufio`, a different one). The definitions are over
the real `bufio` structs (the main tree's translation, whose fields are the lab's); errors with a
message are `models_lab.errAny` (`Net/`'s, the lab's `models_lab.errAny`).

**Port changes** (`readerOk`, `readsOk`): only reads into a non-empty buffer are specified (the
real `bufio` and `io.ReadAtLeast` never pass an empty one; `Net/`'s `Read` spec does not fix the
count of an empty read, as dsv-bufio's `conn_readerOk`); and the underlying reader's `Read` gives its stream state one
step later (`▷ I (R ++ data)`; the lab's gave it now). Over `Net/` a connection's read gives
`recvTokL`, whose protocol fact is a step later (`GooseLang/Ext/Net/Proto.lean`, `read_au`), and
`recvTokL ⊢ ▷ recvTok` (`recvTokL_later`). The hypotheses over these (`*.labSpec`) stay true of the
real `bufio`/`io` code, which takes steps after each underlying `Read` (dsv-bufio's revised reader
law, `recvTokL_proto`, is the same idea).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Base
public import Net.Proof.models_lab.Errors
public import Proof.bufio.Own
public import Proof.bufio.NewWriter
public import Proof.bufio.NewWriterSize
public import Proof.bufio.Writer__Write
public import Proof.bufio.Writer__WriteByte
public import Proof.bufio.Writer__Flush

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
      ⌜0 < bs.length⌝ -∗ I R -∗ b ↦* bs -∗
      ▷ (∀ (data : List w8) (err : GoInterface), ⌜data.length ≤ bs.length⌝ -∗
          b ↦* (data ++ bs.drop data.length) -∗ ▷ I (R ++ data) -∗ errOrNil err -∗
          Φ (PairV #(W64 data.length) #err)) -∗
      WP (App (Val #(methods e.ty go!"Read" e.v)) (Val #b)) {{ Φ }})

/-- The underlying `io.Writer` `wr`: dsv-bufio's `io.writerOk` (`Proof/io/WriterOk.lean`) at some
error evidence `Ew`, with the lab's (stronger) `prefixClosed Q` (persistent). -/
def writerOk (wr : GoInterface) (J : List w8 → IProp GF) (Q : List w8 → IProp GF) :
    IProp GF :=
  iprop(∃ (e : GoInterfaceOk) (Ew : GoInterface → IProp GF),
    ⌜wr = interface.ok e ∧ e.ty ≠ go.GoType.PointerType bufio.Writer.ty⌝ ∗
    prefixClosed Q ∗ EtcdGrove.io.writerOk e J Q Ew)

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

/-- The `*bufio.Writer` `bw` over `wr` (with `J`, `Q`) has sent `sent` and buffers `pend`; its
sticky error is `err`: dsv-bufio's `ownBufWriter` at some error evidence and buffer size. -/
def ownWriter (bw : Loc) (wr : GoInterface) (J Q : List w8 → IProp GF)
    (sent pend : List w8) (err : GoInterface) : IProp GF :=
  iprop(∃ (e : GoInterfaceOk) (Ew : GoInterface → IProp GF) (sz : Nat), ⌜wr = interface.ok e⌝ ∗
    EtcdGrove.bufio.ownBufWriter bw e J Q Ew sz sent pend err)

/-- The lab's `prefixClosed` gives `io`'s. -/
theorem prefixClosed_io (Q : List w8 → IProp GF) :
    prefixClosed Q ⊢ EtcdGrove.io.prefixClosed Q := by
  unfold prefixClosed EtcdGrove.io.prefixClosed
  iintro #H !> %x %y #HQ
  iapply H $$ HQ

theorem writerOk_prefixClosed (wr : GoInterface) (J Q : List w8 → IProp GF) :
    writerOk wr J Q ⊢ prefixClosed Q := by
  unfold writerOk
  iintro ⟨%e, %Ew, -, #H, -⟩
  iexact H

/-- The `Read` spec of the `io.Reader` `rd` over `I`: see the file header (persistent). -/
def readsOk (rd : GoInterface) (I : List w8 → IProp GF) : IProp GF :=
  iprop(∃ e : GoInterfaceOk, ⌜rd = interface.ok e⌝ ∗
    □ ∀ (b : GoSlice) (bs : List w8) (R : List w8) (Φ : val → IProp GF),
      ⌜0 < bs.length⌝ -∗ I R -∗ b ↦* bs -∗
      ▷ (∀ (data : List w8) (err : GoInterface), ⌜data.length ≤ bs.length⌝ -∗
          b ↦* (data ++ bs.drop data.length) -∗ ▷ I (R ++ data) -∗ errOrNil err -∗
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

/-- lab `Proof/client/BufioErr.lean` `bufio.wp_WriteByte_err` (proved there from `bufio`'s code; a hypothesis
here until that proof is ported onto the main tree's `bufio` lemmas). -/
abbrev Writer.WriteByte_err.labSpec : Prop :=
  ∀ (bw : Loc) (wr : GoInterface) (J Q : List w8 → IProp GF)
    (sent pend : List w8) (err : GoInterface) (c : w8) (_herr : err ≠ interface.nil),
  {{ ownWriter bw wr J Q sent pend err }}
      (App (Val (bw @!! go.GoType.PointerType bufio.Writer.ty @!! go!"WriteByte")) (Val #c))
    {{ RET #err; ownWriter bw wr J Q sent pend err }}

/-- lab `Proof/client/BufioErr.lean` `bufio.wp_Write_err` (proved there from `bufio`'s code; a hypothesis
here until that proof is ported onto the main tree's `bufio` lemmas). -/
abbrev Writer.Write_err.labSpec : Prop :=
  ∀ (bw : Loc) (wr : GoInterface) (J Q : List w8 → IProp GF)
    (sent pend : List w8) (err : GoInterface) (p : GoSlice) (dq : DFrac) (ps : List w8)
    (_herr : err ≠ interface.nil),
  {{ ownWriter bw wr J Q sent pend err ∗ p ↦*{dq} ps }}
      (App (Val (bw @!! go.GoType.PointerType bufio.Writer.ty @!! go!"Write")) (Val #p))
    {{ (nn : w64), RET (PairV #nn #err); p ↦*{dq} ps ∗ ownWriter bw wr J Q sent pend err }}

/-- lab `Proof/client/BufioErr.lean` `bufio.wp_ReadByte_wf` (proved there from `bufio`'s code; a hypothesis
here until that proof is ported onto the main tree's `bufio` lemmas). -/
abbrev Reader.ReadByte_wf.labSpec : Prop :=
  ∀ (br : Loc) (rd : GoInterface) (I : List w8 → IProp GF) (R : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ readerOk rd I ∗ ownReader br rd I R }}
      (App (Val (br @!! go.GoType.PointerType bufio.Reader.ty @!! go!"ReadByte")) (Val #()))
    {{ (c : w8) (err : GoInterface), RET (PairV #c #err);
        (⌜err = interface.nil⌝ ∗ ownReader br rd I (R ++ [c])) ∨
        (⌜err ≠ interface.nil ∧ errWf err⌝ ∗ models_lab.errAny err ∗ ownReader br rd I R) }}

end specs

/-! ### The writer's lab specs, from dsv-bufio's -/

section writerProofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [bufio.Assumptions] [io.Assumptions]

theorem NewWriter.labProof : NewWriter.labSpec (GF := GF) := by
  intro wr J Q W
  iintro %Φ ⟨#Hpkg, #Hwr, HJ, #HQ⟩ HΦ
  iunfold writerOk at Hwr
  icases Hwr with ⟨%e, %Ew, %He, -, #Hio⟩
  obtain ⟨rfl, hty⟩ := He
  wp_apply (EtcdGrove.bufio.NewWriter.wp_proof EtcdGrove.bufio.NewWriterSize.wp_proof)
    e J Q Ew W $$ [HJ] as %bw Hown
  · iframe Hpkg Hio HJ HQ; ipureintro; exact hty
  iapply HΦ
  unfold ownWriter
  iexists e, Ew, 4096
  iframe Hown; ipureintro; rfl

theorem Writer.Flush.labProof : Writer.Flush.labSpec (GF := GF) := by
  intro bw wr J Q sent pend err
  iintro %Φ ⟨-, -, Hown⟩ HΦ
  iunfold ownWriter at Hown
  icases Hown with ⟨%e, %Ew, %sz, %He, Hown⟩
  wp_apply EtcdGrove.bufio.Writer.Flush.wp_proof bw e J Q Ew sz sent pend err $$ [Hown]
    as %e' ⟨%k, %Hk, Hown⟩
  · iexact Hown
  iapply HΦ
  iexists k
  isplitr
  · ipureintro; exact Hk
  unfold ownWriter
  iexists e, Ew, sz
  iframe Hown; ipureintro; exact He

theorem Writer.WriteByte.labProof : Writer.WriteByte.labSpec (GF := GF) := by
  intro bw wr J Q sent pend err c
  iintro %Φ ⟨-, -, Hown, #HQ⟩ HΦ
  iunfold ownWriter at Hown
  icases Hown with ⟨%e, %Ew, %sz, %He, Hown⟩
  wp_apply (EtcdGrove.bufio.Writer.WriteByte.wp_proof EtcdGrove.bufio.Writer.Flush.wp_proof)
    bw e J Q Ew sz sent pend err c $$ [Hown] as %e' ⟨%sent', %pend', %Hk, Hown⟩
  · iframe Hown; iintro %_; iexact HQ
  iapply HΦ
  iexists sent', pend'
  isplitr
  · ipureintro
    obtain ⟨h1, h2, h3, h4, -⟩ := Hk
    exact ⟨h1, h2, h3, fun h => (h4 h).1⟩
  unfold ownWriter
  iexists e, Ew, sz
  iframe Hown; ipureintro; exact He

theorem Writer.Write.labProof : Writer.Write.labSpec (GF := GF) := by
  intro bw wr J Q sent pend err p dq ps
  iintro %Φ ⟨-, -, Hown, #HQ, Hp⟩ HΦ
  iunfold ownWriter at Hown
  icases Hown with ⟨%e, %Ew, %sz, %He, Hown⟩
  wp_apply (EtcdGrove.bufio.Writer.Write.wp_proof EtcdGrove.bufio.Writer.Flush.wp_proof)
    bw e J Q Ew sz sent pend err p dq ps $$ [Hown Hp]
    as %nn %e' ⟨%k, %sent', %pend', %Hk, Hp, Hown⟩
  · iframe Hown Hp; iintro %_; iexact HQ
  iapply HΦ
  iexists k, sent', pend'
  isplitr
  · ipureintro
    obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := Hk
    exact ⟨h1, h2, h3, h4, h5, fun h => ⟨(h6 h).1, (h6 h).2.1⟩⟩
  iframe Hp
  unfold ownWriter
  iexists e, Ew, sz
  iframe Hown; ipureintro; exact He

theorem Writer.WriteByte_err.labProof : Writer.WriteByte_err.labSpec (GF := GF) := by
  intro bw wr J Q sent pend err c herr
  iintro %Φ Hown HΦ
  iunfold ownWriter at Hown
  icases Hown with ⟨%e, %Ew, %sz, %He, Hown⟩
  wp_apply (EtcdGrove.bufio.Writer.WriteByte.wp_proof EtcdGrove.bufio.Writer.Flush.wp_proof)
    bw e J Q Ew sz sent pend err c $$ [Hown] as %e' ⟨%sent', %pend', %Hk, Hown⟩
  · iframe Hown; iintro %h; exact absurd h herr
  obtain ⟨-, -, -, h4, -⟩ := Hk
  obtain ⟨rfl, rfl, rfl⟩ := h4 herr
  iapply HΦ
  unfold ownWriter
  iexists e, Ew, sz
  iframe Hown; ipureintro; exact He

theorem Writer.Write_err.labProof : Writer.Write_err.labSpec (GF := GF) := by
  intro bw wr J Q sent pend err p dq ps herr
  iintro %Φ ⟨Hown, Hp⟩ HΦ
  iunfold ownWriter at Hown
  icases Hown with ⟨%e, %Ew, %sz, %He, Hown⟩
  wp_apply (EtcdGrove.bufio.Writer.Write.wp_proof EtcdGrove.bufio.Writer.Flush.wp_proof)
    bw e J Q Ew sz sent pend err p dq ps $$ [Hown Hp]
    as %nn %e' ⟨%k, %sent', %pend', %Hk, Hp, Hown⟩
  · iframe Hown Hp; iintro %h; exact absurd h herr
  obtain ⟨-, -, -, -, -, h6, -⟩ := Hk
  obtain ⟨rfl, -, rfl, rfl⟩ := h6 herr
  iapply HΦ
  iframe Hp
  unfold ownWriter
  iexists e, Ew, sz
  iframe Hown; ipureintro; exact He

/-- Two writers at one location exclude each other. (The one place that unfolds dsv-bufio's
`ownBufWriter`: a law for dsv-bufio's `Own.lean`; notes/dsv-swiftpaxos.md, "For review".) -/
theorem ownWriter_excl_heap (bw : Loc) (wr wr' : GoInterface) (J Q J' Q' : List w8 → IProp GF)
    (s p s' p' : List w8) (e e' : GoInterface) :
    ownWriter bw wr J Q s p e ∗ ownWriter bw wr' J' Q' s' p' e' ⊢
      ∃ (b1 b2 : GoSlice) (n1 n2 : w64) (w1 w2 : GoInterfaceOk),
        bw ↦ bufio.Writer.mk e b1 n1 (interface.ok w1) ∗
        bw ↦ bufio.Writer.mk e' b2 n2 (interface.ok w2) := by
  unfold ownWriter EtcdGrove.bufio.ownBufWriter EtcdGrove.bufio.writerRep
  iintro ⟨⟨%i1, %E1, %z1, -, -, -, -, -, %b1, %n1, %r1, H1, -⟩,
    ⟨%i2, %E2, %z2, -, -, -, -, -, %b2, %n2, %r2, H2, -⟩⟩
  iexists b1, b2, n1, n2, i1, i2
  iframe H1 H2

end writerProofs

end bufio

end Perennial
