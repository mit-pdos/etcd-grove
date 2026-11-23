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
public import Proof.bufio.ErrOrNil
public import Proof.bufio.Own
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.LibDeps
public import Proof.bufio.ReaderLaws
public import Perennial.Proof.errors.NewVar
public import Perennial.Proof.io.Link

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

/-- The errors with the evidence `E` are errors with some message (and `errWf`) (persistent). -/
def errsOk (E : List w8 → GoInterface → IProp GF) : IProp GF :=
  iprop(□ ∀ (r : List w8) (e : GoInterface), E r e -∗ models_lab.errAny e ∗ ⌜errWf e⌝)

/-- The underlying `io.Reader` `rd` over the stream state `I`: Perennial's `io.readerOk` for reads
into a non-empty buffer (a connection's, `net.conn_readerOk`), with errors that have a message;
not a `*bufio.Reader` (persistent). -/
def readerOk (rd : GoInterface) (I : List w8 → IProp GF) : IProp GF :=
  iprop(∃ (ri : GoInterfaceOk) (E : List w8 → GoInterface → IProp GF),
    ⌜rd = interface.ok ri ∧ ri.ty ≠ go.GoType.PointerType bufio.Reader.ty⌝ ∗ errsOk E ∗
    io.readerOk ri (fun _ m => 0 < m) I E)

/-- The underlying `io.Writer` `wr`: dsv-bufio's `io.streamWriterOk` (`Proof/io/StreamWriterOk.lean`) at some
error evidence `Ew`, with the lab's (stronger) `prefixClosed Q` (persistent). -/
def writerOk (wr : GoInterface) (J : List w8 → IProp GF) (Q : List w8 → IProp GF) :
    IProp GF :=
  iprop(∃ (e : GoInterfaceOk) (Ew : GoInterface → IProp GF),
    ⌜wr = interface.ok e ∧ e.ty ≠ go.GoType.PointerType bufio.Writer.ty⌝ ∗
    prefixClosed Q ∗ EtcdGrove.io.streamWriterOk e J Q Ew)

instance prefixClosed_persistent (Q : List w8 → IProp GF) :
    Persistent (prefixClosed (GF := GF) Q) := by
  unfold prefixClosed; infer_instance
instance errsOk_persistent (E : List w8 → GoInterface → IProp GF) :
    Persistent (errsOk (GF := GF) E) := by
  unfold errsOk; infer_instance
instance readerOk_persistent (rd : GoInterface) (I : List w8 → IProp GF) :
    Persistent (readerOk (GF := GF) rd I) := by
  unfold readerOk; infer_instance
instance writerOk_persistent (wr : GoInterface) (J Q : List w8 → IProp GF) :
    Persistent (writerOk (GF := GF) wr J Q) := by
  unfold writerOk; infer_instance

/-- The `*bufio.Reader` `br` over `rd` (with the stream state `I`) has returned `R`: dsv-bufio's
`ownBufReader` (reads into a non-empty buffer, errors with a message). Over a connection `I` is
`recvTokL`: the protocol fact of what was read comes a step later (`ownReader_proto`). -/
def ownReader (br : Loc) (rd : GoInterface) (I : List w8 → IProp GF) (R : List w8) :
    IProp GF :=
  iprop(∃ (ri : GoInterfaceOk) (E : List w8 → GoInterface → IProp GF), ⌜rd = interface.ok ri⌝ ∗
    errsOk E ∗ EtcdGrove.bufio.ownBufReader br ri (fun _ m => 0 < m) I E R)

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

/-- The `io.Reader` `rd` over `I`, for `io.ReadFull`/`io.ReadAtLeast`: Perennial's `io.readerOk`
with a condition every read meets (a `*bufio.Reader`'s), errors with a message (persistent). -/
def readsOk (rd : GoInterface) (I : List w8 → IProp GF) : IProp GF :=
  iprop(∃ (ri : GoInterfaceOk) (Pre : List w8 → Nat → Prop) (E : List w8 → GoInterface → IProp GF),
    ⌜rd = interface.ok ri ∧ ∀ r m, Pre r m⌝ ∗ errsOk E ∗ io.readerOk ri Pre I E)

instance readsOk_persistent (rd : GoInterface) (I : List w8 → IProp GF) :
    Persistent (readsOk (GF := GF) rd I) := by
  unfold readsOk; infer_instance

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

theorem NewWriter.labProof [github_com.imdea_software.swiftpaxos.SwiftBufioDeps GF] : NewWriter.labSpec (GF := GF) := by
  intro wr J Q W
  iintro %Φ ⟨#Hpkg, #Hwr, HJ, #HQ⟩ HΦ
  iunfold writerOk at Hwr
  icases Hwr with ⟨%e, %Ew, %He, -, #Hio⟩
  obtain ⟨rfl, hty⟩ := He
  wp_apply (github_com.imdea_software.swiftpaxos.SwiftBufioDeps.newWriter (GF := GF))
    e J Q Ew W $$ [HJ] as %bw Hown
  · iframe Hpkg Hio HJ HQ; ipureintro; exact hty
  iapply HΦ
  unfold ownWriter
  iexists e, Ew, 4096
  iframe Hown; ipureintro; rfl

theorem Writer.Flush.labProof [github_com.imdea_software.swiftpaxos.SwiftBufioDeps GF] : Writer.Flush.labSpec (GF := GF) := by
  intro bw wr J Q sent pend err
  iintro %Φ ⟨-, -, Hown⟩ HΦ
  iunfold ownWriter at Hown
  icases Hown with ⟨%e, %Ew, %sz, %He, Hown⟩
  wp_apply (github_com.imdea_software.swiftpaxos.SwiftBufioDeps.flush (GF := GF)) bw e J Q Ew sz sent pend err $$ [Hown]
    as %e' ⟨%k, %Hk, Hown⟩
  · iexact Hown
  iapply HΦ
  iexists k
  isplitr
  · ipureintro; exact Hk
  unfold ownWriter
  iexists e, Ew, sz
  iframe Hown; ipureintro; exact He

theorem Writer.WriteByte.labProof [github_com.imdea_software.swiftpaxos.SwiftBufioDeps GF] : Writer.WriteByte.labSpec (GF := GF) := by
  intro bw wr J Q sent pend err c
  iintro %Φ ⟨-, -, Hown, #HQ⟩ HΦ
  iunfold ownWriter at Hown
  icases Hown with ⟨%e, %Ew, %sz, %He, Hown⟩
  wp_apply (github_com.imdea_software.swiftpaxos.SwiftBufioDeps.writeByte (GF := GF))
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

theorem Writer.Write.labProof [github_com.imdea_software.swiftpaxos.SwiftBufioDeps GF] : Writer.Write.labSpec (GF := GF) := by
  intro bw wr J Q sent pend err p dq ps
  iintro %Φ ⟨-, -, Hown, #HQ, Hp⟩ HΦ
  iunfold ownWriter at Hown
  icases Hown with ⟨%e, %Ew, %sz, %He, Hown⟩
  wp_apply (github_com.imdea_software.swiftpaxos.SwiftBufioDeps.write (GF := GF))
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

theorem Writer.WriteByte_err.labProof [github_com.imdea_software.swiftpaxos.SwiftBufioDeps GF] : Writer.WriteByte_err.labSpec (GF := GF) := by
  intro bw wr J Q sent pend err c herr
  iintro %Φ Hown HΦ
  iunfold ownWriter at Hown
  icases Hown with ⟨%e, %Ew, %sz, %He, Hown⟩
  wp_apply (github_com.imdea_software.swiftpaxos.SwiftBufioDeps.writeByte (GF := GF))
    bw e J Q Ew sz sent pend err c $$ [Hown] as %e' ⟨%sent', %pend', %Hk, Hown⟩
  · iframe Hown; iintro %h; exact absurd h herr
  obtain ⟨-, -, -, h4, -⟩ := Hk
  obtain ⟨rfl, rfl, rfl⟩ := h4 herr
  iapply HΦ
  unfold ownWriter
  iexists e, Ew, sz
  iframe Hown; ipureintro; exact He

theorem Writer.Write_err.labProof [github_com.imdea_software.swiftpaxos.SwiftBufioDeps GF] : Writer.Write_err.labSpec (GF := GF) := by
  intro bw wr J Q sent pend err p dq ps herr
  iintro %Φ ⟨Hown, Hp⟩ HΦ
  iunfold ownWriter at Hown
  icases Hown with ⟨%e, %Ew, %sz, %He, Hown⟩
  wp_apply (github_com.imdea_software.swiftpaxos.SwiftBufioDeps.write (GF := GF))
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

/-- Two writers at one location exclude each other (dsv-bufio's `ownBufWriter_excl`). -/
theorem ownWriter_excl (bw : Loc) (wr wr' : GoInterface) (J Q J' Q' : List w8 → IProp GF)
    (s p s' p' : List w8) (e e' : GoInterface) :
    ownWriter bw wr J Q s p e ∗ ownWriter bw wr' J' Q' s' p' e' ⊢ False := by
  unfold ownWriter
  iintro ⟨⟨%i1, %E1, %z1, -, H1⟩, ⟨%i2, %E2, %z2, -, H2⟩⟩
  iapply EtcdGrove.bufio.ownBufWriter_excl $$ [$H1 $H2]

/-- A reader is not at `null` (dsv-bufio's `ownBufReader_not_null`). -/
theorem ownReader_not_null (br : Loc) (rd : GoInterface) (I : List w8 → IProp GF) (R : List w8) :
    ownReader br rd I R ⊢ ⌜br ≠ null⌝ := by
  unfold ownReader
  iintro ⟨%ri, %E, -, -, H⟩
  iapply EtcdGrove.bufio.ownBufReader_not_null $$ H

end writerProofs

/-! ### The reader's lab specs, from dsv-bufio's and Perennial's `io` -/

section readerProofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [bufio.Assumptions] [io.Assumptions]

theorem errWf_of_ptrTyped {e : GoInterface} (h : io.ptrTyped e) : errWf e :=
  fun ii hi T hT => h ii T hi hT

/-- An `errors.New` variable holds an error with a message. -/
theorem newVar_err (X msg : GoString) :
    errors.newVar (GF := GF) X msg ⊢
      ∃ e : GoInterface, globalAddr X ↦□ e ∗ models_lab.errAny e ∗
        ⌜errWf e ∧ e ≠ interface.nil⌝ := by
  iintro #Hv
  ihave #Hv' := Hv
  iunfold errors.newVar at Hv'
  icases Hv' with ⟨%x, #Hx, -⟩
  iunfold errors.newVar at Hv
  icases Hv with ⟨%x', #Hx', -, #HE⟩
  icombine Hx Hx' gives %Heq
  ihave #Ha : models_lab.errAny (GF := GF)
      (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x') $$ []
  · unfold models_lab.errAny
    iexists ⟨go.GoType.PointerType errors.errorString.ty, #x'⟩
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; go_type_set
    imodintro
    iintro %Φ HΦ
    iapply HE
    inext
    iapply HΦ
  iexists _
  iframe Hx
  rw [Heq]
  iframe Ha
  ipureintro
  refine ⟨?_, by simp [interface.mkOk]⟩
  intro ii hi T hT
  simp [interface.mkOk] at hi
  subst hi
  exact ⟨x', rfl⟩

/-- A `*bufio.Reader`'s errors (its reader's, or `io.ErrNoProgress`) have a message. -/
theorem errsOk_errE (E : List w8 → GoInterface → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.io ∗ errsOk E ⊢ errsOk (EtcdGrove.bufio.errE E) := by
  iintro ⟨#Hio, #HE⟩
  ihave #Hi := io.isInit_access $$ Hio
  icases Hi with ⟨-, -, -, -, -, -, #HNP, -⟩
  icases newVar_err _ _ $$ HNP with ⟨%enp, #Henp, #Ha, %Hw⟩
  unfold errsOk EtcdGrove.bufio.errE
  iintro !> %r %e (H | #H)
  · iapply HE $$ H
  · icombine H Henp gives %Heq
    subst Heq
    iframe Ha; ipureintro; exact Hw.1

theorem errAt_errOrNil (E : List w8 → GoInterface → IProp GF) (r : List w8) (e : GoInterface) :
    errsOk E ⊢ io.errAt E r e -∗ ⌜io.ptrTyped e⌝ -∗ errOrNil e := by
  iintro #HE #He %hp
  unfold io.errAt errOrNil
  icases He with (%h | #H)
  · ileft; ipureintro; exact h
  · iright
    iunfold errsOk at HE
    icases HE $$ H with ⟨#Ha, %Hw⟩
    iframe Ha; ipureintro; exact Hw

theorem NewReader.labProof [github_com.imdea_software.swiftpaxos.SwiftBufioDeps GF] : NewReader.labSpec (GF := GF) := by
  intro rd I R
  iintro %Φ ⟨#Hpkg, #Hrd, HI⟩ HΦ
  iunfold readerOk at Hrd
  icases Hrd with ⟨%ri, %E, %He, #HE, #Hok⟩
  obtain ⟨rfl, hty⟩ := He
  wp_apply (github_com.imdea_software.swiftpaxos.SwiftBufioDeps.newReaderOk (GF := GF))
    ri (fun _ m => 0 < m) I E R $$ [HI] as %br Hown
  · isplitr
    · ipureintro; exact hty
    iframe Hpkg Hok HI
    iapply EtcdGrove.bufio.preUpTo_trivial
  iapply HΦ
  unfold ownReader
  iexists ri, E
  iframe HE Hown
  ipureintro; rfl

/-- `ReadByte`'s result, the error case with its message. -/
theorem readByte_post (br : Loc) (rd : GoInterface) (I : List w8 → IProp GF) (R : List w8)
    (ri : GoInterfaceOk) (E : List w8 → GoInterface → IProp GF) (hrd : rd = interface.ok ri)
    (c : w8) (err : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.io ∗ errsOk E ∗
      ((⌜err = interface.nil⌝ ∗
          EtcdGrove.bufio.ownBufReader br ri (fun _ m => 0 < m) I E (R ++ [c])) ∨
        (⌜err ≠ interface.nil⌝ ∗ □ EtcdGrove.bufio.errE E R err ∗ ⌜io.ptrTyped err⌝ ∗
          EtcdGrove.bufio.ownBufReader br ri (fun _ m => 0 < m) I E R)) ⊢
      (⌜err = interface.nil⌝ ∗ ownReader br rd I (R ++ [c])) ∨
        (⌜err ≠ interface.nil ∧ errWf err⌝ ∗ models_lab.errAny err ∗ ownReader br rd I R) := by
  iintro ⟨#Hio, #HE, (⟨%h, Hown⟩ | ⟨%h, #He, %hp, Hown⟩)⟩
  · ileft
    isplitr
    · ipureintro; exact h
    unfold ownReader
    iexists ri, E
    iframe HE Hown
    ipureintro; exact hrd
  · iright
    ihave #HE' := errsOk_errE E $$ [$Hio $HE]
    iunfold errsOk at HE'
    icases HE' $$ He with ⟨#Ha, -⟩
    iframe Ha
    isplitr
    · ipureintro; exact ⟨h, errWf_of_ptrTyped hp⟩
    unfold ownReader
    iexists ri, E
    iframe HE Hown
    ipureintro; exact hrd

theorem Reader.ReadByte_wf.labProof [github_com.imdea_software.swiftpaxos.SwiftBufioDeps GF] : Reader.ReadByte_wf.labSpec (GF := GF) := by
  intro br rd I R
  iintro %Φ ⟨#Hpkg, -, Hown⟩ HΦ
  ihave #Hio := EtcdGrove.bufio.io_init_of_bufio $$ Hpkg
  iunfold ownReader at Hown
  icases Hown with ⟨%ri, %E, %hrd, #HE, Hown⟩
  wp_apply (github_com.imdea_software.swiftpaxos.SwiftBufioDeps.readByte (GF := GF)) br ri (fun _ m => 0 < m) I E R $$ [Hown]
    as %c %err Hr
  · iexact Hown
  iapply HΦ
  iapply readByte_post br rd I R ri E hrd c err $$ [$Hio $HE $Hr]

theorem Reader.ReadByte.labProof [github_com.imdea_software.swiftpaxos.SwiftBufioDeps GF] : Reader.ReadByte.labSpec (GF := GF) := by
  intro br rd I R
  iintro %Φ ⟨#Hpkg, #Hrd, Hown⟩ HΦ
  wp_apply Reader.ReadByte_wf.labProof br rd I R $$ [$Hpkg $Hrd $Hown] as %c %err Hr
  iapply HΦ
  icases Hr with (H | ⟨⟨%h, -⟩, #Ha, Hown⟩)
  · ileft; iexact H
  · iright; iframe Ha Hown; ipureintro; exact h

theorem Reader.Read.labProof [github_com.imdea_software.swiftpaxos.SwiftBufioDeps GF] : Reader.Read.labSpec (GF := GF) := by
  intro br rd I R p ps
  iintro %Φ ⟨#Hpkg, -, Hown, Hp⟩ HΦ
  ihave #Hio := EtcdGrove.bufio.io_init_of_bufio $$ Hpkg
  iunfold ownReader at Hown
  icases Hown with ⟨%ri, %E, %hrd, #HE, Hown⟩
  wp_apply (github_com.imdea_software.swiftpaxos.SwiftBufioDeps.readOk (GF := GF)) br ri (fun _ m => 0 < m) I E R p ps
    $$ [Hown Hp] as %n %err ⟨%ys, %Hys, Hp, Hown, #He, %hp⟩
  · iframe Hown Hp; ipureintro; exact id
  ihave #HE' := errsOk_errE E $$ [$Hio $HE]
  iapply HΦ
  iexists ys
  isplitr
  · ipureintro; exact ⟨EtcdGrove.bufio.w64_of_sintZ Hys.1, Hys.2⟩
  iframe Hp
  isplitl [Hown]
  · unfold ownReader
    iexists ri, E
    iframe HE Hown
    ipureintro; exact hrd
  iapply errAt_errOrNil _ _ _ $$ HE' He
  ipureintro; exact hp

/-- A `*bufio.Reader` (as an `io.Reader`) reads its stream (the lab's `bufio.bufioReadsOk`). -/
theorem bufioReadsOk [github_com.imdea_software.swiftpaxos.SwiftBufioDeps GF] (br : Loc) (rd : GoInterface) (I : List w8 → IProp GF) :
    (isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ readerOk rd I) ⊢
      readsOk (interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br) (ownReader br rd I) := by
  iintro ⟨#Hpkg, -⟩
  ihave #Hio := EtcdGrove.bufio.io_init_of_bufio $$ Hpkg
  unfold readsOk
  iexists EtcdGrove.bufio.readerIface br, (fun _ _ => True),
    (fun _ e => iprop(models_lab.errAny e ∗ ⌜errWf e⌝))
  isplitr
  · ipureintro; exact ⟨rfl, fun _ _ => trivial⟩
  isplitr
  · unfold errsOk; iintro !> %r %e H; iexact H
  unfold io.readerOk EtcdGrove.bufio.readerIface
  iintro !> %R %p %xs
  iintro !> %Φ ⟨-, Hown, Hp⟩ HΦ
  dsimp only
  iunfold ownReader at Hown
  icases Hown with ⟨%ri, %E, %hrd, #HE, Hown⟩
  wp_apply (github_com.imdea_software.swiftpaxos.SwiftBufioDeps.readOk (GF := GF)) br ri (fun _ m => 0 < m) I E R p xs
    $$ [Hown Hp] as %n %err ⟨%ys, %Hys, Hp, Hown, #He, %hp⟩
  · iframe Hown Hp; ipureintro; exact id
  ihave #HE' := errsOk_errE E $$ [$Hio $HE]
  iapply HΦ
  iexists ys
  iframe Hp
  isplitr
  · ipureintro; exact Hys
  isplitl [Hown]
  · unfold ownReader
    iexists ri, E
    iframe HE Hown
    ipureintro; exact hrd
  isplitr
  · unfold io.errAt
    icases He with (%h | #H)
    · ileft; ipureintro; exact h
    · iright; imodintro; iunfold errsOk at HE'; iapply HE' $$ H
  ipureintro; exact hp

/-- `io.ReadAtLeast`'s result as the lab's: from `readAtLeastRes`. -/
theorem readAtLeastRes_lab (E : List w8 → GoInterface → IProp GF) (eof ueof sb : GoInterface)
    (r ys : List w8) (m : Nat) (min : w64) (err : GoInterface) (hmin : sint.Z min ≤ m)
    (hys : ys.length ≤ m) (hu : errWf ueof ∧ ueof ≠ interface.nil) :
    errsOk E ⊢ models_lab.errAny ueof -∗
      io.readAtLeastRes E eof ueof sb r ys m (sint.Z min) err -∗
      ⌜err = interface.nil ↔ sint.Z min ≤ ys.length⌝ ∗ errOrNil err := by
  iintro #HE #Hu #Hr
  unfold io.readAtLeastRes
  icases Hr with (%h | %h | ⟨%e, %h, #H⟩)
  · exfalso; omega
  · obtain ⟨-, h2, rfl⟩ := h
    isplitr
    · ipureintro; exact ⟨fun _ => h2, fun _ => rfl⟩
    unfold errOrNil; ileft; ipureintro; rfl
  · obtain ⟨-, h2, hne, h3, h4⟩ := h
    iunfold errsOk at HE
    icases HE $$ H with ⟨#Ha, %Hw⟩
    by_cases hc : e = eof ∧ ys ≠ []
    · have := h3 hc; subst this
      isplitr
      · ipureintro; exact ⟨fun h => absurd h hu.2, fun h => by omega⟩
      unfold errOrNil; iright; iframe Hu; ipureintro; exact hu.1
    · have := h4 hc; subst this
      isplitr
      · ipureintro; exact ⟨fun h => absurd h hne, fun h => by omega⟩
      unfold errOrNil; iright; iframe Ha; ipureintro; exact Hw

/-- `io`'s error variables. -/
theorem io_errs :
    isPkgInit (PROP := IProp GF) pkg_id.io ⊢
      ∃ eof ueof sb : GoInterface, globalAddr io.EOF ↦□ eof ∗
        globalAddr io.ErrUnexpectedEOF ↦□ ueof ∗ globalAddr io.ErrShortBuffer ↦□ sb ∗
        models_lab.errAny ueof ∗ ⌜errWf ueof ∧ ueof ≠ interface.nil⌝ := by
  iintro #Hio
  ihave #Hi := io.isInit_access $$ Hio
  icases Hi with ⟨-, -, -, #HSB, #HEOF, #HUE, -⟩
  icases newVar_err _ _ $$ HSB with ⟨%sb, #Hsb, -⟩
  icases newVar_err _ _ $$ HEOF with ⟨%eof, #Heof, -⟩
  icases newVar_err _ _ $$ HUE with ⟨%ueof, #Hueof, #Ha, %Hw⟩
  iexists eof, ueof, sb
  iframe Heof Hueof Hsb Ha
  ipureintro; exact Hw

theorem io.ReadAtLeast.labProof : io.ReadAtLeast.labSpec (GF := GF) := by
  intro rd I R buf bs min hmin
  iintro %Φ ⟨#Hio, #Hrd, HI, Hb⟩ HΦ
  iunfold readsOk at Hrd
  icases Hrd with ⟨%ri, %Pre, %E, %He, #HE, #Hok⟩
  obtain ⟨rfl, hPre⟩ := He
  icases io_errs $$ Hio with ⟨%eof, %ueof, %sb, #Heof, #Hueof, #Hsb, #Hu, %Hw⟩
  wp_apply _root_.Perennial.io.wp_ReadAtLeast ri Pre I E R buf bs min eof ueof sb $$ [HI Hb]
    as %n %err ⟨%ys, %Hys, Hb, HI, #Hr⟩
  · iframe Hok Heof Hueof Hsb HI Hb
    ipureintro; intro ys _; exact hPre _ _
  ihave ⟨%Hiff, #Herr⟩ := readAtLeastRes_lab E eof ueof sb R ys bs.length min err hmin Hys.2 Hw
    $$ HE Hu Hr
  iapply HΦ
  iexists ys
  isplitr
  · ipureintro; exact ⟨EtcdGrove.bufio.w64_of_sintZ Hys.1, Hys.2, Hiff⟩
  iframe Hb HI Herr

theorem io.ReadFull.labProof : io.ReadFull.labSpec (GF := GF) := by
  intro rd I R buf bs
  iintro %Φ ⟨#Hio, #Hrd, HI, Hb⟩ HΦ
  iunfold readsOk at Hrd
  icases Hrd with ⟨%ri, %Pre, %E, %He, #HE, #Hok⟩
  obtain ⟨rfl, hPre⟩ := He
  icases io_errs $$ Hio with ⟨%eof, %ueof, %sb, #Heof, #Hueof, -, #Hu, %Hw⟩
  wp_apply _root_.Perennial.io.wp_ReadFull ri Pre I E R buf bs eof ueof $$ [HI Hb]
    as %n %err ⟨%ys, %Hys, Hb, HI, #Hr⟩
  · iframe Hok Heof Hueof HI Hb
    ipureintro; intro ys _; exact hPre _ _
  iapply HΦ
  iexists ys
  iframe Hb HI
  unfold io.readFullRes
  icases Hr with (%h | ⟨%e, %h, #H⟩)
  · obtain ⟨h1, rfl⟩ := h
    isplitr
    · ipureintro; exact ⟨EtcdGrove.bufio.w64_of_sintZ Hys.1, Hys.2, fun _ => h1, fun _ => rfl⟩
    unfold errOrNil; ileft; ipureintro; rfl
  · obtain ⟨h1, hne, h3, h4⟩ := h
    iunfold errsOk at HE
    icases HE $$ H with ⟨#Ha, %Hwe⟩
    by_cases hc : e = eof ∧ ys ≠ []
    · have := h3 hc; subst this
      isplitr
      · ipureintro
        exact ⟨EtcdGrove.bufio.w64_of_sintZ Hys.1, Hys.2, fun h => absurd h Hw.2,
          fun h => by omega⟩
      unfold errOrNil; iright; iframe Hu; ipureintro; exact Hw.1
    · have := h4 hc; subst this
      isplitr
      · ipureintro
        exact ⟨EtcdGrove.bufio.w64_of_sintZ Hys.1, Hys.2, fun h => absurd h hne,
          fun h => by omega⟩
      unfold errOrNil; iright; iframe Ha; ipureintro; exact Hwe

end readerProofs

end bufio

end Perennial
