/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/client/Sink.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
Writing a message through an `io.Writer` (the generated `Marshal` methods' view of their
`wire`), internal to the client group (the replica group's marshaling would share it).

* `sinkOk wire S Q` (persistent): `wire.Write(p)` takes the intended stream `W` (`S W`) to
  `W ++ bs` for the bytes `bs` of `p`, when the stream with them is allowed (`□ Q (W ++ bs)`);
  its results are not inspected.
* `wsink bw wr J Q W`: a `*bufio.Writer` whose bytes so far are `W` unless it has a sticky
  error (then nothing more is sent); `bufio_sinkOk`: such a writer is a sink.
* `sinkOkE wire S Q` (persistent): `sinkOk` that also says the stream is dead (`∀ X, S X`)
  after a `Write` that fails (`encoding.gob.writeSink`; what gob's `Encode`, which stops at a
  failed `Write`, needs); `bufio_sinkOkE`: a `*bufio.Writer` (its error is sticky) is one;
  `sinkOk_of_E`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps


@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace wire

section defs

variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF] [github_com.imdea_software.swiftpaxos.SwiftHyps GF]

/-- `wire`'s `Write` appends to the intended stream (see the file header). -/
def sinkOk (wire : GoInterface) (S Q : List w8 → IProp GF) : IProp GF :=
  iprop(∃ e : GoInterfaceOk, ⌜wire = interface.ok e⌝ ∗
    □ ∀ (p : GoSlice) (dq : DFrac) (W bs : List w8) (Φ : val → IProp GF),
      S W -∗ □ Q (W ++ bs) -∗ p ↦*{dq} bs -∗
      ▷ (∀ (nn : w64) (err : GoInterface), S (W ++ bs) -∗ p ↦*{dq} bs -∗
          Φ (PairV #nn #err)) -∗
      WP (App (Val #(methods e.ty go!"Write" e.v)) (Val #p)) {{ Φ }})

instance sinkOk_persistent (wire : GoInterface) (S Q : List w8 → IProp GF) :
    Persistent (sinkOk wire S Q) := by
  unfold sinkOk; infer_instance

/-- A `*bufio.Writer` as a sink: its bytes are `W` unless its error is set. -/
def wsink (bw : Loc) (wr : GoInterface) (J Q : List w8 → IProp GF) (W : List w8) :
    IProp GF :=
  iprop(∃ (sent pend : List w8) (err : GoInterface), bufio.ownWriter bw wr J Q sent pend err ∗
    ⌜err = interface.nil → sent ++ pend = W⌝)

/-- `sinkOk`, and the stream is dead after a failed `Write` (see the file header). -/
def sinkOkE (wire : GoInterface) (S Q : List w8 → IProp GF) : IProp GF :=
  iprop(∃ e : GoInterfaceOk, ⌜wire = interface.ok e⌝ ∗ encoding.gob.writeSink e S Q)

instance sinkOkE_persistent (wire : GoInterface) (S Q : List w8 → IProp GF) :
    Persistent (sinkOkE wire S Q) := by
  unfold sinkOkE; infer_instance

end defs

section proofs

variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF] [github_com.imdea_software.swiftpaxos.SwiftHyps GF]
variable [bufio.Assumptions]

theorem bufio_sinkOk (bw : Loc) (wr : GoInterface) (J Q : List w8 → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ bufio.writerOk wr J Q ⊢
      sinkOk (interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw) (wsink bw wr J Q) Q := by
  iintro ⟨#Hpkg, #Hwr⟩
  unfold sinkOk
  iexists ⟨go.GoType.PointerType bufio.Writer.ty, #bw⟩
  isplitr
  · ipureintro; rfl
  imodintro
  iintro %p %dq %W %bs %Φ Hs #HQ Hp HΦ
  unfold wsink
  icases Hs with ⟨%sent, %pend, %err, Hown, %Hw⟩
  by_cases herr : err = interface.nil
  · subst herr
    have hw := Hw rfl
    wp_apply bufio.wp_Write bw wr J Q sent pend interface.nil p dq bs $$ [$Hpkg $Hwr Hown Hp]
      as %nn %e ⟨%k, %sent', %pend', %Hk, Hp, Hown⟩
    · iframe; rw [hw]; iexact HQ
    iapply HΦ $$ %nn %e [Hown] Hp
    iexists sent', pend', e
    iframe
    ipureintro
    intro he
    obtain ⟨-, -, h3, -, h5, -⟩ := Hk
    rw [h3, hw, h5 he, List.take_length]
  · wp_apply bufio.wp_Write_err bw wr J Q sent pend err p dq bs herr $$ [Hown Hp]
      as %nn ⟨Hp, Hown⟩
    · iframe
    iapply HΦ $$ %nn %err [Hown] Hp
    iexists sent, pend, err
    iframe
    ipureintro
    intro h; exact absurd h herr

theorem sinkOk_of_E (wire : GoInterface) (S Q : List w8 → IProp GF) :
    sinkOkE wire S Q ⊢ sinkOk wire S Q := by
  iintro #H
  unfold sinkOkE sinkOk
  icases H with ⟨%e, %He, #Hw⟩
  iexists e
  isplitr
  · ipureintro; exact He
  imodintro
  iintro %p %dq %W %bs %Φ HS #HQ Hp HΦ
  unfold encoding.gob.writeSink
  iapply Hw $$ %p %dq %W %bs %Φ HS HQ Hp
  inext
  iintro %nn %err Hr Hp
  icases Hr with (⟨-, HS⟩ | ⟨-, HS⟩)
  · iapply HΦ $$ %nn %err HS Hp
  · iapply HΦ $$ %nn %err [HS] Hp
    iapply HS

theorem bufio_sinkOkE (bw : Loc) (wr : GoInterface) (J Q : List w8 → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ bufio.writerOk wr J Q ⊢
      sinkOkE (interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #bw) (wsink bw wr J Q) Q := by
  iintro ⟨#Hpkg, #Hwr⟩
  unfold sinkOkE
  iexists ⟨go.GoType.PointerType bufio.Writer.ty, #bw⟩
  isplitr
  · ipureintro; rfl
  unfold encoding.gob.writeSink
  imodintro
  iintro %p %dq %W %bs %Φ Hs #HQ Hp HΦ
  unfold wsink
  icases Hs with ⟨%sent, %pend, %err, Hown, %Hw⟩
  by_cases herr : err = interface.nil
  · subst herr
    have hw := Hw rfl
    wp_apply bufio.wp_Write bw wr J Q sent pend interface.nil p dq bs $$ [$Hpkg $Hwr Hown Hp]
      as %nn %e ⟨%k, %sent', %pend', %Hk, Hp, Hown⟩
    · iframe; rw [hw]; iexact HQ
    iapply HΦ $$ %nn %e [Hown] Hp
    by_cases he : e = interface.nil
    · ileft
      isplitr
      · ipureintro; exact he
      iexists sent', pend', e
      iframe
      ipureintro
      intro _
      obtain ⟨-, -, h3, -, h5, -⟩ := Hk
      rw [h3, hw, h5 he, List.take_length]
    · iright
      isplitr
      · ipureintro; exact he
      iintro %X
      iexists sent', pend', e
      iframe
      ipureintro
      intro h; exact absurd h he
  · wp_apply bufio.wp_Write_err bw wr J Q sent pend err p dq bs herr $$ [Hown Hp]
      as %nn ⟨Hp, Hown⟩
    · iframe
    iapply HΦ $$ %nn %err [Hown] Hp
    iright
    isplitr
    · ipureintro; exact herr
    iintro %X
    iexists sent, pend, err
    iframe
    ipureintro
    intro h; exact absurd h herr

theorem wp_WriteByte_sink (bw : Loc) (wr : GoInterface) (J Q : List w8 → IProp GF)
    (W : List w8) (c : w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ bufio.writerOk wr J Q ∗ wsink bw wr J Q W ∗
        □ Q (W ++ [c]) }}
      (App (Val (bw @!! go.GoType.PointerType bufio.Writer.ty @!! go!"WriteByte")) (Val #c))
    {{ (e : GoInterface), RET #e; wsink bw wr J Q (W ++ [c]) }} := by
  iintro %Φ ⟨#Hpkg, #Hwr, Hs, #HQ⟩ HΦ
  unfold wsink
  icases Hs with ⟨%sent, %pend, %err, Hown, %Hw⟩
  by_cases herr : err = interface.nil
  · subst herr
    have hw := Hw rfl
    wp_apply bufio.wp_WriteByte bw wr J Q sent pend interface.nil c $$ [$Hpkg $Hwr Hown]
      as %e ⟨%sent', %pend', %Hk, Hown⟩
    · iframe; rw [hw]; iexact HQ
    iapply HΦ
    iexists sent', pend', e
    iframe
    ipureintro
    intro he
    rw [Hk.2.1 he, hw]
  · wp_apply bufio.wp_WriteByte_err bw wr J Q sent pend err c herr $$ [$Hown] as Hown
    iapply HΦ
    iexists sent, pend, err
    iframe
    ipureintro
    intro h; exact absurd h herr

theorem wp_Flush_sink (bw : Loc) (wr : GoInterface) (J Q : List w8 → IProp GF) (W : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ bufio.writerOk wr J Q ∗ wsink bw wr J Q W }}
      (App (Val (bw @!! go.GoType.PointerType bufio.Writer.ty @!! go!"Flush")) (Val #()))
    {{ (e : GoInterface), RET #e; ∃ (sent pend : List w8) (err : GoInterface),
        bufio.ownWriter bw wr J Q sent pend err ∗
        ⌜err = interface.nil → sent = W ∧ pend = []⌝ }} := by
  iintro %Φ ⟨#Hpkg, #Hwr, Hs⟩ HΦ
  unfold wsink
  icases Hs with ⟨%sent, %pend, %err, Hown, %Hw⟩
  wp_apply bufio.wp_Flush bw wr J Q sent pend err $$ [$Hpkg $Hwr $Hown] as %e ⟨%k, %Hk, Hown⟩
  iapply HΦ
  iexists _, _, e
  iframe
  ipureintro
  intro he
  obtain ⟨hk1, hk2, hk3⟩ := Hk
  have hk := hk2 he
  subst hk
  have herr : err = interface.nil := Classical.byContradiction fun h => h ((hk3 h).1 ▸ he)
  rw [List.take_length, List.drop_length]
  exact ⟨Hw herr, rfl⟩

end proofs

end wire

end Perennial
