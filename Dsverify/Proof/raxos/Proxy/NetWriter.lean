/-
Package `proxy`: the client port's protocol is closed under prefixes (`ProtoPrefixClosed`), as
`net.conn_streamWriterOk` asks of the writers' connections (`NetDial.lean`).

Changed against the lab: the lab's `wp_WriteByte_sticky` (a `WriteByte` on a writer with a sticky
error) and `marshal_strong` (`Marshal` straight into a `*bufio.Writer`) go: the landed
`bufio.Writer.WriteByte.spec` asks the protocol only when the writer has no error (review W1),
and the proxy marshals into a `msgBuffer` (`MsgBuf.lean`).
-/
module

public import Dsverify.Proof.raxos.Proxy.NetSpecs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]

/-- The client port's protocol is prefix-closed. -/
theorem clientInProto_prefixClosed (γ : QNames) (c : Nat) :
    ProtoPrefixClosed (GF := GF) (clientInProto γ c) where
  nil cn := by
    iintro !>
    unfold clientInProto
    iexists 0, []
    isplitr
    · ipureintro; exact ⟨by decide, List.nil_prefix, by simp⟩
    · iempintro
  pre cn a b h := by
    iintro #H
    iintro !>
    unfold clientInProto
    icases H with ⟨%k, %L, %Hp, #HL⟩
    iexists k, L
    iframe HL
    ipureintro
    exact ⟨Hp.1, h.trans Hp.2.1, Hp.2.2⟩

end lemmas

end Perennial.raxos
