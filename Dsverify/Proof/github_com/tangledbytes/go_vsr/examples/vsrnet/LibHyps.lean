/-
The vr kit's library premises other than `encoding/json` (`JsonHyps.lean`) and the package
initializers (notes/dsv-vr.md, "Hypotheses"): `log/slog`'s specs (no Lean model of `log/slog` here;
`Proof/replica/LibHyps.lean`, `Proof/network/LibHyps.lean`) and `connReaderOk` (finding 5), bundled
as `LibHyps`, one `Prop`; each a named spec, none an axiom.

`connReaderOk`: the end `s` of a connection `cn` (a `*TCPConn` `t`) is an `io.Reader` (Perennial's
`io.readerOk`, with Net's `net.connReadE` errors) whose stream state is `recvTokL cn s P`, for any
buffer. Net's law `net.conn_readerOk` (`Net/Proof/net/ConnIo.lean`) asks `0 < len(p)` of each read,
which Perennial's `io.ReadFull.spec` cannot give (its premise asks `Pre` of every remaining length,
`0` included, though `ReadAtLeast` reads only while bytes remain); and a read into an empty buffer
is not derivable from `net.Conn.Read.spec`, whose count is only `sint.nat k = 0` there. True of Go:
a `*TCPConn`'s `Read` of an empty buffer returns `0, nil` without reading.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.LibHyps
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.network.LibHyps
public import Net.Proof.net.ConnIo
public import Perennial.Proof.io.Reader

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.tangledbytes.go_vsr.examples.vsrnet

section hyps
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.tangledbytes.go_vsr.examples.vsrnet.Assumptions]
variable [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

/-- **Premise** (see the file header): a connection's end is an `io.Reader` of its stream, for any
buffer. -/
abbrev connReaderOk : Prop :=
  ∀ (t : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra eof ed : GoInterface) (P : Proto GF),
    io.ptrTyped eof →
    net.connAt (GF := GF) t cn s a la ra ∗ globalAddr io.EOF ↦□ eof ∗
        globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ⊢
      io.readerOk ⟨go.GoType.PointerType net.TCPConn.ty, #t⟩ (fun _ _ => True)
        (recvTokL (Gg := hG.goose_globalGS) cn s P) (net.connReadE eof la ra ed)

/-- **The kit's library premises** but `encoding/json`'s (see the file header). -/
structure LibHyps : Prop where
  slog_New : log.slog.New.spec (GF := GF) (hG := hG)
  slog_Discard : log.slog.DiscardHandler.load_spec (GF := GF) (hG := hG)
  slog_Debug : log.slog.Debug.spec (GF := GF) (hG := hG)
  slog_LDebug : log.slog.Logger.Debug.spec (GF := GF) (hG := hG)
  slog_LInfo : log.slog.Logger.Info.spec (GF := GF) (hG := hG)
  slog_LWarn : log.slog.Logger.Warn.spec (GF := GF) (hG := hG)
  slog_LError : log.slog.Logger.Error.spec (GF := GF) (hG := hG)
  conn_readerOk : connReaderOk (GF := GF) (hG := hG)

end hyps

end github_com.tangledbytes.go_vsr.examples.vsrnet
end Perennial
