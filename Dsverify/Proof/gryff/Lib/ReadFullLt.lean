/-
Copied from dsv-rabia (`Dsverify/Proof/rabia/examples/rabianet/ConnRead.lean`; specs and the
connection lemma; `ReadFullLtProof.lean` holds the two proofs). Gryff's `waitForPeerConnections`
reads a peer's 4-byte handshake with `io.ReadFull(conn, bs)` directly. Changed: `wp_connReadFull`
also gives an error's `errAny` (for `log.Printf("… %v", err)`).
`io.ReadFull` over a reader whose contract asks a condition only of reads that `ReadAtLeast` makes
(`ys.length < xs.length`: it reads only while it has fewer bytes than asked), such as a
connection's (`net.conn_readerOk`: a non-empty buffer). Perennial's `io.ReadAtLeast.spec` asks the
condition at every `ys.length ≤ xs.length`, the full buffer included, which a connection's
contract does not meet (the gap dsv-bufio records as review C1; Perennial branch
`readatleast-prefix` changes the premise). Until it lands: `io.ReadAtLeast.wp_proofLt`, a copy of
Perennial's proof (`Perennial/Proof/io/ReadAtLeast.lean`, Perennial `9c3b81f3`) with the weaker
premise (one line changed), and `io.ReadFull.wp_proofLt` over it; then `wp_connReadFull`, a
connection end's `io.ReadFull` (the kit's `sendConf` and `awaitConf` read a connection with
`io.ReadFull` directly).
-/
module

public import Perennial.Spec.io.ReadAtLeast
public import Perennial.Spec.io.ReadFull
public import Net.Proof.net.ConnIo
public import Net.Spec.net.Conn__Read
public import Dsverify.Proof.gryff.N.ConnErr

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.lib

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `io.ReadAtLeast.spec` with the condition asked only below the buffer's length. -/
abbrev io.ReadAtLeast.specLt : Prop :=
  ∀ (ri : GoInterfaceOk) (Pre : List w8 → Nat → Prop) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → IProp GF) (r0 : List w8) (p : GoSlice) (xs : List w8)
    (min : w64) (eof ueof sb : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗ _root_.Perennial.io.readerOk ri Pre S E ∗
      globalAddr _root_.Perennial.io.EOF ↦□ eof ∗ globalAddr _root_.Perennial.io.ErrUnexpectedEOF ↦□ ueof ∗
      globalAddr _root_.Perennial.io.ErrShortBuffer ↦□ sb ∗
      ⌜∀ ys : List w8, ys.length < xs.length → Pre (r0 ++ ys) (xs.length - ys.length)⌝ ∗
      S r0 ∗ p ↦* xs }}
    (App (App (App (Val (@! _root_.Perennial.io.ReadAtLeast)) (Val #(interface.ok ri))) (Val #p)) (Val #min))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      ∃ ys : List w8, ⌜sint.Z n = ys.length ∧ ys.length ≤ xs.length⌝ ∗
        p ↦* (ys ++ xs.drop ys.length) ∗ S (r0 ++ ys) ∗
        _root_.Perennial.io.readAtLeastRes E eof ueof sb r0 ys xs.length (sint.Z min) err }}

/-- `io.ReadFull.spec` with the condition asked only below the buffer's length. -/
abbrev io.ReadFull.specLt : Prop :=
  ∀ (ri : GoInterfaceOk) (Pre : List w8 → Nat → Prop) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → IProp GF) (r0 : List w8) (p : GoSlice) (xs : List w8)
    (eof ueof : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗ _root_.Perennial.io.readerOk ri Pre S E ∗
      globalAddr _root_.Perennial.io.EOF ↦□ eof ∗ globalAddr _root_.Perennial.io.ErrUnexpectedEOF ↦□ ueof ∗
      ⌜∀ ys : List w8, ys.length < xs.length → Pre (r0 ++ ys) (xs.length - ys.length)⌝ ∗
      S r0 ∗ p ↦* xs }}
    (App (App (Val (@! _root_.Perennial.io.ReadFull)) (Val #(interface.ok ri))) (Val #p))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      ∃ ys : List w8, ⌜sint.Z n = ys.length ∧ ys.length ≤ xs.length⌝ ∗
        p ↦* (ys ++ xs.drop ys.length) ∗ S (r0 ++ ys) ∗
        _root_.Perennial.io.readFullRes E eof ueof r0 ys xs.length err }}

end spec

section conn
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [_root_.Perennial.io.Assumptions] [net.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]

/-- `io.ReadFull(c, p)` of the end `s` of the connection `cn` (its `*TCPConn` `t`): what it read
extends the reader's token; no error only if it filled `p`. -/
theorem wp_connReadFull (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (wp_ReadFullLt : io.ReadFull.specLt (GF := GF) (hG := hG)) (t : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra ed : GoInterface)
    (P : Proto GF) (r0 : List w8) (p : GoSlice) (xs : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗ net.connAt t cn s a la ra ∗
        globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗
        recvTokL (Gg := hG.goose_globalGS) cn s P r0 ∗ p ↦* xs }}
      (App (App (Val (@! _root_.Perennial.io.ReadFull))
        (Val #(interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t))) (Val #p))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ∃ ys : List w8, ⌜sint.Z n = ys.length ∧ ys.length ≤ xs.length ∧
          (err = interface.nil → ys.length = xs.length)⌝ ∗
        p ↦* (ys ++ xs.drop ys.length) ∗ recvTokL (Gg := hG.goose_globalGS) cn s P (r0 ++ ys) ∗
        (⌜err = interface.nil⌝ ∨ models_lab.errAny err) }} := by
  iintro %Φ ⟨#Hio, #Hc, #Hed, HS, Hp⟩ HΦ
  ihave #Hi := _root_.Perennial.io.isInit_access $$ Hio
  icases Hi with ⟨-, -, -, -, #HEOFv, #HUEOFv, -⟩
  ihave #HEOF := HEOFv
  ihave #HUEOF := HUEOFv
  iunfold _root_.Perennial.errors.newVar at HEOF HUEOF
  icases HEOF with ⟨%x1, #Heof, -⟩
  icases HUEOF with ⟨%x2, #Hueof, -⟩
  ihave #Hrok := net.conn_readerOk wp_Read t cn s a la ra _ ed P $$ [$Hio $Hc $Heof $Hed]
  rw [show interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t = GoInterface.ok (net.connIface t)
    from rfl]
  iapply wp_ReadFullLt (net.connIface t) (fun _ m => 0 < m)
    (recvTokL (Gg := hG.goose_globalGS) cn s P) _ r0 p xs _ _ $$ [HS Hp]
  · iframe Hio Hrok Heof Hueof HS Hp
    ipureintro
    intro ys h; show 0 < xs.length - ys.length; omega
  inext
  iintro %n %err ⟨%ys, %Hys, Hp, HS, #Hres⟩
  unfold _root_.Perennial.io.readFullRes
  ihave %Himp : ⌜err = interface.nil → ys.length = xs.length⌝ $$ [Hres]
  · icases Hres with (%h | ⟨%e, %h, -⟩)
    · ipureintro; exact fun _ => h.1
    · ipureintro
      obtain ⟨hlt, hne, h1, h2⟩ := h
      intro he
      exfalso
      by_cases hc : e = interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x1 ∧ ys ≠ []
      · rw [h1 hc] at he; simp [interface.mkOk] at he
      · rw [h2 hc] at he; exact hne he
  ihave #HeA : iprop(⌜err = interface.nil⌝ ∨ models_lab.errAny err) $$ [Hres]
  · icases Hres with (%h | ⟨%e, %h, #HE⟩)
    · ileft; ipureintro; exact h.2
    · iright
      obtain ⟨hlt, hne, h1, h2⟩ := h
      by_cases hc : e = interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x1 ∧ ys ≠ []
      · rw [h1 hc]
        ihave ⟨H, -⟩ := netN.newVar_errAny _ _ _ $$ HUEOFv Hueof
        iexact H
      · rw [h2 hc]
        unfold net.connReadE
        icases HE with (%He | ⟨%k, Hk⟩)
        · subst He
          ihave ⟨H, -⟩ := netN.newVar_errAny _ _ _ $$ HEOFv Heof
          iexact H
        · unfold net.resErr net.opErr
          icases Hk with ⟨%e', ⟨%pe, %nw, ⟨%Herr, -⟩, #Hpe⟩, -⟩
          subst Herr
          iapply netN.opErrPtr_errAny $$ Hpe
  iapply HΦ
  iexists ys
  iframe Hp HS HeA
  ipureintro
  exact ⟨Hys.1, Hys.2, Himp⟩

end conn

end Perennial.gryff.lib
