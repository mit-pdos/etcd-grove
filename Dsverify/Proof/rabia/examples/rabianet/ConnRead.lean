/-
(Specs and the connection lemma; `ConnReadFull.lean` holds the proof.)
`io.ReadFull` over a reader whose contract asks a condition only of reads that `ReadAtLeast` makes
(`ys.length < xs.length`: it reads only while it has fewer bytes than asked), such as a
connection's (`net.conn_readerOk`: a non-empty buffer): `io.ReadFull.specLt`, Perennial's
`io.ReadFull.spec` since the pin bump to Perennial `580868e54` (2026-11-24, which has branch
`readatleast-prefix`; until then a local copy of that branch's spec, with a copy of its proof); then
`wp_connReadFull`, a connection end's `io.ReadFull` (the kit's `sendConf` and `awaitConf` read a
connection with `io.ReadFull` directly).
-/
module

public import Perennial.Spec.io.ReadAtLeast
public import Perennial.Spec.io.ReadFull
public import Net.Proof.net.ConnIo
public import Net.Spec.net.Conn__Read

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.rabia.examples.rabianet

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `io.ReadFull.spec` with the condition asked only below the buffer's length: Perennial's own
since the pin bump to Perennial `580868e54` (2026-11-24, branch `readatleast-prefix` landed). -/
abbrev io.ReadFull.specLt : Prop := _root_.Perennial.io.ReadFull.spec (GF := GF) (hG := hG)

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
        p ↦* (ys ++ xs.drop ys.length) ∗ recvTokL (Gg := hG.goose_globalGS) cn s P (r0 ++ ys) }} := by
  iintro %Φ ⟨#Hio, #Hc, #Hed, HS, Hp⟩ HΦ
  ihave #Hi := _root_.Perennial.io.isInit_access $$ Hio
  icases Hi with ⟨-, -, -, -, #HEOF, #HUEOF, -⟩
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
  iapply HΦ
  iexists ys
  iframe Hp HS
  ipureintro
  exact ⟨Hys.1, Hys.2, Himp⟩

end conn

end Perennial.rabia.examples.rabianet
