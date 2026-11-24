/-
`cr.Read(p)` (the model's `server.go`) while the server reads a request's head (`crHead`,
`ConnReaderHead.lean`: the main phase, the fields owned, the reader with its connection `c`, not
`nil`, the delivered bytes `r`): `p`'s first bytes `ys` (`sint.Z n = len(ys)`, at most `len(p)`) are
the connection's next bytes, the reader then at `r ++ ys`; no error, or an error (a pointer); a byte
or an error when `p` is not empty. At the read limit (`r` of length `L`) `io.EOF`; after an error
(`crHeadErr γe`) nothing (the net extension's sticky read errors, the end's read deadline not set). As `io.readerStreamNE`'s triple, for the server's
`bufio.Reader` (`conn.serve`'s `c.bufr`). Proved in `Net/Proof/net/http/connReader__Read.lean`.
-/
module

public import Net.Proof.net.http.ConnReaderHead
public import Net.Proof.net.Base
public import Proof.io.ReaderStream

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net.http

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]
variable [π : NetProtoGS]

/-- See the file header. -/
abbrev connReader.Read.spec : Prop :=
  ∀ (cr : Loc) (γ : CrNames) (t : Loc) (cn : Nat) (a : GoString) (la ra : GoInterface)
    (P Q : Proto GF) (hs : List w8) (Z : Nat → IProp GF) (L : Nat) (c : Loc) (γe : GName)
    (r : List w8) (p : GoSlice) (xs : List w8),
  {{ ⌜c ≠ null ∧ L < 2 ^ 62 ∧ r.length + xs.length < 2 ^ 62⌝ ∗
      crIs cr γ cn P hs Z ∗ readEnv ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗ crConnOk c ∗
      structFieldRef net.http.connReader go!"rwc" cr ↦□
        interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t ∗
      connAt t cn true a la ra ∗ crHead cr γ γe cn P Q L c r ∗ p ↦* xs }}
    (App (Val #(methods (go.GoType.PointerType net.http.connReader.ty) go!"Read" #cr)) (Val #p))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      ∃ ys : List w8, ⌜sint.Z n = ys.length ∧ ys.length ≤ xs.length ∧
          (xs ≠ [] → ys ≠ [] ∨ err ≠ interface.nil)⌝ ∗
        EtcdGrove.io.errAt (crHeadErr γe) (r ++ ys) err ∗
        p ↦* (ys ++ xs.drop ys.length) ∗ crHead cr γ γe cn P Q L c (r ++ ys) }}

end spec

end net.http
end Perennial
