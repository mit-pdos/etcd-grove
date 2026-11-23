/-
`cr.Read(p)`, the model's `connectReader` (`models/net/rpc/client.go`) over the dialer's end of a
connection to `a` in `W` before any request (`crAt`, `crSt`, `HttpDefs.lean`), the end's reader
at `r`: `p`'s first bytes `ys` (`sint.Z n = len(ys)`, at most `len(p)`) are the connection's next
bytes, `cr` then at `r ++ ys`, still a prefix of the answer `connectAns` or of net/http's `400`
answer `badReqAns`; and no error, or an error
(`crErr`: `cr` failed at `r ++ ys`, which it stays at); a byte or an error when `p` is not empty.
As `io.readerStreamNE`'s triple, for `DialHTTPPath`'s `bufio.Reader`. Proved in `Net/Proof/net/rpc/connectReader__Read.lean`.
-/
module

public import Net.Proof.net.rpc.HttpDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net.rpc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

/-- See the file header. -/
abbrev connectReader.Read.spec : Prop :=
  ∀ (W : RpcWorld GF) (a : GoString) (cn : Nat) (γ : RpcConnNames) (cr t : Loc)
    (la ra : GoInterface) (γe : GName) (r : List w8) (p : GoSlice) (xs : List w8)
    (ed : GoInterface),
  {{ ⌜W.hsAns a = connectAns⌝ ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
      globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗
      crAt cr t cn a la ra ∗ crSt W a cn γ cr γe r ∗ p ↦* xs }}
    (App (Val #(methods (go.GoType.PointerType net.rpc.connectReader.ty) go!"Read" #cr)) (Val #p))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      ∃ ys : List w8, ⌜sint.Z n = ys.length ∧ ys.length ≤ xs.length ∧
          (xs ≠ [] → ys ≠ [] ∨ err ≠ interface.nil)⌝ ∗
        EtcdGrove.io.errAt (crErr γe) (r ++ ys) err ∗
        p ↦* (ys ++ xs.drop ys.length) ∗ crSt W a cn γ cr γe (r ++ ys) }}

end spec

end net.rpc
end Perennial
