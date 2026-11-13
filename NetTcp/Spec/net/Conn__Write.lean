/-
`c.Write(b)` on a `Conn` `c` that is the end `s` of a TCP connection `cn` (`isConn`), through the
interface (`conn.Write.impl`, promoted): `b`'s bytes read (any fraction), then the extension's
`Write`, whose outcome the caller takes by a logically atomic update over the end's state and its
written bytes (`tcpEnd`, `tcpOut`; `WriteRes`). Its result `Q k ok` is handed back with what the
call returns: `(k, nil)` if all was written (`ok`), else `(k, err)` with an `*OpError`. Proved in
`NetTcp/Proof/net/Conn__Write.lean`.
-/
module

public import NetTcp.Proof.net.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Tcp

namespace net

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions] [field_sem : net.FieldAssumptions]

/-- See the file header. -/
abbrev Conn.Write.spec : Prop :=
  ∀ (t : Loc) (cn : Nat) (s : Bool) (a : GoString) (b : GoSlice) (bs : List w8)
    (dq : DFrac) (Q : Nat → Bool → IProp GF),
  {{ connAt (GF := GF) t cn s a ∗ b ↦*{dq} bs ∗
      (|={⊤,∅}=> ∃ st r out f, tcpEnd (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn s st r ∗
        tcpOut (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn s out f ∗
        ∀ k ok st', ⌜WriteRes st bs k ok st'⌝ -∗
          tcpEnd (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn s st' r -∗
          tcpOut (extGlobalGS tcpExt (G := hG.goose_globalGS)) cn s (out ++ bs.take k) f
          ={∅,⊤}=∗ Q k ok) }}
    (App (Val #(methods (go.GoType.PointerType TCPConn.ty) go!"Write" #t)) (Val #b))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      ∃ k ok, Q k ok ∗ b ↦*{dq} bs ∗
        ⌜n = BitVec.ofNat 64 k ∧ (ok = true → err = interface.nil) ∧ (ok = false → netErr err)⌝ }}

end spec

end net
end Perennial
