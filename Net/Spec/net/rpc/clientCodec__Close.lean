/-
`c.Close()` on the model's client codec `c` (`codec.go`), whose `rwc` holds the end `s` of the
connection `cn` (kept, `↦□`): the connection's `Close` (`net.Conn.Close.spec`), with the caller's
update `Q` over the end's state passed through. Proved in `Net/Proof/net/rpc/clientCodec__Close.lean`.
-/
module

public import Net.Spec.net.Conn__Close
public import Net.Proof.net.rpc.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net.rpc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]

/-- See the file header. -/
abbrev clientCodec.Close.spec : Prop :=
  ∀ (c t : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra : GoInterface)
    (Q : Option NetErr → IProp GF),
  {{ structFieldRef net.rpc.clientCodec go!"rwc" c ↦□
        interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t ∗
      net.connAt (GF := GF) t cn s a la ra ∗
      (|={⊤,∅}=> ∃ st d, netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st ∗
        netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn s d ∗
        ∀ res st' d', ⌜CloseOutcome st d res st' d'⌝ -∗
          netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st' -∗
          netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn s d' ={∅,⊤}=∗ Q res) }}
    (App (Val (c @!! go.GoType.PointerType net.rpc.clientCodec.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err;
      ∃ res, Q res ∗ net.resErr res go!"close" la ra none (· = go!"close") err }}

end spec

end net.rpc
end Perennial
