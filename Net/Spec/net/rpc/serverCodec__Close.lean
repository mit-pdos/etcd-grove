/-
`c.Close()` on the model's server codec `c` (`codec.go`), whose `rwc` holds the end `s` of the
connection `cn` (kept, `↦□`) and whose `closed` flag the caller owns (`b`): once closed, `nil` and
nothing else; otherwise `closed` set and the connection's `Close` (`net.Conn.Close.spec`), with the
caller's update `Q` over the end's state passed through. Proved in
`Net/Proof/net/rpc/serverCodec__Close.lean`.
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
abbrev serverCodec.Close.spec : Prop :=
  ∀ (c t : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra : GoInterface) (b : Bool)
    (Q : Option NetErr → IProp GF),
  {{ structFieldRef net.rpc.serverCodec go!"rwc" c ↦□
        interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t ∗
      net.connAt (GF := GF) t cn s a la ra ∗ structFieldRef net.rpc.serverCodec go!"closed" c ↦ b ∗
      (if b then iprop(True) else
        |={⊤,∅}=> ∃ st d, netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st ∗
          netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn s d ∗
          ∀ res st' d', ⌜CloseOutcome st d res st' d'⌝ -∗
            netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st' -∗
            netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn s d' ={∅,⊤}=∗ Q res) }}
    (App (Val (c @!! go.GoType.PointerType net.rpc.serverCodec.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err; structFieldRef net.rpc.serverCodec go!"closed" c ↦ true ∗
      (if b then iprop(⌜err = interface.nil⌝) else
        ∃ res, Q res ∗ net.resErr res go!"close" la ra none (· = go!"close") err) }}

end spec

end net.rpc
end Perennial
