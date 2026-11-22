-- The copy for the part `KvNet/` of `Net/Spec/net/Conn__Close.lean` (etc/copy-part.py; rerun it, do not edit).
/-
`c.Close()` on a `Conn` `c` that is the end `s` of a TCP connection `cn` (`connAt`, with the end's
addresses `la`, `ra`), through the interface (`conn.Close.impl`, promoted): the extension's
`Close`, whose outcome (`CloseOutcome`, `GooseLang/Ext/Net/Impl.lean`, D3, D17: the end closed, its
direction shut if open, success; `closed` if closed already) the caller takes by a logically atomic
update over the end's state and the direction from it (`netEnd`, `netDir`). Its result `Q res` is
handed back with the error: `nil` for success, else the `*OpError{Op: "close", Source: la, Addr:
ra}` of the failure's kind (`resErr`; no timeout). Proved in `Net/Proof/net/Conn__Close.lean`.
-/
module

public import KvNet.Proof.net.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions] [field_sem : net.FieldAssumptions]

/-- See the file header. -/
abbrev Conn.Close.spec : Prop :=
  ∀ (t : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra : GoInterface)
    (Q : Option NetErr → IProp GF),
  {{ connAt (GF := GF) t cn s a la ra ∗
      (|={⊤,∅}=> ∃ st d, netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st ∗ netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn s d ∗
        ∀ res st' d', ⌜CloseOutcome st d res st' d'⌝ -∗ netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st' -∗
          netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn s d' ={∅,⊤}=∗ Q res) }}
    (App (Val #(methods (go.GoType.PointerType TCPConn.ty) go!"Close" #t)) (Val #()))
  {{ (err : GoInterface), RET #err;
      ∃ res, Q res ∗ resErr res go!"close" la ra none (· = go!"close") err }}

end spec

end net
end Perennial
