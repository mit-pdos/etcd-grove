/-
`c.Write(b)` on a `Conn` `c` that is the end `s` of a TCP connection `cn` (`connAt`, with the end's
addresses `la`, `ra`), through the interface (`conn.Write.impl`, promoted): Go's loop of steps (D2,
D15, `GooseLang/Ext/Net/Impl.lean`), each the extension's `Write` of the bytes not yet written. The
caller makes the steps through a writer predicate `P w res` (`w`: the bytes this call has written
so far, a prefix of `b`'s `bs`; `res`: the last step's result, `none` while no step failed; `P []
none` given) and an accessor (persistent: it is used once per step), which opens the end's state and
the direction from it (`netEnd`, `netDir`) for a step on the bytes `rs` not yet written
(`w ++ rs = bs`) and closes them at what the step left (`WriteOutcome`), giving `P` of the bytes
written then and the step's result. `b`'s bytes are read (any fraction) and kept.

It returns `(len w, nil)` once every byte is written (`res = none`, `w = bs`), else `(len w, err)`
at the first failing step, `err` the `*OpError{Op: "write", Source: la, Addr: ra}` of the failure's
kind (`resErr`, D14): fewer bytes than asked only with an error, and an error with every byte
written only for an empty `b` (whose one step may fail). Proved in
`Net/Proof/net/Conn__Write.lean`.
-/
module

public import Net.Proof.net.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions]

/-- See the file header. -/
abbrev Conn.Write.spec : Prop :=
  ∀ (t : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra : GoInterface) (b : GoSlice)
    (bs : List w8) (dq : DFrac) (ed : GoInterface) (P : List w8 → Option NetErr → IProp GF),
  {{ connAt (GF := GF) t cn s a la ra ∗ b ↦*{dq} bs ∗
      globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗ P [] none ∗
      □ (∀ (w rs : List w8), ⌜w ++ rs = bs⌝ -∗ P w none -∗
        |={⊤,∅}=> ∃ st d, netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st ∗ netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn s d ∗
          ∀ k res d', ⌜WriteOutcome st d rs k res d'⌝ -∗ netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st -∗
            netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn s d' ={∅,⊤}=∗ P (w ++ rs.take k) res) }}
    (App (Val #(methods (go.GoType.PointerType TCPConn.ty) go!"Write" #t)) (Val #b))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      ∃ w res, P w res ∗ b ↦*{dq} bs ∗
        ⌜w <+: bs ∧ n = BitVec.ofNat 64 w.length ∧ (res = none → w = bs) ∧
          (w = bs → res = none ∨ bs = [])⌝ ∗
        resErr res go!"write" la ra (some ed) (· = go!"write") err }}

end spec

end net
end Perennial
