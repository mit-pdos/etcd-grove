/-
The net model's errors as error results (`bufio.errOrNil`, the vocabulary of the writers' and the
encoding/json model's `Encoder`'s specs): an `*OpError` (`net.opErr`) and a net operation's result
error (`net.resErr`). Moved from `Dsverify`'s vr kit (`network.resErr_errOrNil`) for `encoding.json.Encoder.Encode`'s proof on a connection. Lemmas over
definitions only. Lean-first (no Rocq counterpart).
-/
module

public import Net.Proof.net.Errors
public import Net.Proof.net.OpErrorMsg
public import Proof.bufio.ErrOrNil

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [net.Assumptions]

/-- A net operation's error (`net.resErr`) is an error result: `nil`, or an `*OpError` whose
`Error()` returns some string (Go's `OpError.Error`, `wp_OpError_Error`, which needs `syscall`'s
error table, `syscall.errnoOk`: since the Go-model net, 2026-11-25, an `*OpError`'s message is
Go's, built from its `Err`'s; `net.connAt_errnoOk` gives it from a connection). -/
theorem resErr_errOrNil (res : Option NetErr) (op : GoString) (src addr : GoInterface)
    (ed : Option GoInterface) (nm : GoString → Prop) (err : GoInterface) :
    syscall.errnoOk (GF := GF) ⊢ net.resErr res op src addr ed nm err -∗ bufio.errOrNil err := by
  cases res with
  | none =>
    unfold net.resErr bufio.errOrNil
    iintro #_ %h; ileft; ipureintro; exact h
  | some k =>
    unfold net.resErr
    iintro #Hsys ⟨%e, #Hop, -, #Hes, #Hs, #Ha⟩
    unfold net.opErr bufio.errOrNil
    icases Hop with ⟨%pe, %nw, %he, #Hpe⟩
    obtain ⟨he, -⟩ := he
    subst he
    ihave #Hok : net.opErrMsgOk (GF := GF) (OpError.mk op nw src addr e) $$ []
    · unfold net.opErrMsgOk
      iframe Hes Hs Ha
    iright
    isplitl
    · unfold models_lab.errAny
      iexists _
      isplitr
      · ipureintro; rfl
      isplitr
      · ipureintro; go_type_set
      imodintro
      iintro %Φ HΦ
      iapply net.wp_OpError_Error $$ Hpe Hok Hsys
      inext
      iintro %msg -
      iapply HΦ
    · ipureintro
      intro e' h T hT
      simp [interface.mkOk] at h
      subst h
      exact ⟨_, rfl⟩

end lemmas

end net
end Perennial
