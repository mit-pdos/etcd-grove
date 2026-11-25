/-
The net model's errors as error results (`bufio.errOrNil`, the vocabulary of the writers' and the
encoding/json model's `Encoder`'s specs): an `*OpError` (`net.opErr`) and a net operation's result
error (`net.resErr`). Moved from `Dsverify`'s vr kit (`network.opErr_errOrNil`,
`network.resErr_errOrNil`) for `encoding.json.Encoder.Encode`'s proof on a connection. Lemmas over
definitions only. Lean-first (no Rocq counterpart).
-/
module

public import Net.Proof.net.Errors
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

/-- An `*OpError` of the net model is an error result (`OpError.Error` returns some string; its
value is a pointer). -/
theorem opErr_errOrNil (op : GoString) (src addr e err : GoInterface) :
    net.opErr op src addr e err ⊢ bufio.errOrNil (GF := GF) err := by
  unfold net.opErr bufio.errOrNil
  iintro ⟨%pe, %nw, %he, #Hpe⟩
  obtain ⟨he, -⟩ := he
  subst he
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
    iapply net.wp_OpError_Error $$ Hpe
    inext
    iintro %msg -
    iapply HΦ
  · ipureintro
    intro e' h T hT
    simp [interface.mkOk] at h
    subst h
    exact ⟨_, rfl⟩

/-- A net operation's error (`net.resErr`) is an error result. -/
theorem resErr_errOrNil (res : Option NetErr) (op : GoString) (src addr : GoInterface)
    (ed : Option GoInterface) (nm : GoString → Prop) (err : GoInterface) :
    net.resErr (GF := GF) res op src addr ed nm err ⊢ bufio.errOrNil err := by
  cases res with
  | none =>
    unfold net.resErr bufio.errOrNil
    iintro %h; ileft; ipureintro; exact h
  | some k =>
    unfold net.resErr
    iintro ⟨%e, #Hop, -⟩
    iapply opErr_errOrNil $$ Hop

end lemmas

end net
end Perennial
