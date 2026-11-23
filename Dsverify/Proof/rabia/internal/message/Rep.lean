/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/message/Spec.lean`, run
`rabia-r1wake-1`: its representations, without the specs over `bufio`, which wait for the shared
bufio change; `Spec.lean` will import this file.)

`rabia/internal/message`'s representations: a Go `ConsensusObj`, `Msg` or `Command` value holds
the record `ObjV`, `MsgV` or `CmdV` (`Core/Model.lean`), its slices read-only (`↦*□`: Rabia never
changes a message after making it; `Unmarshal` makes fresh slices).
-/
module

public import Dsverify.Proof.rabia.Core.Model
public import Dsverify.GeneratedProof.rabia.internal.message

@[expose] public section

noncomputable section

namespace Perennial.rabia.internal.message

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

instance : Pos.Countable Msg :=
  countableOfLeftInverse (B := w32 × w32 × w32 × Loc)
    (fun m => (m.Type', m.Phase', m.Value', m.Obj'))
    (fun (a, b, c, d) => ⟨a, b, c, d⟩)
    (fun _ => rfl)
instance : Pos.Countable Command :=
  countableOfLeftInverse (B := w32 × w32 × w32 × GoSlice)
    (fun c => (c.CliId', c.CliSeq', c.SvrSeq', c.Commands'))
    (fun (a, b, c, d) => ⟨a, b, c, d⟩)
    (fun _ => rfl)
instance : Pos.Countable ConsensusObj :=
  countableOfLeftInverse (B := w32 × w32 × w32 × Bool × GoSlice × GoSlice × GoSlice)
    (fun o => (o.ProId', o.ProSeq', o.SvrSeq', o.IsNull', o.CliIds', o.CliSeqs', o.Commands'))
    (fun (a, b, c, d, e, f, g) => ⟨a, b, c, d, e, f, g⟩)
    (fun _ => rfl)

/-- The Go value `v` of a `ConsensusObj` holds `o` (its slices read-only, persistent). -/
def objRep (v : ConsensusObj) (o : ObjV) : IProp GF :=
  iprop(⌜v.ProId' = o.proId ∧ v.ProSeq' = o.proSeq ∧ v.SvrSeq' = o.svrSeq ∧ v.IsNull' = o.isNull⌝ ∗
    v.CliIds' ↦*□ o.cliIds ∗ v.CliSeqs' ↦*□ o.cliSeqs ∗ v.Commands' ↦*□ o.commands)

/-- The Go value `v` of a `Msg` holds `m` (its object, if any, read-only). -/
def msgRep (v : Msg) (m : MsgV) : IProp GF :=
  iprop(⌜v.Type' = m.ty ∧ v.Phase' = m.phase ∧ v.Value' = m.value⌝ ∗
    match m.obj with
    | none => ⌜v.Obj' = null⌝
    | some o => ∃ ov, v.Obj' ↦□ ov ∗ objRep ov o)

/-- The Go value `v` of a `Command` holds `c`. -/
def cmdRep (v : Command) (c : CmdV) : IProp GF :=
  iprop(⌜v.CliId' = c.cliId ∧ v.CliSeq' = c.cliSeq ∧ v.SvrSeq' = c.svrSeq⌝ ∗
    v.Commands' ↦*□ c.commands)

instance objRep_persistent (v : ConsensusObj) (o : ObjV) : Persistent (objRep (GF := GF) v o) :=
  by unfold objRep; infer_instance
instance msgRep_persistent (v : Msg) (m : MsgV) : Persistent (msgRep (GF := GF) v m) := by
  unfold msgRep; cases m.obj <;> infer_instance
/-- The scalar fields of a represented message (a law). -/
theorem msgRep_fields (v : Msg) (m : MsgV) :
    msgRep (GF := GF) v m ⊢ ⌜v.Type' = m.ty ∧ v.Phase' = m.phase ∧ v.Value' = m.value⌝ := by
  unfold msgRep; iintro ⟨%h, -⟩; ipureintro; exact h

/-- The scalar fields of a represented object (a law: clients do not unfold `objRep`). -/
theorem objRep_fields (v : ConsensusObj) (o : ObjV) :
    objRep (GF := GF) v o ⊢ ⌜v.ProId' = o.proId ∧ v.ProSeq' = o.proSeq ∧ v.SvrSeq' = o.svrSeq ∧
      v.IsNull' = o.isNull⌝ := by
  unfold objRep; iintro ⟨%h, -⟩; ipureintro; exact h

instance cmdRep_persistent (v : Command) (c : CmdV) : Persistent (cmdRep (GF := GF) v c) :=
  by unfold cmdRep; infer_instance

end defs

end Perennial.rabia.internal.message
