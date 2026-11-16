/-
Lean-first (no Rocq counterpart). Laws of the trace event's `Properties` map representation
(`tracingPropsRep`, `InvTraceLogger.lean`), for the hooks' proofs: of raft's `with_tla` build only
(until the two builds were separated, in `TracedMsg.lean`).
-/
module

public import RaftTla.Proof.go_etcd_io.raft.v3.TracedMsg
public import RaftTla.Proof.go_etcd_io.raft.v3.InvTraceLogger

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The properties' representation reads only the event's three properties. -/
theorem tracingPropsRep_congr (m : GoMap) (e e' : TraceEv) (h1 : e.propCC = e'.propCC)
    (h2 : e.propMatch = e'.propMatch) (h3 : e.propNext = e'.propNext) :
    tracingPropsRep (GF := GF) m e ⊣⊢ tracingPropsRep m e' := by
  unfold tracingPropsRep
  rw [h1, h2, h3]
  exact .rfl

/-- ... as a wand. -/
theorem tracingPropsRep_of (m : GoMap) (e e' : TraceEv) (h1 : e.propCC = e'.propCC)
    (h2 : e.propMatch = e'.propMatch) (h3 : e.propNext = e'.propNext) :
    ⊢ tracingPropsRep (GF := GF) m e' -∗ tracingPropsRep m e := by
  iintro H
  iapply (tracingPropsRep_congr m e e' h1 h2 h3).2
  iexact H

/-- A nil `prop`. -/
theorem tracingPropsRep_nil : ⊢ tracingPropsRep (GF := GF) map.nil noProps := by
  unfold tracingPropsRep
  ileft
  isplitr <;> ipureintro
  · rfl
  · exact ⟨rfl, rfl, rfl⟩

/-- An empty, read-only `prop` (`traceSendMessage`'s map with no `Progress`). -/
theorem tracingPropsRep_empty (m : GoMap) :
    (m ↦$□ (∅ : GMap GoString GoInterface) : IProp GF) ⊢ tracingPropsRep m noProps := by
  iintro #Hm
  unfold tracingPropsRep
  iright
  iexists ∅, null
  iframe Hm
  isplitr
  · ipureintro
    simp [noProps]
  · simp only [noProps, tracingCCRep]; ipureintro; trivial

/-- `prop` with the sender's `match` and `next` (`traceSendMessage`'s map for a `MsgApp`). -/
theorem tracingPropsRep_mn (m : GoMap) (mt nx : w64) :
    (m ↦$□ (<[go!"next" := interface.mkOk go.uint64 #nx]>
        (<[go!"match" := interface.mkOk go.uint64 #mt]> (∅ : GMap GoString GoInterface))) : IProp GF) ⊢
      tracingPropsRep m { noProps with propMatch := some mt, propNext := some nx } := by
  iintro #Hm
  unfold tracingPropsRep
  iright
  iexists _, null
  iframe Hm
  have hnm : (go!"next" : GoString) ≠ go!"match" := by decide
  have hnc : (go!"next" : GoString) ≠ go!"cc" := by decide
  have hmc : (go!"match" : GoString) ≠ go!"cc" := by decide
  have hinj : ∀ a b : w64, (#a : val) = #b → a = b := fun a b h => go.IntoValInj.intoVal_inj h
  isplitr
  · ipureintro
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [noProps]
    · intro _
      simp
    · intro w
      simp only [GMap.lookup_insert_ne _ _ hnm, GMap.lookup_insert]
      constructor
      · intro h; cases h; rfl
      · intro h
        have h' := (interface_mkOk_inj _ _ _ _).1 (Option.some.inj h)
        rw [hinj _ _ h'.2]
    · simp
    · intro w
      simp only [GMap.lookup_insert]
      constructor
      · intro h; cases h; rfl
      · intro h
        have h' := (interface_mkOk_inj _ _ _ _).1 (Option.some.inj h)
        rw [hinj _ _ h'.2]
    · simp
    · intro k hk
      have hk1 : k ≠ go!"next" := fun h => hk (by simp [h])
      have hk2 : k ≠ go!"match" := fun h => hk (by simp [h])
      rw [GMap.lookup_insert_ne _ _ (Ne.symm hk1), GMap.lookup_insert_ne _ _ (Ne.symm hk2)]
      rfl
  · simp only [noProps, tracingCCRep]; ipureintro; trivial

end defs

end EtcdGrove
end Perennial
