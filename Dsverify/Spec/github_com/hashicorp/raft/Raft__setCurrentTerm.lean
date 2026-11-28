/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__setCurrentTerm.lean (241f27e).
-/
/-
`raft.(*Raft).setCurrentTerm`'s spec (raft-internal interface, notes/raft-iface.md). Persists the term (stable store) and stores it in the `currentTerm` atomic, where the protocol step happens. (hraft_robust R4a) The main goroutine's stable view keeps its staged commit index `g` (`stVS`). (hraft_robust L0, R1 §2.3) The step is `tp`, adopting `t` (`setTerm_upd`, with `termOk`) or an election (`electTerm_upd`, with a receipt); from `SetUint64`'s commit point to the atomic store it is pending in `srvDurInv` (fired by a crash).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Laws

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open github_com.hashicorp.raft github_com.hashicorp.raft.gprot github_com.hashicorp.raft.proto

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- `(*Raft).setCurrentTerm`: Persists the term (stable store) and stores it in the `currentTerm` atomic, where the protocol step happens. (hraft_robust L0, R1 §2.3) The step is `tp`, adopting `t` (`setTerm_upd`, with `termOk`) or an election (`electTerm_upd`, with a receipt); from `SetUint64`'s commit point to the atomic store it is pending in `srvDurInv` (fired by a crash). -/
abbrev github_com.hashicorp.raft.Raft.setCurrentTerm.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (sst : StableAbs) (g : w64) (t : w64)
    (tp : TermPend),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
     srvV rc s ∗ stVS rc sst g ∗ tpRes γ (some tp) ∗
     ⌜(tp = .set (uint.nat t) ∧ s.term ≤ uint.nat t) ∨ (tp = .elect ∧ uint.nat t = s.term + 1)⌝ }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"setCurrentTerm")) (Val #t))
  {{ RET #(); srvV rc { s with term := uint.nat t } ∗ termLb γ i (uint.nat t) ∗
      stVS rc { sst with ints := sst.ints.insert (go!"CurrentTerm" : List w8) t } g ∗
      (match tp with
        | .set _ => iprop(True)
        | .elect => iprop(candIs γ i (s.term + 1) s.log.length (lastTerm s.log) ∗
            pubOwn γ i (s.term + 1) 0 ∗ ccfgOwn γ i (s.term + 1) 0 ∗ ccfgOwn γ i (s.term + 1) 0)) }}

end spec

end Perennial
