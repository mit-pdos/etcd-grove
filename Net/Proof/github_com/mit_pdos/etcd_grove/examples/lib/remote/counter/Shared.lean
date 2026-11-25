/-
# remote's counter instance: what the machines share (R4)

- The masks: node 0's invariant (`pendN`), lintest's (`lintestN`) and the server's (`syncN`, the
  operation's mask `(cR γ).Eop`) are disjoint (`pendN_syncN`, `lintestN_disj`).
- The server's system resource `srvTok γs sys` (`opMaybe`'s `tok`): `sys` is its `*Counter`, whose
  state (`counterState γc`, `Counter.Apply`'s) the invariant `syncInv` keeps equal to the start's
  ghost variable `γs` (the store's `sysState`).
- `lin_mono`: an update with a result gives one with none (a client node's unknown branch).
- `remoteGF`: the deployment's ghost state, `netGF` with a slot for iris-lean's non-atomic
  invariants (porcupine's, `NaInvG`), as lintest/counter's `counterGF`.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.counter.Defs
public import GooseLang.Ext.Net.Adequacy

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote.counter

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote

/-! ## Masks -/

theorem pendN_syncN : (↑pendN : CoPset) ⊆ ⊤ \ ↑syncN := by
  intro p hp
  have h1 := nclose_subseteq (nroot.@"remote") "pend" p hp
  exact mask_ndot_ne' nroot "remote" "remote_counter_sync" (by decide) p h1

theorem lintestN_disj : (↑lintest.lintestN : CoPset) ⊆ ⊤ \ (↑syncN ∪ ↑pendN) := by
  intro p hp
  change p ∈ (↑(nroot.@"lintest") : CoPset) at hp
  rw [LawfulSet.mem_diff, LawfulSet.mem_union, not_or]
  refine ⟨CoPset.mem_full, ?_, ?_⟩
  · intro h
    exact ndot_ne_disjoint nroot (show "lintest" ≠ "remote_counter_sync" by decide) p ⟨hp, h⟩
  · intro h
    have h1 := nclose_subseteq (nroot.@"remote") "pend" p h
    exact ndot_ne_disjoint nroot (show "lintest" ≠ "remote" by decide) p ⟨hp, h1⟩

/-! ## The server's system -/

section srv
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [lc_sem : github_com.mit_pdos.etcd_grove.examples.lib.lintest.counter.Assumptions]

/-- The start's ghost variable and the counter's, equal. -/
def syncInv (γs γc : GName) : IProp GF :=
  inv syncN iprop(∃ n : w64, ghostVar γs (1 : Qp).half n ∗ lintest.counter.counterState γc n)

instance syncInv_persistent (γs γc : GName) : Persistent (syncInv (GF := GF) γs γc) := by
  unfold syncInv; infer_instance

/-- The server's system: its `*Counter`, in step with the start's ghost variable. -/
def srvTok (γs : GName) (sys : GoInterface) : IProp GF :=
  iprop(∃ (c : Loc) (γc : GName), ⌜sys = interface.mkOk (go.GoType.PointerType
      github_com.mit_pdos.etcd_grove.examples.lib.lintest.counter.Counter.ty) #c⌝ ∗
    lintest.counter.isCounter γc c ∗ syncInv γs γc ∗
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.lintest.counter)

end srv

/-! ## Updates -/

section lin
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF]
variable {St J I O : Type} [Pos.Countable I] [Pos.Countable O]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem lin_mono (R : RBase GF St J I O) (i : I) (Φ Ψ : O → IProp GF) :
    (∀ o, Φ o ⊢ Ψ o) → lin (Gg := Gg) R i Φ ⊢ lin (Gg := Gg) R i Ψ := by
  intro h
  unfold lin
  refine (Iris.BI.and_intro Iris.BI.true_intro .rfl).trans (aupd_intro ?_)
  iintro ⟨-, HL⟩
  ihave HL := aupd_aacc $$ HL
  iapply atomic_acc_wand $$ [] HL
  isplit
  · iintro H
    iexact H
  · isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
    iintro %st H
    iapply h $$ H

end lin

/-! ## The ghost state -/

section gf
attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet

/-- `netGF` with iris-lean's non-atomic invariants at slot 8. -/
def remoteGF : BundledGFunctors := fun
  | 0 => ⟨AllURF, inferInstance⟩
  | 1 => ⟨InvMapF, inferInstance⟩
  | 2 => ⟨constOF CoPsetDisjL, inferInstance⟩
  | 3 => ⟨constOF (DisjointLeibnizSet PosSet), inferInstance⟩
  | 4 => ⟨Auth.AuthURF (constOF Credit), inferInstance⟩
  | 5 => ⟨constOF (NaHeapUR Loc val), inferInstance⟩
  | 6 => ⟨constOF (HeapView proph_id (Agree (DiscreteO (List val))) (GMap proph_id)), inferInstance⟩
  | 7 => ⟨GhostVarF (GMap GoString Bool), inferInstance⟩
  | 8 => ⟨NaInvF, inferInstance⟩
  | _ => ⟨constOF Unit, inferInstance⟩

instance remoteGpreS : GooseGpreS remoteGF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGExts := (⟨allGOfSlot 0 rfl⟩, PUnit.unit)
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goosePreGAllG := allGOfSlot 0 rfl

instance remoteGF_naInvG : NaInvG remoteGF := ⟨⟨8, rfl⟩⟩

end gf

end github_com.mit_pdos.etcd_grove.examples.lib.remote.counter
end Perennial
