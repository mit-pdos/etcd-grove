/- Lean-first (no Rocq counterpart).

# `net/rpcdriver`: the driver's own predicates

* **The package's variables** (`drvFacts`, persistent): `failMsgs` holds the slice of the method's
  messages (`failList`, the driver's: `"driver: ..."`), and `reached` a function whose calls return
  (its body is empty). The package's `isPkgInit` fact is `True` (generated `Init.lean`); the boot's
  first initialization of the package returns `drvFacts` (`InitFirst.lean`).
* **The client's ids** (`isCtr γid γb c`, persistent): the `counter` `c`'s mutex owns its `next`
  field, the authority of the ids issued so far (the ghost map `γid`: `issued start n`, the ids
  `start`, ..., `start + n - 1`, wrapping) and a budget: the take credits handed out (`ownToks γb`,
  `Perennial/Proof/TokSet.lean`) and `n` together never exceed `ctrBudget` (`132`: at most 4 dials of
  at most 4 workers making at most 8 calls, and one call after each `Close`). So the `n` ids are
  distinct (`n < 2 ^ 64`), and `take` hands out the token `idTok γid id` of a fresh id
  (`Svc.lean`).
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.Svc
public import Net.GeneratedProof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver
public import Perennial.Proof.TokSet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.net.rpcdriver

/-- The method's messages (`failMsgs`). -/
def failList : List GoString :=
  [go!"driver: no such key", go!"driver: not leader", go!"driver: x"]

/-- The marker of the method's messages (`isFailMsg`). -/
def driverMark : GoString := go!"driver: "

theorem failList_marked (m : GoString) (h : m ∈ failList) : driverMark <+: m := by
  simp only [failList, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> decide

/-- None of net/rpc's own error answers is marked as the method's. -/
theorem srvErrMsg_not_marked (msg : GoString) (h : net.rpc.srvErrMsg msg) :
    ¬ driverMark <+: msg := by
  rintro ⟨t, ht⟩
  have hd : msg.head? = some (W8 100) := by
    rw [← ht]
    simp only [driverMark, List.cons_append, List.head?_cons] <;> try decide
  unfold net.rpc.srvErrMsg net.rpc.rdErrMsg net.opErrMsg at h
  rcases h with ⟨sm, rfl⟩ | ⟨sm, rfl⟩ | ⟨sm, rfl⟩ | rfl | rfl | rfl | rfl | ⟨s1, s2, rfl⟩ <;>
    simp only [List.cons_append, List.head?_cons, Option.some.injEq, List.append_assoc] at hd <;>
    revert hd <;> decide

/-- The bound on the ids the client takes (see the file header). -/
def ctrBudget : Nat := 132

/-- The ids `start`, ..., `start + n - 1`. -/
def issued (start : w64) : Nat → GMap w64 Unit
  | 0 => ∅
  | n + 1 => (issued start n).insert (start + W64 n) ()

/-- The next id is fresh while fewer than `2 ^ 64` were issued. -/
theorem issued_fresh (start : w64) : ∀ (n j : Nat), n ≤ j → j < 2 ^ 64 →
    (issued start n).lookup (start + W64 j) = none
  | 0, _, _, _ => rfl
  | n + 1, j, h1, h2 => by
    simp only [issued]
    rw [GMap.lookup_insert_ne _ _ ?_]
    · exact issued_fresh start n j (by omega) h2
    · intro h
      have h' : (W64 n : w64) = W64 j := by
        have := congrArg (fun x => x - start) h
        simpa using this
      word

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The package's variables (see the file header). -/
def drvFacts : IProp GF :=
  iprop((∃ sl : GoSlice, globalAddr failMsgs ↦□ sl ∗ sl ↦*□ failList) ∗
    (∃ f : GoFunc, globalAddr reached ↦□ f ∗
      □ ∀ s : GoString, WP (App (Val #f) (Val #s)) {{ v, ⌜v = #()⌝ }}))

instance drvFacts_persistent : Persistent (drvFacts (GF := GF)) := by
  unfold drvFacts; infer_instance

/-- The counter's invariant (see the file header). -/
def ctrInv (γid γb : GName) (start : w64) (c : Loc) : IProp GF :=
  iprop(∃ n k : Nat, structFieldRef counter go!"next" c ↦ (start + W64 n) ∗
    ghostMapAuth (K := w64) (V := Unit) γid 1 (issued start n) ∗ ownTokAuth γb k ∗
    ⌜n + k ≤ ctrBudget⌝)

/-- `c` is the client's counter of ids (persistent; see the file header). -/
def isCtr (γid γb : GName) (c : Loc) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.sync ∗
    ∃ start : w64, sync.isMutex (structFieldRef counter go!"mu" c) (ctrInv γid γb start c))

instance isCtr_persistent (γid γb : GName) (c : Loc) : Persistent (isCtr (GF := GF) γid γb c) := by
  unfold isCtr; infer_instance

end defs

end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver

end Perennial
