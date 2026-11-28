/-
Lean-first (no Rocq counterpart).

# `SharedModel`'s model and representation (k8s-dist K9 step 4, `notes/k8s-dist-k9.md` §2.1)

- `GoStep R mode c x y e`: one step of `SharedModel`'s `Step` from the configuration `c` on the
  operation `(x, y)` reaches `e`. In mode `Lazy` (0), `c` skipped to the operation's target
  (`targetL`) steps if `stepL` allows it anything; otherwise (and in every other mode) a configuration
  `settle` reaches from `c` (`GoSettle`, `Full` = mode 2) skipped to its target, then `stepL`. The
  model's step reads the output as it is (`y`), `stepL` its plain part (`plainOut y`, as `step`);
- `sharedM g0 R mode`: the model's states are sets of configurations (`GCfg → Prop`), from `{⟨g0, []⟩}`; a step
  keeps every `GoStep` of every configuration, and fails when none is left;
- `SharedBounded B k g`: a configuration of a state made by `k` steps from `g0` is well formed
  (`HWf`), its pending inputs are writes, its revision with its pending writes is at most `2^62 + k`
  (a step lands a write at a revision the operation, `R` or one past the revision names, all below
  `2^62`, or adds one pending write or one revision), and its items with its pending writes at
  most `B + k` (`B` the seeded store's items);
- `RevsBelow x y`: every revision the operation names (`OpAnchors`, and the answer's revision) is
  below `2^62`; `RevsLBelow R`: `R`'s revisions are. (Below `2^62`, not etcd's `2^63`: `settle`
  needs room above a landing for the pending writes, `SettleOk`.)
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.WMemo
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.SharedLand
public import Proof.github_com.anishathalye.porcupine.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI
open k8s_dist
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj Revs mcfg)

section pure
variable [GooseExts]

/-- One step of `SharedModel`'s `Step` from `c` (see the file header). -/
def GoStep (R : RevsL) (mode : Nat) (c : GCfg) (x : Input) (y : Output) (e : GCfg) : Prop :=
  let lazy := stepL ⟨skipToL c.st (targetL x y (uint.nat c.st.st.rv)), c.pend⟩ x (plainOut y)
  if mode = 0 ∧ lazy ≠ [] then e ∈ lazy
  else ∃ d, GoSettle R (boundL x y) (mode = 2) x y c d ∧
    e ∈ stepL ⟨skipToL d.st (targetL x y (uint.nat d.st.st.rv)), d.pend⟩ x (plainOut y)

/-- Every revision `x` and `y` name is below `2^62` (see the file header). -/
def RevsBelow (x : Input) (y : Output) : Prop :=
  OpAnchors (List.range (2 ^ 62)) x y ∧ uint.nat y.RV' < 2 ^ 62

/-- `R`'s revisions are below `2^62`. -/
def RevsLBelow (R : RevsL) : Prop :=
  (∀ a ∈ R.anchors, uint.nat a < 2 ^ 62) ∧ (∀ k, ∀ a ∈ R.byKey k, uint.nat a < 2 ^ 62) ∧
    ∀ k, ∀ a ∈ R.fastByKey k, uint.nat a < 2 ^ 62

/-- A configuration of a state made by `k` steps (see the file header). -/
def SharedBounded (B k : Nat) (g : GCfg) : Prop :=
  HWf g.st ∧ (∀ p ∈ g.pend, isWriteL p = true) ∧
    uint.nat g.st.st.rv + g.pend.length ≤ 2 ^ 62 + k ∧ g.st.st.items.length + g.pend.length ≤ B + k

end pure

section go
variable [GooseExts] [go_gctx : GoGlobalContext]

open Classical in
/-- Porcupine's operation as the input and output it boxes, if it is one. -/
def decIO (io : github_com.anishathalye.porcupine.OpV) : Option (Input × Output) :=
  if h : ∃ p : Input × Output, io = (boxIn p.1, boxOut p.2) then some h.choose else none

open Classical in
/-- **`SharedModel`'s sequential model** (see the file header). -/
def sharedM (g0 : HSt) (R : RevsL) (mode : Nat) :
    github_com.anishathalye.porcupine.Theory.SeqModel (GCfg → Prop) github_com.anishathalye.porcupine.OpV where
  init := fun g => g = ⟨g0, []⟩
  step S io := match decIO io with
    | none => none
    | some (x, y) =>
      let S' : GCfg → Prop := fun e => ∃ c, S c ∧ GoStep R mode c x y e
      if ∃ e, S' e then some S' else none

end go

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- `v` is a `state` whose configurations are exactly `S` (a configuration may be listed more than
once), each `SharedBounded B k`. -/
def sharedRep (B k : Nat) (v : GoInterface) (S : GCfg → Prop) : IProp GF :=
  iprop(∃ (sl : GoSlice) (cs : List mcfg) (gs : List GCfg),
    ⌜v = boxSt sl ∧ (∀ g, S g ↔ g ∈ gs) ∧ ∀ g ∈ gs, SharedBounded B k g⌝ ∗ sl ↦*□ cs ∗
      [∗list] c;g ∈ cs;gs, cfgOwn c g)

instance sharedRep_persistent (B k : Nat) (v : GoInterface) (S : GCfg → Prop) :
    Persistent (sharedRep (GF := GF) B k v S) := by
  unfold sharedRep; infer_instance

/-- **`SharedModel`'s specification**: `sharedM`, its states' values `sharedRep` (with the seeded
store's items as `B`), on operations naming revisions below `2^62`. -/
def sharedS (g0 : HSt) (R : RevsL) (mode : Nat) :
    github_com.anishathalye.porcupine.ModelSpec GF (GCfg → Prop) where
  M := sharedM g0 R mode
  rep k := sharedRep g0.st.items.length k
  ioOk i o := iprop(∃ x y, ⌜i = boxIn x ∧ o = boxOut y ∧ RevsBelow x y⌝)
  ioOk_pers _ _ := by infer_instance

end defs

end k8s_etcd3
end EtcdGrove
end Perennial
