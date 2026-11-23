/-
The definitions, specs and lemmas of `OrchParts.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.Interface
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Perennial.Proof.fmt

-- PORT: lab imports dropped: Harness.Proof.math.rand

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace orch

/-- The Go value of a configuration. -/
def confV (c : Conf) : examples.swiftnet.Conf :=
  ⟨W64 c.n, W64 c.fastRead, W64 c.pool, W64 c.desc⟩

/-- A planned change as a client node gets it (its `Client` is not on the wire). -/
def toChange (ch : examples.swiftnet.change) : Change := ⟨uint.nat ch.Node', uint.nat ch.After'⟩

/-- `plan`'s changes: made by a client node (`Client < 6`), valid for the configuration. -/
def planOk (c : Conf) (ch : examples.swiftnet.change) : Prop :=
  uint.nat ch.Client' < 6 ∧ (toChange ch).valid c

/-- `mine(cs, c)`: the changes of client `c`. -/
def mineL (cs : List examples.swiftnet.change) (c : w64) : List examples.swiftnet.change :=
  cs.filter (fun ch => decide (ch.Client' = c))

/-- The changes a client node gets are valid (`decode`'s check). -/
theorem mineL_ok (c : Conf) (cs : List examples.swiftnet.change) (cl : w64)
    (hl : cs.length ≤ maxChanges) (hok : ∀ ch ∈ cs, planOk c ch) :
    c.changesOk ((mineL cs cl).map toChange) := by
  refine ⟨?_, ?_⟩
  · simp only [List.length_map, mineL]
    exact Nat.le_trans (List.length_filter_le _ _) hl
  · intro ch hch
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hch
    exact (hok x (List.mem_filter.1 hx).1).2

theorem confV_nat (a b c d : w64) :
    confV ⟨uint.nat a, uint.nat b, uint.nat c, uint.nat d⟩ = ⟨a, b, c, d⟩ := by
  simp only [confV, examples.swiftnet.Conf.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> word

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [examples.swiftnet.Assumptions]

local notation "swiftnetPkg" => pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet

/-- `choose()`: a valid configuration (any: `math/rand`'s model). -/
abbrev choose.spec : Prop :=
  {{ isPkgInit (PROP := IProp netDistGF) swiftnetPkg }}
    (App (Val (@! examples.swiftnet.choose)) (Val #()))
  {{ (c : Conf), RET #(confV c); ⌜c.valid⌝ }}

/-- `plan(conf)`: one or two leader changes, each by a client node at a replica node of the
configuration, after 1..7 operations. -/
abbrev plan.spec : Prop :=
  ∀ (c : Conf), c.valid →
  {{ isPkgInit (PROP := IProp netDistGF) swiftnetPkg }}
    (App (Val (@! examples.swiftnet.plan)) (Val #(confV c)))
  {{ (sl : GoSlice) (cs : List examples.swiftnet.change), RET #sl;
      sl ↦* cs ∗ ⌜cs.length ≤ maxChanges ∧ ∀ ch ∈ cs, planOk c ch⌝ }}

/-- `mine(cs, c)`. -/
abbrev mine.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (cs : List examples.swiftnet.change) (c : w64),
  {{ isPkgInit (PROP := IProp netDistGF) swiftnetPkg ∗ sl ↦*{dq} cs }}
    (App (App (Val (@! examples.swiftnet.mine)) (Val #sl)) (Val #c))
  {{ (m : GoSlice), RET #m; m ↦* mineL cs c ∗ sl ↦*{dq} cs }}

/-- `conf.encode(cs)` (through the pointer `p` to a configuration): the nine bytes. -/
abbrev Conf.encode.spec : Prop :=
  ∀ (p : Loc) (c : Conf) (dq : DFrac) (sl : GoSlice) (dq' : DFrac)
    (cs : List examples.swiftnet.change), c.valid → cs.length ≤ maxChanges →
  {{ isPkgInit (PROP := IProp netDistGF) swiftnetPkg ∗ p ↦{dq} confV c ∗ sl ↦*{dq'} cs }}
    (App (Val (p @!! go.GoType.PointerType examples.swiftnet.Conf.ty @!! go!"encode"))
      (Val #sl))
  {{ (b : GoSlice), RET #b; b ↦* c.encodeC (cs.map toChange) ∗ p ↦{dq} confV c ∗
      sl ↦*{dq'} cs }}

/-- `conf.String()` (through the pointer `p`): some string. -/
abbrev Conf.String.spec : Prop :=
  ∀ (p : Loc) (v : examples.swiftnet.Conf) (dq : DFrac),
  {{ isPkgInit (PROP := IProp netDistGF) swiftnetPkg ∗ p ↦{dq} v }}
    (App (Val (p @!! go.GoType.PointerType examples.swiftnet.Conf.ty @!! go!"String"))
      (Val #()))
  {{ (s : GoString), RET #s; p ↦{dq} v }}

end specs

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [examples.swiftnet.Assumptions]

set_option goose.wp.extras true

/-- The configuration's encoding after `i` of the changes `cs` are written. -/
def encPart (c : Conf) (cs : List Change) (i : Nat) : List w8 :=
  [W8 c.n, W8 c.fastRead, W8 c.pool, W8 c.desc, W8 cs.length] ++
    (List.range maxChanges).flatMap (fun j =>
      match (if j < i then cs[j]? else none) with
      | some ch => [W8 ch.node, W8 ch.after]
      | none => [W8 0, W8 0])

theorem encPart_done (c : Conf) (cs : List Change) (i : Nat) (h : cs.length ≤ i) :
    encPart c cs i = c.encodeC cs := by
  unfold encPart Conf.encodeC
  congr 2
  funext j
  by_cases hj : j < i
  · rw [if_pos hj]; cases cs[j]? <;> rfl
  · rw [if_neg hj, List.getElem?_eq_none (by omega : cs.length ≤ j)]

theorem encPart_length (c : Conf) (cs : List Change) (i : Nat) : (encPart c cs i).length = 9 := by
  unfold encPart
  simp only [maxChanges, show List.range 2 = [0, 1] from rfl, List.flatMap_cons, List.flatMap_nil,
    List.length_append, List.append_nil]
  split <;> split <;> simp

theorem encPart_step (c : Conf) (cs : List Change) (i : Nat) (ch : Change)
    (hi : i < maxChanges) (hch : cs[i]? = some ch) :
    ((encPart c cs i).set (5 + 2 * i) (W8 ch.node)).set (6 + 2 * i) (W8 ch.after) =
      encPart c cs (i + 1) := by
  unfold maxChanges at hi
  unfold encPart
  simp only [maxChanges]
  rw [show List.range 2 = [0, 1] from rfl]
  match i, hi with
  | 0, _ => simp [hch]
  | 1, _ =>
    cases h0 : cs[0]? <;> simp [hch, h0]

theorem W8_W64 (m : Nat) (hm : m < 2 ^ 32) : W8 (uint.Z (W64 (m : Int))) = W8 (m : Int) := by
  word

theorem W8_uint (x : w64) : W8 (uint.nat x : Int) = W8 (uint.Z x) := by
  congr 1

end proofs

end orch

end Perennial.github_com.imdea_software.swiftpaxos
