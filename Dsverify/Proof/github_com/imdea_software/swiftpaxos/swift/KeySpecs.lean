/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/KeySpecs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`lightKeyInfo` (swift/key.go; the replica group's internal specs, not frozen): a key's last put
`W` and the last put and the gets since `C` (both read-only slices once made: `add` makes new
ones, so a slice `getConflictCmds` returned stays valid).
* `newLightKeyInfo()`: `W = C = []`.
* `ki.add(c, x)`: a put: `W = C = [x]`; anything else: `C ++ [x]` (premise: `C`'s length + 1
  fits an `int`, the capacity `make` is given).
* `ki.remove(c, x)`: each list that starts with `x` becomes empty.
* `ki.getConflictCmds(c)`: `W` for a get, `C` else.
Their relation to the protocol model's `lkDeps` is `KeyModel.lean`'s.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HashLeaf
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HashLogKey

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift.lki
open swift.hlog (cmdIdDecEq)

/-- `add`'s effect on `(W, C)`. -/
def addTo (op : w8) (x : swift.CommandId) (W C : List swift.CommandId) :
    List swift.CommandId × List swift.CommandId :=
  if op = W8 1 then ([x], [x]) else (W, C ++ [x])

/-- `remove`'s effect on a list. -/
def dropIf (x : swift.CommandId) (L : List swift.CommandId) : List swift.CommandId :=
  if L.head? = some x then [] else L

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [swift.Assumptions]

/-- The `*lightKeyInfo` at `ki` holds `W` and `C`. -/
def lkiOwn (ki : Loc) (W C : List swift.CommandId) : IProp netDistGF :=
  iprop(∃ lw lc : GoSlice, ki ↦ swift.lightKeyInfo.mk lw lc ∗ lw ↦*□ W ∗ lc ↦*□ C)

abbrev newLightKeyInfo.spec : Prop :=
  {{ (True : IProp netDistGF) }}
    (App (Val (@! swift.newLightKeyInfo)) (Val #()))
  {{ (ki : Loc), RET #ki; lkiOwn ki [] [] }}

abbrev lightKeyInfo.add.spec : Prop :=
  ∀ (ki : Loc) (W C : List swift.CommandId) (c : state.Command) (x : swift.CommandId),
  {{ lkiOwn ki W C ∗ ⌜C.length + 1 < 2 ^ 63⌝ }}
    (App (App (Val (ki @!! go.GoType.PointerType swift.lightKeyInfo.ty @!! go!"add")) (Val #c))
      (Val #x))
  {{ RET #(); lkiOwn ki (addTo c.Op' x W C).1 (addTo c.Op' x W C).2 }}

abbrev lightKeyInfo.remove.spec : Prop :=
  ∀ (ki : Loc) (W C : List swift.CommandId) (c : state.Command) (x : swift.CommandId),
  {{ lkiOwn ki W C }}
    (App (App (Val (ki @!! go.GoType.PointerType swift.lightKeyInfo.ty @!! go!"remove"))
      (Val #c)) (Val #x))
  {{ RET #(); lkiOwn ki (dropIf x W) (dropIf x C) }}

abbrev lightKeyInfo.getConflictCmds.spec : Prop :=
  ∀ (ki : Loc) (W C : List swift.CommandId) (c : state.Command),
  {{ lkiOwn ki W C }}
    (App (Val (ki @!! go.GoType.PointerType swift.lightKeyInfo.ty @!! go!"getConflictCmds"))
      (Val #c))
  {{ (sl : GoSlice), RET #sl; lkiOwn ki W C ∗ sl ↦*□ (if c.Op' = W8 2 then W else C) }}

end defs

end swift.lki

end Perennial.github_com.imdea_software.swiftpaxos
