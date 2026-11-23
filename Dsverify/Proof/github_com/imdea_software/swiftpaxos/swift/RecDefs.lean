/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/RecDefs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The recovery's Go state against the model (recovery.go; Spec/swift/Model/Defs.lean): a
`*recEntry` (`swift.recOwn`) and the map `kept` (`swift.keptOwn`) against the model's `Kept`
(an association list; the Go map's keys are its keys, each entry the model's), and the specs of
the recovery's helpers (`recReaches`, `recOrder`, `syncOrder`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SortedIdsDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecPure

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]

/-- A Go `*recEntry` at `p` against the model's entry `e`. `o`: its dependency slice is owned
with its capacity (the closure's fresh lists, which rules 3b and 4 append to), or read-only (a
report's slice, before the closure replaces it). The phase is at most `COMMIT` (so Go's signed
comparisons are the model's), the class at most 2. -/
def swift.recOwn (p : Loc) (e : sp.RecEntry) (o : Bool) : IProp netDistGF :=
  iprop(∃ (ph cls : w64) (vs dsl : GoSlice),
    p ↦ swift.recEntry.mk ph (state.Command.mk e.cmd.op e.cmd.key vs) dsl cls ∗
    vs ↦*□ e.cmd.val ∗
    (if o then iprop(dsl ↦* (e.dep.map ofCmdId) ∗ ownSliceCap swift.CommandId dsl (DFrac.own 1))
      else iprop(dsl ↦*□ (e.dep.map ofCmdId))) ∗
    ⌜uint.nat ph = e.phase ∧ e.phase ≤ 3 ∧ uint.nat cls = e.cls ∧ e.cls ≤ 2⌝)

/-- The map `kept` at `m` against the model's `Kept` `k`: the same keys (no duplicate in `k`),
each entry the model's; `o` says which entries own their dependency slices. -/
def swift.keptOwn (m : Loc) (k : sp.Kept) (o : sp.CmdId → Bool) : IProp netDistGF :=
  iprop(∃ mk : GMap swift.CommandId Loc, m ↦$ mk ∗
    ⌜(k.map Prod.fst).Nodup ∧ ∀ c, (mk !! c).isSome = (k.get (toCmdId c)).isSome⌝ ∗
    [∗map] c ↦ p ∈ mk, ∃ e, ⌜k.get (toCmdId c) = some e⌝ ∗ swift.recOwn p e (o (toCmdId c)))

/-- `keptOwn` at a given Go map `mk` (its body). -/
def swift.keptAt (m : Loc) (k : sp.Kept) (o : sp.CmdId → Bool) (mk : GMap swift.CommandId Loc) :
    IProp netDistGF :=
  iprop(m ↦$ mk ∗
    ⌜(k.map Prod.fst).Nodup ∧ ∀ c, (mk !! c).isSome = (k.get (toCmdId c)).isSome⌝ ∗
    [∗map] c ↦ p ∈ mk, ∃ e, ⌜k.get (toCmdId c) = some e⌝ ∗ swift.recOwn p e (o (toCmdId c)))

/-- An `MSync` at `ls` (read-only) carrying the model's `M` for ballot `b`: its `Phases` keys
are `M`'s ids (no duplicate), and for each command its `Cmds` and `Deps` entries are `M`'s
(the phases' values are not constrained: `handleSync` only tests the keys). -/
def swift.syncMaps (ls : Loc) (b : Nat) (M : sp.SyncMsg) : IProp netDistGF :=
  iprop(∃ (rep bl : w32) (ph cm dp : Loc) (phM : GMap swift.CommandId w64)
      (cmM : GMap swift.CommandId state.Command) (dpM : GMap swift.CommandId GoSlice),
    ls ↦□ swift.MSync.mk rep bl ph cm dp ∗ ph ↦$□ phM ∗ cm ↦$□ cmM ∗ dp ↦$□ dpM ∗
    ⌜sp.bal bl = b ∧ (M.map Prod.fst).Nodup ∧
      ∀ x, (phM !! x).isSome = true ↔ toCmdId x ∈ M.map Prod.fst⌝ ∗
    [∗list] p ∈ M, ∃ (vs dsl : GoSlice),
      ⌜cmM !! ofCmdId p.1 = some (state.Command.mk p.2.1.op p.2.1.key vs) ∧
        dpM !! ofCmdId p.1 = some dsl⌝ ∗
      vs ↦*□ p.2.1.val ∗ dsl ↦*□ (p.2.2.map ofCmdId))

/-- The `Cmds`/`Deps` entries of `M`'s commands (read-only). -/
def swift.syncEnts (cmM : GMap swift.CommandId state.Command) (dpM : GMap swift.CommandId GoSlice)
    (M : sp.SyncMsg) : IProp netDistGF :=
  iprop([∗list] p ∈ M, ∃ (vs dsl : GoSlice),
    ⌜cmM !! ofCmdId p.1 = some (state.Command.mk p.2.1.op p.2.1.key vs) ∧
      dpM !! ofCmdId p.1 = some dsl⌝ ∗
    vs ↦*□ p.2.1.val ∗ dsl ↦*□ (p.2.2.map ofCmdId))

instance swift.syncEnts_persistent (cmM : GMap swift.CommandId state.Command)
    (dpM : GMap swift.CommandId GoSlice) (M : sp.SyncMsg) :
    Persistent (swift.syncEnts cmM dpM M) := by
  unfold swift.syncEnts
  exact BigSepL.bigSepL_persistent (fun _ _ _ => by infer_instance)

/-- An `MSync` as its sender built it: `syncMaps`, and (for its marshalling; the receivers only
read `syncMaps`) the whole picture again at the same maps: its `Replica`/`Ballot` fields, its
phases (all `COMMIT`), and (change log C18) the `Cmds`/`Deps` maps with exactly `M`'s keys (the
`Phases`' keys). -/
def swift.syncSent (ls : Loc) (me bl : w32) (M : sp.SyncMsg) : IProp netDistGF :=
  iprop(swift.syncMaps ls (sp.bal bl) M ∗
    ∃ (ph cm dp : Loc) (phM : GMap swift.CommandId w64)
      (cmM : GMap swift.CommandId state.Command) (dpM : GMap swift.CommandId GoSlice),
      ls ↦□ swift.MSync.mk me bl ph cm dp ∗ ph ↦$□ phM ∗ cm ↦$□ cmM ∗ dp ↦$□ dpM ∗
      ⌜(∀ x v, phM !! x = some v → v = W64 3) ∧ (M.map Prod.fst).Nodup ∧
        (∀ x, (phM !! x).isSome = true ↔ toCmdId x ∈ M.map Prod.fst) ∧
        ∀ x, (cmM !! x).isSome = (phM !! x).isSome ∧ (dpM !! x).isSome = (phM !! x).isSome⌝ ∗
      swift.syncEnts cmM dpM M)

end defs

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]

/-- `recReaches(kept, from, to)`: the model's `recReaches` (reachability through the kept
dependencies, `sp.recReaches_iff`). -/
abbrev swift.recReaches.specI : Prop :=
  ∀ (m : Loc) (k : sp.Kept) (o : sp.CmdId → Bool) (src dst : swift.CommandId),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      swift.keptOwn m k o }}
    (App (App (App (Val (@! swift.recReaches)) (Val #m)) (Val #src)) (Val #dst))
  {{ RET #(sp.recReaches k (toCmdId src) (toCmdId dst)); swift.keptOwn m k o }}

/-- `recReaches` at a given Go map (the map is not changed: rules 3b and 4 keep their entries'
pointers across the call). `specI` is its instance. -/
abbrev swift.recReaches.specM : Prop :=
  ∀ (m : Loc) (k : sp.Kept) (o : sp.CmdId → Bool) (mk : GMap swift.CommandId Loc)
    (src dst : swift.CommandId),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      swift.keptAt m k o mk }}
    (App (App (App (Val (@! swift.recReaches)) (Val #m)) (Val #src)) (Val #dst))
  {{ RET #(sp.recReaches k (toCmdId src) (toCmdId dst)); swift.keptAt m k o mk }}

/-- `recOrder(kept, ids)` for distinct kept `ids`: the model's `recOrder` (a new slice). -/
abbrev swift.recOrder.specI : Prop :=
  ∀ (m : Loc) (k : sp.Kept) (o : sp.CmdId → Bool) (isl : GoSlice) (ids : List swift.CommandId)
    (dq : DFrac),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      swift.keptOwn m k o ∗ isl ↦*{dq} ids ∗
      ⌜ids.Nodup ∧ ∀ c ∈ ids, (k.get (toCmdId c)).isSome⌝ }}
    (App (App (Val (@! swift.recOrder)) (Val #m)) (Val #isl))
  {{ (osl : GoSlice), RET #osl; swift.keptOwn m k o ∗ isl ↦*{dq} ids ∗
      osl ↦* ((sp.recOrder k (ids.map toCmdId)).map ofCmdId) ∗
      ownSliceCap swift.CommandId osl (DFrac.own 1) }}

/-- `syncOrder(msg)`: the model's `syncOrder` of the `MSync`'s contents (a new slice). -/
abbrev swift.syncOrder.specI : Prop :=
  ∀ (ls : Loc) (b : Nat) (M : sp.SyncMsg),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      swift.syncMaps ls b M ∗ ⌜M.length ≤ 2 ^ 62⌝ }}
    (App (Val (@! swift.syncOrder)) (Val #ls))
  {{ (osl : GoSlice), RET #osl; osl ↦* ((sp.syncOrder M).map ofCmdId) ∗
      ownSliceCap swift.CommandId osl (DFrac.own 1) }}

end specs

end Perennial.github_com.imdea_software.swiftpaxos
