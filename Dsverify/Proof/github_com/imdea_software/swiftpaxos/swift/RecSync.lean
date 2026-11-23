/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/RecSync.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`recoveredSync` (recovery.go) against the model's `recoverSync` (Spec/swift/Model/Defs.lean):
the reports' Go representation (`swift.ackObj`), the premises the new leader's reports satisfy
(`swift.RepsOk`, discharged from the protocol invariant by `handleNewLeaderAckNs`), the specs of
`recoveredSync`'s callees not yet stated elsewhere (hypotheses of its proof), and its spec.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.KeySpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Defs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumSpecs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-! ## Pure: the premises on the reports -/

/-- `SCAN` (`state.SCAN`): no report carries one (`Cmd.conflict` and `keysOf` are the
put/get ones). -/
def swift.opSCAN : w8 := 3

/-- What `recoveredSync` needs of its reports (Go's behavior is the model's under these):
a majority's (non-empty, distinct replicas `< N`, sorted the same by Go's `SortFunc` and the
model's stable sort), each `cballot` an `int32`, every phase at most `COMMIT` (Go's signed
comparisons of phases are the model's on `toNat`), every pre-accepted entry's dependencies
without duplicates (`Dep.Equals` is a set comparison: the model's `isPerm` on such lists), no
`SCAN`, and the sizes bounded (`sortedIds`' `2^62`). -/
structure swift.RepsOk (N : Nat) (reps : List (Nat × sp.Report)) : Prop where
  ne : reps ≠ []
  nodup : (reps.map Prod.fst).Nodup
  len : reps.length ≤ N
  hN : 1 ≤ N ∧ N ≤ 7
  rep : ∀ a ∈ reps, a.1 < N ∧ a.2.cbal < 2 ^ 31
  ents : ∀ a ∈ reps, ∀ e ∈ a.2.entries, e.phase.toNat ≤ 3 ∧ e.cmd.op ≠ swift.opSCAN ∧
    (e.phase.toNat = 1 → e.dep.Nodup)
  size : (reps.flatMap (·.2.entries)).length < 2 ^ 31
  /-- every reported command is a put or a get (D10: registered commands are; Go's
  `getConflictCmds` and the model's `lkDeps` agree on them, SWA-1) -/
  pg : ∀ a ∈ reps, ∀ e ∈ a.2.entries, e.cmd.isPut ∨ e.cmd.isGet

section defs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]

/-- An entry of a report (its `i`-th): its command and its dependencies (read-only). -/
def swift.repEntryObj (cm : state.Command) (sd : swift.SDep) (e : sp.RepEntry) : IProp netDistGF :=
  iprop(∃ vs : GoSlice, ⌜cm = state.Command.mk e.cmd.op e.cmd.key vs⌝ ∗ vs ↦*□ e.cmd.val ∗
    sd.Dep' ↦*□ (e.dep.map ofCmdId))

/-- A recovery report at `p` (an `*MNewLeaderAckN`, read-only) carrying the model's report `a`
(its replica and contents). -/
def swift.ackObj (p : Loc) (a : Nat × sp.Report) : IProp netDistGF :=
  iprop(∃ (rep bl cb : w32) (ids ph cm dp : GoSlice) (cmL : List state.Command)
      (dpL : List swift.SDep),
    p ↦□ swift.MNewLeaderAckN.mk rep bl cb ids ph cm dp ∗
    ids ↦*□ (a.2.entries.map (fun e => ofCmdId e.id)) ∗
    ph ↦*□ (a.2.entries.map (·.phase)) ∗ cm ↦*□ cmL ∗ dp ↦*□ dpL ∗
    ⌜sint.Z rep = a.1 ∧ sint.Z cb = a.2.cbal ∧ cmL.length = a.2.entries.length ∧
      dpL.length = a.2.entries.length⌝ ∗
    [∗list] i ↦ e ∈ a.2.entries, ∃ (c : state.Command) (sd : swift.SDep),
      ⌜cmL[i]? = some c ∧ dpL[i]? = some sd⌝ ∗ swift.repEntryObj c sd e)

instance swift.repEntryObj_persistent (cm : state.Command) (sd : swift.SDep) (e : sp.RepEntry) :
    Persistent (swift.repEntryObj cm sd e) := by
  unfold swift.repEntryObj; infer_instance

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 1000000 in
instance swift.ackObj_persistent (p : Loc) (a : Nat × sp.Report) :
    Persistent (swift.ackObj p a) := by
  unfold swift.ackObj; infer_instance

/-- The reports as `recoveredSync` gets them (`msgs []interface{}`): each an
`*MNewLeaderAckN` with its model report (`prs`: the pointers with their reports). -/
def swift.acksIs (ms : List GoInterface) (reps : List (Nat × sp.Report)) : IProp netDistGF :=
  iprop(∃ prs : List (Loc × (Nat × sp.Report)),
    ⌜ms = prs.map (fun q => interface.mkOk (go.GoType.PointerType swift.MNewLeaderAckN.ty) #q.1) ∧
      reps = prs.map Prod.snd⌝ ∗
    [∗list] q ∈ prs, swift.ackObj q.1 q.2)

instance swift.acksIs_persistent (ms : List GoInterface) (reps : List (Nat × sp.Report)) :
    Persistent (swift.acksIs ms reps) := by
  unfold swift.acksIs; infer_instance

/-- `slices.SortFunc`'s comparator, needed only on the slice's elements (each satisfying the
persistent `P`): Perennial's `cmpImplements` asks for every pair of values, which a comparator
that dereferences its arguments (`recoveredSync`'s, on `*MNewLeaderAckN`) cannot give. -/
def slices.cmpImplementsOn {E : Type} [ZeroVal E] [TypedPointsto (GF := netDistGF) E] {Et : go.GoType}
    [IntoValTyped (GF := netDistGF) E Et] (R : E → E → Prop) (P : E → IProp netDistGF)
    (cmp_code : GoFunc) : IProp netDistGF :=
  iprop(∀ (x y : E),
    {{ P x ∗ P y }}
      (App (App (Val #cmp_code) (Val #x)) (Val #y))
    {{ (r : w64), RET #r; ⌜sint.Z r < 0 ↔ R x y⌝ }})

end defs

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]

/-- **FRAMEWORK request** (Perennial, `slices.SortFunc.spec`): the spec with the comparator
required only on the slice's elements (`SortFunc` compares only elements of the slice). A
hypothesis of `recoveredSync`'s proof (and of `fillNewLeaderAckN`'s, whose comparator indexes
local slices). -/
abbrev slices.SortFunc.specOn : Prop :=
  ∀ {E : Type} [ZeroVal E] [TypedPointsto (GF := netDistGF) E] {Et : go.GoType}
    [IntoValTyped (GF := netDistGF) E Et] (R : E → E → Prop) (P : E → IProp netDistGF)
    [∀ x, Persistent (P x)] {S : go.GoType} [S ↓u go.SliceType Et]
    (data : GoSlice) (cmp_code : GoFunc) (xs : List E) (SWO : slices.StrictWeakOrder R),
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.slices ∗
        data ↦* xs ∗ ⌜xs.length ≤ 2 ^ 62⌝ ∗ ([∗list] x ∈ xs, P x) ∗
        slices.cmpImplementsOn (Et := Et) R P cmp_code }}
      (App (App (Val #(functions slices.SortFunc [S, Et])) (Val #data)) (Val #cmp_code))
    {{ (xs' : List E), RET #();
        data ↦* xs' ∗ ⌜xs ≡ₚ xs'⌝ ∗
        ⌜∀ (i j : Nat) (xi xj : E), xs'[i]? = some xi → xs'[j]? = some xj → i < j → ¬ R xj xi⌝ }}

/-- `inConflict(c1, c2)` (`state.Conflict`) for commands that are not `SCAN`s: the model's
`Cmd.conflict` (the same key, and a put). -/
abbrev swift.inConflict.specI : Prop :=
  ∀ (c1 c2 : sp.Cmd) (v1 v2 : GoSlice),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      ⌜c1.op ≠ swift.opSCAN ∧ c2.op ≠ swift.opSCAN⌝ }}
    (App (App (Val (@! swift.inConflict)) (Val #(state.Command.mk c1.op c1.key v1)))
      (Val #(state.Command.mk c2.op c2.key v2)))
  {{ RET #(sp.Cmd.conflict c1 c2); True }}

/-- `keysOf(cmd)` for a command that is not a `SCAN`: its key. -/
abbrev swift.keysOf.specI : Prop :=
  ∀ (c : sp.Cmd) (vs : GoSlice),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      ⌜c.op ≠ swift.opSCAN⌝ }}
    (App (Val (@! swift.keysOf)) (Val #(state.Command.mk c.op c.key vs)))
  {{ (sl : GoSlice), RET #sl; sl ↦* [c.key] }}

/-- `(&dep).Contains(x)`: membership. -/
abbrev swift.Dep.Contains.specI : Prop :=
  ∀ (dp : Loc) (dsl : GoSlice) (dq dq' : DFrac) (ds : List swift.CommandId) (x : swift.CommandId),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      typedPointsto dp dsl dq ∗ dsl ↦*{dq'} ds }}
    (App (Val (dp @!! go.GoType.PointerType swift.Dep.ty @!! go!"Contains")) (Val #x))
  {{ RET #(decide (x ∈ ds)); typedPointsto dp dsl dq ∗ dsl ↦*{dq'} ds }}

/-- `(&dep1).Equals(dep2)` on lists without duplicates: equal as sets (the model's `depEq`). -/
abbrev swift.Dep.Equals.specG : Prop :=
  ∀ (dp : Loc) (d1 d2 : GoSlice) (dq dq1 dq2 : DFrac) (l1 l2 : List swift.CommandId),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      typedPointsto dp d1 dq ∗ d1 ↦*{dq1} l1 ∗ d2 ↦*{dq2} l2 ∗ ⌜l1.Nodup ∧ l2.Nodup⌝ }}
    (App (Val (dp @!! go.GoType.PointerType swift.Dep.ty @!! go!"Equals")) (Val #d2))
  {{ RET #(sp.depEq (l1.map toCmdId) (l2.map toCmdId));
      typedPointsto dp d1 dq ∗ d1 ↦*{dq1} l1 ∗ d2 ↦*{dq2} l2 }}

/-- `r.recoveredSync(msgs)` (the new leader of ballot `bal`, replica `me` of `N`): the `MSync`
of the model's `recoverSync N reps`, a new object (read-only from then on), with its `Replica`
field `me` and ballot `bal` (`swift.syncSent`). -/
abbrev swift.Replica.recoveredSync.specI : Prop :=
  ∀ (rp rr qs : Loc) (N : Nat) (me bal : w32) (dq : DFrac) (msl : GoSlice)
    (ms : List GoInterface) (reps : List (Nat × sp.Report)),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.slices ∗
      swift.fld rp go!"Replica" ↦□ rr ∗ replica.fld rr go!"N" ↦□ (W64 N) ∗
      replica.fld rr go!"Id" ↦□ me ∗ swift.fld rp go!"qs" ↦□ qs ∗
      replica.quorum.isQS qs N ∗
      typedPointsto (swift.fld rp go!"ballot") bal dq ∗
      msl ↦*□ ms ∗ swift.acksIs ms reps ∗ ⌜swift.RepsOk N reps⌝ }}
    (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"recoveredSync")) (Val #msl))
  {{ (ls : Loc), RET #ls; typedPointsto (swift.fld rp go!"ballot") bal dq ∗
      swift.syncSent ls me bal (sp.recoverSync N reps) }}

end specs

end Perennial.github_com.imdea_software.swiftpaxos
