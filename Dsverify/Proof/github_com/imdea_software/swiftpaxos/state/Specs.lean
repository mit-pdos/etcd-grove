/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/state/Specs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`state`'s internal specs (the replica group's): the store as SwiftPaxos's replicas execute
commands on it.

* `keyEnc k`: a `state.Key` as an `interface{}` (the treemap's keys);
* `ownState st σ`: the `*State` at `st` holds the key-value map `σ` (a key's value: the bytes
  of the `Value` slice stored, read-only); its mutex is initialized (invariant `True`: the
  replica serializes executions itself, under `execL`);
* `execS op k v σ`: a command's effect and result: `PUT` sets `k` to `v` and returns an empty
  value, `GET` returns `k`'s value (empty if none), any other operation but `SCAN` (`NONE`)
  changes nothing and returns an empty value (`sp.lin.apply`'s, on the replica's keys).

Specs: `KeyComparator` (signed comparison of two keys), `NIL`, `InitState`,
`(*Command).Execute` (not for `SCAN`: a registered command is a put or a get, `sp.cmdIs_ok`).
-/
module

public import Dsverify.Proof.github_com.emirpasic.gods.maps.treemap.Specs
public import Perennial.Proof.sync
public import Perennial.Golang.Theory
public import Dsverify.GeneratedProof.github_com.imdea_software.swiftpaxos.state

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv
open github_com.emirpasic.gods.maps (treemap.isTreeMap treemap.cmpOk treemap.lookupE
  treemap.Entries)

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp

section defs
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions]

/-- A key as the treemap holds it. -/
def state.keyEnc (k : w64) : GoInterface := interface.mkOk state.Key.ty #k

/-- The values of the entries `es` are read-only `Value` slices holding `σ`'s values. -/
def state.valsOk (es : treemap.Entries) (σ : w64 → Option (List w8)) : IProp GF :=
  iprop(□ ∀ k : w64, match treemap.lookupE es k with
    | none => ⌜σ k = none⌝
    | some x => ∃ (sl : GoSlice) (bs : List w8),
        ⌜x = interface.mkOk state.Value.ty #sl ∧ σ k = some bs⌝ ∗ sl ↦*□ bs)

instance state.valsOk_persistent (es : treemap.Entries) (σ : w64 → Option (List w8)) :
    Persistent (state.valsOk (GF := GF) es σ) := by unfold state.valsOk; infer_instance

/-- A put keeps the values read-only slices. -/
theorem state.valsOk_put (es : treemap.Entries) (σ : w64 → Option (List w8)) (k : w64)
    (vsl : GoSlice) (v : List w8) (hs : github_com.emirpasic.gods.maps.treemap.sortedE es) :
    state.valsOk (GF := GF) es σ ∗ vsl ↦*□ v ⊢
      state.valsOk (github_com.emirpasic.gods.maps.treemap.putE es k
        (interface.mkOk state.Value.ty #vsl)) (fun k' => if k' = k then some v else σ k') := by
  iintro ⟨#Hvals, #Hv⟩
  iunfold state.valsOk
  iintro !> %k'
  rw [github_com.emirpasic.gods.maps.treemap.lookupE_putE es k _ hs k']
  by_cases hk : k' = k
  · simp only [hk, ite_true]
    iexists vsl, v
    iframe Hv
    ipureintro; exact ⟨rfl, rfl⟩
  · simp only [hk, ite_false]
    iunfold state.valsOk at Hvals
    iapply Hvals

/-- The `*State` at `st` holds `σ`. -/
def state.ownState (st : Loc) (σ : w64 → Option (List w8)) : IProp GF :=
  iprop(∃ (mu tm : Loc) (es : treemap.Entries),
    st ↦ state.State.mk mu tm ∗ sync.isMutex mu iprop(True) ∗
    treemap.isTreeMap tm state.keyEnc es ∗ state.valsOk es σ)

/-- A command's effect on the map and its result (not for `SCAN`). -/
def state.execS (op : w8) (k : w64) (v : List w8) (σ : w64 → Option (List w8)) :
    (w64 → Option (List w8)) × List w8 :=
  if op = W8 1 then ((fun k' => if k' = k then some v else σ k'), [])
  else if op = W8 2 then (σ, (σ k).getD [])
  else (σ, [])

end defs

section spec
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions]
variable [sync.Assumptions] [SwiftNetPkgState GF]

/-- `KeyComparator(a, b)` on two keys: the sign of the signed comparison. -/
abbrev state.KeyComparator.spec : Prop :=
  ∀ (a b : w64),
  {{ (True : IProp GF) }}
    (App (App (Val (@! state.KeyComparator)) (Val #(state.keyEnc a))) (Val #(state.keyEnc b)))
  {{ (c : w64), RET #c; ⌜(sint.Z c < 0 ↔ sint.Z a < sint.Z b) ∧ (c = W64 0 ↔ a = b)⌝ }}

/-- `NIL()`: a fresh empty value. -/
abbrev state.NIL.spec : Prop :=
  {{ (True : IProp GF) }}
    (App (Val (@! state.NIL)) (Val #()))
  {{ (sl : GoSlice), RET #sl; sl ↦* ([] : List w8) }}

/-- `InitState()`: an empty store. -/
abbrev state.InitState.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.state }}
    (App (Val (@! state.InitState)) (Val #()))
  {{ (st : Loc), RET #st; state.ownState st (fun _ => none) }}

/-- `c.Execute(st)` of a command other than `SCAN` whose value slice is read-only: the store
changes and the result is as `execS` says (the result read-only: a `GET` returns the stored
slice itself). -/
abbrev state.Command.Execute.spec : Prop :=
  ∀ (c : Loc) (dq : DFrac) (op : w8) (k : w64) (vsl : GoSlice) (v : List w8) (st : Loc)
    (σ : w64 → Option (List w8)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.state ∗
      c ↦{dq} state.Command.mk op k vsl ∗ vsl ↦*□ v ∗ state.ownState st σ ∗ ⌜op ≠ W8 3⌝ }}
    (App (Val (c @!! go.GoType.PointerType state.Command.ty @!! go!"Execute")) (Val #st))
  {{ (r : GoSlice), RET #r; c ↦{dq} state.Command.mk op k vsl ∗
      state.ownState st (state.execS op k v σ).1 ∗ r ↦*□ (state.execS op k v σ).2 }}

end spec

end Perennial.github_com.imdea_software.swiftpaxos
