/-
`Run(model, addrs, codec, gen, ops, d, timeout)`: the orchestrator (node 0). lintest's driver
(`perclient.Run`) with `len(addrs)` clients of `ops` operations, client `c`'s made at the node at
`addrs[c]` (`remoteAddr`) by `Do`, the history checked by porcupine against `model` (`isModel S`).

**porcupine never reports `Illegal`, and `Ok` with no timeout**, when: `S` is the pending-writes
model of the far side's store `R.B` (`PendDec`) and node 0's invariant `pendCtx` (the far side's
state `R.sysState`, timeless, at the model's initial state, `pendLib`) is in place, the generator gives the
store's inputs (`iv i`), the codec is `R`'s (`codecOk`), every address serves `R`'s calls; the
masks: the far side's (`R.Eop`), node 0's invariant's (`pendN`) and lintest's (`lintestN`) are
disjoint; lintest's bounds on the history, and the time receipts' (`CounterClock`); and the call
budget: `nb ≥ ops * readTries` of each address's call units (`budUnits`), `readTries` per operation
(`Do`). Proved in
`Net/Proof/.../lib/remote/Run.lean`.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Pend
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.Defs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net github_com.anishathalye.porcupine EtcdGrove.lintest

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.mit_pdos.etcd_grove.examples.lib.remote.Assumptions]
variable [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]
variable {St I O : Type} [DecidableEq I] [Pos.Countable I] [Pos.Countable O]

/-- See the file header. -/
abbrev Run.spec : Prop :=
  ∀ (R : RBase GF St I O) (S : ModelSpec GF (EtcdGrove.linkv.PSet St I)) (γ : PendNames)
    (m : Model) (addrs : GoSlice) (addrL : List GoString) (cd : remote.Codec) (gen : GoFunc)
    (ops d tmo : w64),
  (↑pendN : CoPset) ⊆ ⊤ \ R.Eop → (↑lintestN : CoPset) ⊆ ⊤ \ (R.Eop ∪ ↑pendN) →
  PendDec R S → (∀ o o', R.encOut (R.ov o) = R.encOut (R.ov o') → o = o') →
  (∀ st, Timeless (R.sysState st)) → receiptBound GF ≤ 2 ^ 63 →
  sint.Z addrs.len < 2 ^ 31 → 0 ≤ sint.Z ops → sint.Z addrs.len * sint.Z ops < 2 ^ 60 →
  ∀ nb : Nat, sint.nat ops * readTries ≤ nb →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote ∗ context.isClosedchanInit ∗ isModel S m ∗
      genSpec gen (fun x => iprop(∃ i, ⌜x = R.iv i⌝)) ∗ addrs ↦*□ addrL ∗
      ([∗list] a ∈ addrL, remoteAddr (Gg := hG.goose_globalGS) R a) ∗ mapCtx (Gg := hG.goose_globalGS) (I := I) ∗ codecOk R cd ∗
      pendCtx (Gg := hG.goose_globalGS) R S γ ∗ pendLib (Gg := hG.goose_globalGS) S γ S.M.init ∗
      [∗list] a ∈ addrL, budUnits (Gg := hG.goose_globalGS) a nb }}
    (App (App (App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.remote.Run)) (Val #m)) (Val #addrs)) (Val #cd))
      (Val #gen)) (Val #ops)) (Val #d)) (Val #tmo))
  {{ (r : GoString), RET #r; ⌜r ≠ go!"Illegal" ∧ (sint.Z tmo ≤ 0 → r = go!"Ok")⌝ }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.remote
end Perennial
