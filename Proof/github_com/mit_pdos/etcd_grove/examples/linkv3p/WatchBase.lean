/-
**The watch workload's vocabulary** (W4d of `notes/watch-cut-plan.md`, 2026-10-22; watchkv's,
`Proof/.../watchkv/Defs.lean`, for linkv3p's copy of its program). Lean-first (no Rocq
counterpart).

The program's structs by short names (`wkv`, `wev`, `wrec`), the prefix `wkPfx`, `genPut`'s keys
and values (`genKeys`, `genVals`), `pairOf` (a `kv`'s key and value), `GenKv` (a `kv` `genPut`
may return), `CheckOk` (what `checkWatch` needs not to panic).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv3p.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3p

open github_com.mit_pdos.etcd_grove.examples.linkv3p

section pure
variable [ext : FfiSyntax]

/-- The program's structs (`kv`, `event`, `putRec`), by short names. -/
abbrev wkv := github_com.mit_pdos.etcd_grove.examples.linkv3p.kv
abbrev wev := github_com.mit_pdos.etcd_grove.examples.linkv3p.event
abbrev wrec := github_com.mit_pdos.etcd_grove.examples.linkv3p.putRec

/-- The prefix the writers' keys are under and the watch covers. -/
abbrev wkPfx : GoString := go!"wk/"

/-- The keys `genPut` picks from. -/
abbrev genKeys : List GoString := [go!"wk/k0", go!"wk/k1", go!"wk/k2"]

/-- The values `genPut` picks from. -/
abbrev genVals : List GoString := [go!"a", go!"b", go!"c", go!"d"]

/-- A `kv`'s key and value. -/
def pairOf (p : wkv) : GoString × GoString := (p.key', p.val')

/-- A `kv` `genPut` may return. -/
def GenKv (p : wkv) : Prop := p.key' ∈ genKeys ∧ p.val' ∈ genVals

/-- **What `checkWatch` needs not to panic** (watchkv's `CheckOk`): the events are puts at
revisions `2, 3, ...` (one per revision, in order), each of a key and value tried, fewer than
`2 ^ 63 - 1`; and each successful put is the event at its revision with its key and value. -/
def CheckOk (evs : List wev) (tried : List wkv) (oks : List wrec) : Prop :=
  evs.length + 1 < 2 ^ 63 ∧
  (∀ (i : Nat) (e : wev), evs[i]? = some e →
    e.put' = true ∧ sint.Z e.rev' = 2 + i ∧ (e.key', e.val') ∈ tried.map pairOf) ∧
  (∀ p ∈ oks, 2 ≤ sint.Z p.rev' ∧ ∃ e, evs[(sint.Z p.rev' - 2).toNat]? = some e ∧
    e.key' = p.key' ∧ e.val' = p.val')

end pure

end linkv3p
end EtcdGrove
end Perennial
