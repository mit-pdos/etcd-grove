/- Lean-first (no Rocq counterpart).

`Model()` (linkv.go): the key-value store's porcupine model, against `kvM decOp` (`linkvS`,
`Defs.lean`): `Partition`, `StepContext` and `Hash` are `nil`; `Init` returns a value of the
initial state (one empty configuration); `Equal` meets porcupine's `equalSpec` of `linkvS` (it
returns `true` only on equal lists, so on one state); and `Step` steps as `kvM decOp` does, on a
state whose configurations' lengths are below `n < 2^63` (`stRepB n`), returning a state whose
lengths are below `n + 1`.

**Not porcupine's `isModel linkvS m`**: its `stepSpec` is for every state value `Step` may return,
with no bound, and no model of a Go value of `Model()` meets it in Perennial's semantics: after
`2^63 - 1` failed puts on one configuration, `insertSorted`'s `make([]kvEntry, 0, len(pend)+1)`
overflows and panics there (`set`'s likewise, with `2^63 - 1` distinct keys). Go cannot reach it
(memory bounds a slice of 32-byte entries far below), nor can porcupine's checker on a history of
fewer than `2^60` operations (each linearization steps each operation once), but neither bound is
visible to `stepSpec`. So `Step`'s spec here carries the lengths' bound (`notes/STATUS.md`, D20).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.linkv github_com.anishathalye.porcupine

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv.Assumptions]

/-- `Init()` returns a value of the initial state, its lengths below `1`. -/
def initSpecB (f : GoFunc) : IProp GF :=
  iprop({{ True }}
    (App (Val #f) (Val #()))
  {{ (v : GoInterface), RET #v; stRepB 1 v kvInit }})

/-- `Step(state, input, output)` steps as `kvM decOp` does, on a state whose lengths are below
`n < 2^63`; the next state's are below `n + 1`. -/
def stepSpecB (f : GoFunc) : IProp GF :=
  iprop(∀ (n : Nat) (v : GoInterface) (S : KVSet GoString GoString) (i o : GoInterface),
    {{ ⌜n < 2 ^ 63⌝ ∗ stRepB n v S ∗ linkvS.ioOk i o }}
      (App (App (App (Val #f) (Val #v)) (Val #i)) (Val #o))
    {{ (ok : Bool) (v' : GoInterface), RET (PairV #ok #v');
        ⌜ok = ((kvM decOp).step S (i, o)).isSome⌝ ∗
        match (kvM decOp).step S (i, o) with
        | some S' => stRepB (n + 1) v' S'
        | none => iprop(True) }})

/-- See the file header. -/
abbrev Model.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkv }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkv.Model)) (Val #()))
  {{ (m : Model), RET #m;
      ⌜m.Partition' = func.nil⌝ ∗ initSpecB m.Init' ∗
      ⌜m.StepContext' = func.nil ∧ m.Step' ≠ func.nil⌝ ∗ stepSpecB m.Step' ∗ isEqHash linkvS m }}

end spec

end linkv
end EtcdGrove
end Perennial
