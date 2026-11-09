/- Lean-first (no Rocq counterpart).

`inRange(key, end, k)` (`examples/mvccrand/mvccrand.go`): whether the key `k` is in the range
`[key, end)` (`end` nil: the key alone; empty: every key from `key` on), as mvcc's reads see a
range (`inRangeM`, the tester's model of it).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccrand

/-- **A range's keys** (the tester's model): the one key when the end is nil, else `[key, e)`, an
empty `e` unbounded (mvcc's `inRange`). -/
def inRangeM (endNil : Bool) (key e k : GoString) : Bool :=
  if endNil then decide (k = key) else mvcc.inRange key e k

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]

/-- See the file header. -/
abbrev inRange.spec : Prop :=
  ∀ (key endk : GoSlice) (kk e : GoString) (k : GoString) (dq dq' : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccrand ∗
      key ↦*{dq} kk ∗ endk ↦*{dq'} e }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.mvccrand.inRange))
      (Val #key)) (Val #endk)) (Val #k))
  {{ RET #(inRangeM (decide (endk = slice.nil)) kk e k); key ↦*{dq} kk ∗ endk ↦*{dq'} e }}

end spec

end mvccrand
end EtcdGrove
end Perennial
