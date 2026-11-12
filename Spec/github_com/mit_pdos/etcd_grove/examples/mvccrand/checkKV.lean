/- Lean-first (no Rocq counterpart).

`checkKV(kv, k, e, keysOnly)` (`examples/mvccrand/mvccrand.go`): returns when the key-value at
`kv` is the model's `e` of the key `k` (`kvMatches`: the key, the create and mod revisions, the
version; a keys-only read's value empty, else the value and the lease). The key-value is read
through its struct (whose points-to the call keeps: the tester reads a key-value once) and its two
slices (given back), at any fractions (a range's result is owned, a watch event's read-only).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.check

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccrand

section model
variable [GooseExts]

/-- **The key-value `v` (key `kk`, value `vv`) is the model's `e` of the key `k`**, as `checkKV`
compares them (`keysOnly`: no value, the lease unchecked). -/
def kvMatches (v : go_etcd_io.etcd.api.v3.mvccpb.KeyValue) (kk vv : GoString) (k : GoString)
    (e : kvRec) (keysOnly : Bool) : Prop :=
  kk = k ∧ v.CreateRevision' = e.create' ∧ v.ModRevision' = e.mod' ∧ v.Version' = e.ver' ∧
    (if keysOnly then vv = [] else vv = e.val' ∧ v.Lease' = e.lease')

end model

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]

/-- See the file header. -/
abbrev checkKV.spec : Prop :=
  ∀ (p : Loc) (v : go_etcd_io.etcd.api.v3.mvccpb.KeyValue) (dq dk dv : DFrac) (kk vv : GoString)
    (k : GoString) (e : kvRec) (keysOnly : Bool),
  kvMatches v kk vv k e keysOnly →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccrand ∗
      p ↦{dq} v ∗ v.Key' ↦*{dk} kk ∗ v.Value' ↦*{dv} vv }}
    (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.mvccrand.checkKV))
      (Val #p)) (Val #k)) (Val #e)) (Val #keysOnly))
  {{ RET #(); v.Key' ↦*{dk} kk ∗ v.Value' ↦*{dv} vv }}

end spec

end mvccrand
end EtcdGrove
end Perennial
