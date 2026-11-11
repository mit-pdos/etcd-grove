/- Lean-first (no Rocq counterpart).

`genList(n, in, c, hasC)` (k8setcd3.go; stage 7e-4): the List `genFrom` draws on `in` (a workload
key, fields that fit an object): an input `Gen` may return (`GenIn`), with `in`'s cached-object
choice unchanged.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Calls

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg state)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev genList.spec : Prop :=
  ∀ (n : w64) (x : Input) (c : Obj) (hasC : Bool),
  x.Key' ∈ wkKeysL → x.UID'.length < 256 → x.Node'.length < 256 → x.App'.length < 256 →
  x.Val'.length ≤ 2 ^ 20 → (x.Match' = W64 0 ∨ x.Match' = W64 1 ∨ x.Match' = W64 2) →
  0 ≤ sint.Z x.Limit' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 }}
    (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.genList))
      (Val #n)) (Val #x)) (Val #c)) (Val #hasC))
  {{ (y : Input), RET #y; ⌜GenIn y ∧ y.UseCached' = x.UseCached'⌝ }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
