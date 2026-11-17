/- Lean-first (no Rocq counterpart).

`ListReadConsistency("", versioner{}, listOptions(in))` (`correctness/consistency.go`), on a
driver's list (k8s 7g step 3): `listConsL in`'s consistency and resource version with no continue
key, or an error where it has none. The driver's package initialization is a precondition (its
versioner's `ParseResourceVersion`). Premise: the input's resource version parses
(the driver draws only such, `kInOk`); the error built from a parse failure (`NewBadRequest` of a
`Sprintf` of the parse error) is not reached.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI k8s_etcd3
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]

/-- See the file header. -/
abbrev ListReadConsistency.spec : Prop :=
  ∀ (x : Input), (parseRVD x.MinRV').isSome →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness ∗
      isPkgInit pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ListReadConsistency))
      (Val #([] : GoString))) (Val #(versionerV))) (Val #(listOptsV x)))
  {{ (c : GoString) (rv : w64) (ck : GoString) (err : GoInterface),
      RET (PairV (PairV (PairV #c #rv) #ck) #err);
      ⌜match listConsL x with
        | some (cs, r) => c = rconsStr cs ∧ rv = r ∧ ck = [] ∧ err = GoInterface.nil
        | none => err ≠ GoInterface.nil⌝ }}

end spec

end k8s_correctness
end EtcdGrove
end Perennial
