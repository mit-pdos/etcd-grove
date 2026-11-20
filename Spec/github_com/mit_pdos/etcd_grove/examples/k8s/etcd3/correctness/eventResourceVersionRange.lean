/-
Lean-first (no Rocq counterpart).

`eventResourceVersionRange(events, versioner)` (`correctness/watch.go`) of read-only events of views
`rs` with the driver's versioner, when the pure function answers without error
(`evRangeR rs = some o`: every event but the Error ones holds a driver's `*Obj` and has a known type):
no error and the range `o` (`rangeRep`: `nil` for none, else a fresh `*ResourceVersionRange`)
(k8s 7g step 5).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchVocab

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI map
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]
variable [driver_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev eventResourceVersionRange.spec : Prop :=
  ∀ (sl : GoSlice) (rs : List REv) (o : Option (w64 × w64)),
  evRangeR rs = some o →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness ∗
      isPkgInit pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ evsRO sl rs }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.eventResourceVersionRange))
      (Val #sl)) (Val #(versionerV)))
  {{ (p : Loc) (err : GoInterface), RET (PairV #p #err); ⌜err = GoInterface.nil⌝ ∗ rangeRep p o }}

end spec

end k8s_correctness
end EtcdGrove
end Perennial
