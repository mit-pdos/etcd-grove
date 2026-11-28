/- Lean-first (no Rocq counterpart).

`landings(revs, c, w, b, full, in, out)` (export.go, notes/k8s-dist-k9.md §2.5): exactly
`landingsL`, in a fresh slice (`settle` reads it only).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.SharedLand

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (mstore mcfg Input Output Revs)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev landings.spec : Prop :=
  ∀ (r : Revs) (R : RevsL) (c : mcfg) (w : Input) (b : w64) (full : Bool) (x : Input) (y : Output),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ revsOwn r R }}
    (App (App (App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.landings)) (Val #r)) (Val #c)) (Val #w)) (Val #b)) (Val #full)) (Val #x)) (Val #y))
  {{ (sl : GoSlice), RET #sl; sl ↦* landingsL R c.st'.rv' w b full x y ∗
      ownSliceCap w64 sl (DFrac.own 1) }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
