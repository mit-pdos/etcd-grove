/- Lean-first (no Rocq counterpart).

`settle(hh, revs, c, b, full, in, out)` (export.go, notes/k8s-dist-k9.md §2.2): the configurations
`c` settles to, each pending write taking effect (or dropped, where it has no effect) at one of
`landingsL`'s revisions, in any order: exactly `GoSettle`'s (duplicates allowed), each well-formed.
`SettleOk`: the bounds the proof needs (K9-6).
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
abbrev settle.spec : Prop :=
  ∀ (hh : Loc) (r : Revs) (R : RevsL) (c : mcfg) (g : GCfg) (b : w64) (full : Bool) (x : Input)
    (y : Output),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ hhOwn hh ∗ revsOwn r R ∗ cfgOwn c g ∗
      ⌜HWf g.st ∧ SettleOk R y g⌝ }}
    (App (App (App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.settle)) (Val #hh)) (Val #r)) (Val #c)) (Val #b)) (Val #full)) (Val #x)) (Val #y))
  {{ (sl : GoSlice) (cs : List mcfg) (gs : List GCfg), RET #sl; sl ↦* cs ∗
      ([∗list] c;g ∈ cs;gs, cfgOwn c g) ∗
      ⌜(∀ e, e ∈ gs ↔ GoSettle R b full x y g e) ∧ ∀ e ∈ gs, HWf e.st⌝ }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
