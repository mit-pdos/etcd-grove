/- Lean-first (no Rocq counterpart).

`perclient.runClient(id, ops, gen, apply, clock)` (perclient.go): lintest's `runClient`
(`Spec/.../lib/lintest/runClient.lean`) for a client `id < clients`, whose calls are
`apply(id, i)` (`applySpecId`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.perclient.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace perclient

open Iris Iris.BI github_com.anishathalye.porcupine lintest

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.lintest.perclient.Assumptions]

/-- See the file header. -/
abbrev runClient.spec : Prop :=
  ∀ (σ : Type) (S : ModelSpec GF σ) (inOk : GoInterface → IProp GF) (libState : σ → IProp GF)
    (clockVal : w64 → IProp GF)
    (Eapp Eclk : CoPset) (n : Nat) (γ : GName) (apply gen clock : GoFunc) (id ops lr clients : w64),
  (↑lintestN : CoPset) ⊆ ⊤ \ Eapp → (↑lintestN : CoPset) ⊆ ⊤ \ Eclk → 0 ≤ sint.Z id → sint.Z id < sint.Z clients →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.lintest.perclient ∗
      applySpecId S inOk libState Eapp clients apply ∗ genSpec gen inOk ∗ clockSpec clockVal Eclk clock ∗
      inv lintestN (linInv S.M libState clockVal n γ) ∗ clientTok γ (sint.nat id) ([], lr) ∗
      threadTok }}
    (App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.lintest.perclient.runClient))
      (Val #id)) (Val #ops)) (Val #gen)) (Val #apply)) (Val #clock))
  {{ (sl : GoSlice), RET #sl;
      ∃ (hc : List Operation) (Lc : List (OpV × w64)) (lr' : w64),
        sl ↦* hc ∗ clientTok γ (sint.nat id) (Lc, lr') ∗
        ⌜ClientOk id hc Lc ∧ Lc.length = sint.nat ops⌝ ∗ opsIoOk S hc ∗ threadTok }}

end spec

end perclient
end EtcdGrove
end Perennial
