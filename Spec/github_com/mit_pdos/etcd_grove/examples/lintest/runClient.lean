/- Lean-first (no Rocq counterpart).

`runClient(id, ops, gen, apply, clock)` (lintest.go): one client's loop, under `Run`'s
invariant (`linInv`, `Proof/.../lintest/Defs.lean`). It starts with its ghost value empty
(`clientTok γ id ([], lr)`) and returns its trace `hc` (one `Operation` per call of `apply`,
`ops` of them if `ops ≥ 0`), with its records `Lc` in the ghost log: the trace's operation
`j` is the client's `j`-th linearized operation, called before and returned after its
linearization point (`ClientOk`), and owns what porcupine's `Step` needs (`opsIoOk`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest

open Iris Iris.BI github_com.anishathalye.porcupine

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.Assumptions]

/-- See the file header. -/
abbrev runClient.spec : Prop :=
  ∀ (σ : Type) (S : ModelSpec GF σ) (libState : σ → IProp GF) (clockVal : w64 → IProp GF)
    (Eapp Eclk : CoPset) (n : Nat) (γ : GName) (apply gen clock : GoFunc) (id ops lr : w64),
  (↑lintestN : CoPset) ⊆ ⊤ \ Eapp → (↑lintestN : CoPset) ⊆ ⊤ \ Eclk → 0 ≤ sint.Z id →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest ∗
      applySpec S libState Eapp apply ∗ genSpec gen ∗ clockSpec clockVal Eclk clock ∗
      inv lintestN (linInv S.M libState clockVal n γ) ∗ clientTok γ (sint.nat id) ([], lr) }}
    (App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lintest.runClient))
      (Val #id)) (Val #ops)) (Val #gen)) (Val #apply)) (Val #clock))
  {{ (sl : GoSlice), RET #sl;
      ∃ (hc : List Operation) (Lc : List (OpV × w64)) (lr' : w64),
        sl ↦* hc ∗ clientTok γ (sint.nat id) (Lc, lr') ∗
        ⌜ClientOk id hc Lc ∧ Lc.length = sint.nat ops⌝ ∗ opsIoOk S hc }}

end spec

end lintest
end EtcdGrove
end Perennial
