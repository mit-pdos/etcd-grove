/- Lean-first (no Rocq counterpart).

**A local copy of the driver's spec** (`notes/logkv-eval-rw.md`): `lintest`'s `runClient.spec`
with the library's spec `applySpecTok` (`applySpec` with the goroutine's thread token,
`Proof/.../lintest/logkvrw/DriverTok.lean`) and the client's thread token in its pre and post.

`runClient(id, ops, gen, apply, clock)` (lintest.go): one client's loop, under `Run`'s
invariant (`linInv`, `Proof/.../lintest/Defs.lean`). It starts with its ghost value empty
(`clientTok γ id ([], lr)`) and returns its trace `hc` (one `Operation` per call of `apply`,
`ops` of them if `ops ≥ 0`; each input is from `gen`, so `apply` gets an input with
`inOk`), with its records `Lc` in the ghost log: the trace's operation
`j` is the client's `j`-th linearized operation, called before and returned after its
linearization point (`ClientOk`), and owns what porcupine's `Step` needs (`opsIoOk`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.logkvrw.DriverTok

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest
namespace logkvrw

open Iris Iris.BI github_com.anishathalye.porcupine

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.Assumptions]

/-- See the file header. -/
abbrev runClientTok.spec : Prop :=
  ∀ (σ : Type) (S : ModelSpec GF σ) (inOk : GoInterface → IProp GF) (libState : σ → IProp GF)
    (clockVal : w64 → IProp GF)
    (Eapp Eclk : CoPset) (n : Nat) (γ : GName) (apply gen clock : GoFunc) (id ops lr : w64),
  (↑lintestN : CoPset) ⊆ ⊤ \ Eapp → (↑lintestN : CoPset) ⊆ ⊤ \ Eclk → 0 ≤ sint.Z id →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest ∗
      applySpecTok S inOk libState Eapp apply ∗ genSpec gen inOk ∗ clockSpec clockVal Eclk clock ∗
      inv lintestN (linInv S.M libState clockVal n γ) ∗ clientTok γ (sint.nat id) ([], lr) ∗ threadTok }}
    (App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lintest.runClient))
      (Val #id)) (Val #ops)) (Val #gen)) (Val #apply)) (Val #clock))
  {{ (sl : GoSlice), RET #sl;
      ∃ (hc : List Operation) (Lc : List (OpV × w64)) (lr' : w64),
        sl ↦* hc ∗ clientTok γ (sint.nat id) (Lc, lr') ∗
        ⌜ClientOk id hc Lc ∧ Lc.length = sint.nat ops⌝ ∗ opsIoOk S hc ∗ threadTok }}

end spec

end logkvrw
end lintest
end EtcdGrove
end Perennial
