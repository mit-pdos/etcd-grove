/- Lean-first (no Rocq counterpart).

`Check(kvs, clock, clients, ops)` (check.go): `lintest.Run` with the store's model (`Model`),
`Gen`'s random traffic, the given clock, and the store as the library: `apply` runs an input's
operation (`Get`, `Put`, or else `Append`) on the replica `kvs[Replica % len(kvs)]`. For
replicas of one store (`isKV γr`, the slice read-only and not empty) whose state is still the
empty store (the client's half, `rkvVal γr kvEmpty`: no operation has run yet), for any clock
with `clockSpec` (whose invariants are not `lintestN`), under `Run`'s bounds on `clients` and
`ops`, porcupine answers `Ok` (the timeout is 0): the store's operations are logically atomic
against the model (`applySpec`; `Check.lean` says how).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.ModelDefs
public import Proof.github_com.anishathalye.porcupine.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI go_etcd_io.raft.v3
open github_com.anishathalye.porcupine

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]

/-- See the file header. -/
abbrev Check.spec : Prop :=
  ∀ (γr : RKVNames) (ksl : GoSlice) (rs : List Loc) (clockVal : w64 → IProp GF) (t0 : w64)
    (Eclk : CoPset) (clock : GoFunc) (clients ops : w64),
  (↑lintest.lintestN : CoPset) ⊆ ⊤ \ Eclk →
  rs ≠ [] →
  0 ≤ sint.Z clients → sint.Z clients < 2 ^ 31 → 0 ≤ sint.Z ops →
  sint.Z clients * sint.Z ops < 2 ^ 60 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv ∗ context.isClosedchanInit ∗
      ksl ↦*□ rs ∗ ([∗list] r ∈ rs, ∃ γp, isKV γr γp r) ∗ rkvVal γr kvEmpty ∗
      lintest.clockSpec clockVal Eclk clock ∗ clockVal t0 }}
    (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kv.Check)) (Val #ksl)) (Val #clock)) (Val #clients))
      (Val #ops))
  {{ (r : GoString), RET #r; ⌜r = go!"Ok"⌝ }}

end spec

end kv
end EtcdGrove
end Perennial
