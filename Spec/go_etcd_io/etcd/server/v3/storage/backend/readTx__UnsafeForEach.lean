/-
`UnsafeForEach` (the backend, `read_tx.go`, promoted from `baseReadTx`). `rt.UnsafeForEach(bucket, visitor)`
of the held shared read transaction: the visitor on `rtForEach` of the readers' state, stopped by its first error.
Lean-first (no Rocq counterpart); auth-schema-srv A6 (the promotion wrapper A2's review deferred).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend backend

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `rt.UnsafeForEach(bucket, visitor)` of the held shared read transaction, with any share `p` of
bbolt's transaction and no open share (as `readTx.UnsafeRange`): `baseReadTx.UnsafeForEach` of the
embedded base, the visitor, on the `i`-th entry `e` of `rtForEach rv bi`, getting half of the share
and the slices as `UnsafeRange` returns them (`rdB`). -/
abbrev backend.readTx.UnsafeForEach.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (rt : Loc) (rtx : Loc) (rv : RView)
    (p : Qp) (bk : GoInterface) (bi : BucketInfo) (fn : GoFunc) (I : Nat → IProp GF)
    (E : Nat → GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isBackend γ P W Pk b ∗ bF go!"readTx" b ↦□ rt ∗ rtHeldF γ P b rtx rv p ∗ isBucket bk bi ∗ I 0 ∗
      □ (∀ (i : Nat) (e : Ent) (k v : GoSlice), ⌜(rtForEach rv bi)[i]? = some e⌝ →
          {{ I i ∗ txLive rtx p.half ∗ rdB rtx k e.1 ∗ rdB rtx v e.2 }}
            (App (App (Val #fn) (Val #k)) (Val #v))
          {{ (err : GoInterface), RET #err; txLive rtx p.half ∗
              ((⌜err = GoInterface.nil⌝ ∗ I (i + 1)) ∨ (⌜err ≠ GoInterface.nil⌝ ∗ E i err)) }}) }}
    (App (App (Val (rt @!! go.GoType.PointerType readTx.ty @!! go!"UnsafeForEach")) (Val #bk)) (Val #fn))
  {{ (err : GoInterface), RET #err; rtHeldF γ P b rtx rv p ∗
      ((⌜err = GoInterface.nil⌝ ∗ I (rtForEach rv bi).length) ∨
       (∃ i : Nat, ⌜err ≠ GoInterface.nil ∧ i < (rtForEach rv bi).length⌝ ∗ E i err)) }}

end spec

end EtcdGrove
end Perennial
