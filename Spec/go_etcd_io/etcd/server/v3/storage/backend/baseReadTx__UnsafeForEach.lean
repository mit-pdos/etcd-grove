/-
`UnsafeForEach` (the backend, `read_tx.go`). `base.UnsafeForEach(bucket, visitor)` of a read transaction
(shared or concurrent): the visitor on `rtForEach` of its state (bbolt's entries whose keys the read buffer
does not hold, in key order, then the buffer's), stopped by its first error.
Lean-first (no Rocq counterpart); auth-schema-srv A2 (`notes/auth-schema-srv-a2-draft.md` §4).
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

/-- `base.UnsafeForEach(bucket, visitor)` (`baseRd`, as `UnsafeRange`): the buffer's keys collected,
then bbolt's walk under `txMu` with those keys skipped, then the buffer's walk. The visitor, on the
`i`-th entry `e` of `rtForEach rv bi`, gets half of the reader's share of `txLive` and the slices as
`UnsafeRange` returns them (`rdB`: the buffer's, or bbolt's valid while `rtx` is open). -/
abbrev backend.baseReadTx.UnsafeForEach.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (base : Loc) (dq : DFrac) (rtx : Loc) (rv : RView) (q : Qp)
    (bk : GoInterface) (bi : BucketInfo) (fn : GoFunc) (I : Nat → IProp GF)
    (E : Nat → GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      baseRd γ P base dq rtx rv q ∗ isBucket bk bi ∗ I 0 ∗
      □ (∀ (i : Nat) (e : Ent) (k v : GoSlice), ⌜(rtForEach rv bi)[i]? = some e⌝ →
          {{ I i ∗ txLive rtx q.half ∗ rdB rtx k e.1 ∗ rdB rtx v e.2 }}
            (App (App (Val #fn) (Val #k)) (Val #v))
          {{ (err : GoInterface), RET #err; txLive rtx q.half ∗
              ((⌜err = GoInterface.nil⌝ ∗ I (i + 1)) ∨ (⌜err ≠ GoInterface.nil⌝ ∗ E i err)) }}) }}
    (App (App (Val (base @!! go.GoType.PointerType baseReadTx.ty @!! go!"UnsafeForEach")) (Val #bk)) (Val #fn))
  {{ (err : GoInterface), RET #err; baseRd γ P base dq rtx rv q ∗
      ((⌜err = GoInterface.nil⌝ ∗ I (rtForEach rv bi).length) ∨
       (∃ i : Nat, ⌜err ≠ GoInterface.nil ∧ i < (rtForEach rv bi).length⌝ ∗ E i err)) }}

end spec

end EtcdGrove
end Perennial
