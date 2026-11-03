/-
`DB.Info` (bbolt): its spec in bbolt's API (the frozen spec of 2026-11-03; the vocabulary in
`Spec/go_etcd_io/bbolt/Api.lean`, the decisions in `notes/bbolt-spec-decisions.md`). Proof:
`Proof/go_etcd_io/bbolt/DB__Info.lean` (unfinished until bbolt's invariants are designed).
-/
module

public import Spec.go_etcd_io.bbolt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
/- Every bbolt spec is stated over OsFs's semantics (round 11, D22: the default `osFs_semantics`,
whose `pwrite` within one aligned OS page is all-or-nothing): the binder `∀ [HasExt osFsExt]` at
the head of each triple (a section variable is dropped from a definition that does not use it),
and in the signature of each vocabulary predicate, so that every statement carries it (checked
with `#check`). -/
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `db.Info()` while a transaction of `db` is live: a fresh `Info` (Go asserts `db.data != nil`
and reads it without `mmaplock`; a live transaction excludes `Close` and a remap). -/
abbrev DB.Info.spec : Prop :=
  ∀ [HasExt osFsExt] (db tx : Loc) (γ : BoltName) (q : Qp) (T : TxView),
  {{ isBolt (GF := GF) db γ ∗ txDB tx db ∗ boltTx tx γ q T }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Info")) (Val #()))
  {{ (i : Loc), RET #i; boltTx tx γ q T ∗ ∃ v : Info, i ↦ v }}

end spec

end bbolt
end EtcdGrove
end Perennial
