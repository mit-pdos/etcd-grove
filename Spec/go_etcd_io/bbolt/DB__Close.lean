/-
`DB.Close` (bbolt): its spec in bbolt's API (the frozen spec of 2026-11-03; the vocabulary in
`Spec/go_etcd_io/bbolt/Api.lean`, the decisions in `notes/bbolt-spec-decisions.md`). Proof:
`Proof/go_etcd_io/bbolt/DB__Close.lean` (unfinished until bbolt's invariants are designed).
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

/-- `db.Close()`: the database closed, from any goroutine, any number of times. It takes the
three locks, so it waits for every live transaction (a goroutine that holds one and calls
`Close` waits forever, which a WP allows), and every later `Begin` fails. An error is the
environment's (unmapping, unlocking, closing the file): the post says nothing of it; the backend's
`DB.Close_kv` adds `err = nil ∨ ¬ dbCloseOk` as a trust-boundary layer. The committed data stays
`boltState`'s. (Margin: the file is not given back, `notes/bbolt-spec-decisions.md`, D9.) -/
abbrev DB.Close.spec : Prop :=
  ∀ [HasExt osFsExt] (db : Loc) (γ : BoltName),
  {{ isBolt (GF := GF) db γ }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err; True }}

end spec

end bbolt
end EtcdGrove
end Perennial
