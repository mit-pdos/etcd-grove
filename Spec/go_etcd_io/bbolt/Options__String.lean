/-
`(*Options).String` (bbolt): its spec in bbolt's API (the frozen spec of 2026-11-03,
`notes/bbolt-spec-decisions.md`, D13's family). `Options` is axiomatized (a translator gap,
`Proof/go_etcd_io/bbolt/Options.lean`'s header), so its proof,
`Proof/go_etcd_io/bbolt/Options__String.lean`, is a trust-boundary axiom until `Options` is
translated.
-/
module

public import Spec.go_etcd_io.bbolt.Options

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

/-- **`(*Options).String()` reads the options and returns a string** (round 7, D13's family:
`Options` is axiomatized). True: `String` only reads the 15 fields and formats them with
`fmt.Sprintf` (`Duration`'s `String`, `FreelistType` as a string, `%p` of a func and an interface),
which cannot fail. With it, `Open` proves `logArgOk (optsAt opts dq o) 's' (*Options)`. -/
abbrev Options.String.spec : Prop :=
  ∀ (l : Loc) (dq : DFrac) (o : OptsM),
  {{ optsAt (GF := GF) l dq o ∗ ⌜loggerPtrOk o.logger⌝ }}
    (App (Val #(methods (go.GoType.PointerType go_etcd_io.bbolt.Options.ty) go!"String" #l))
      (Val #()))
  {{ (s : GoString), RET #s; optsAt l dq o }}

end spec

end bbolt
end EtcdGrove
end Perennial
