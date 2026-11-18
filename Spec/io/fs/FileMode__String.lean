/-
`fs.FileMode.String` (this repository's `io/fs`, project `bboltfs`, translated with its body since
2026-11-18): its spec. bbolt's `Open` logs its mode with `%s` (`db.go`'s `lg.Infof("Opening db file
(%s) with mode %s and with options: %s", path, mode, options)`), so the mode is a Stringer argument
of the logger (`Proof/go_etcd_io/bbolt/Open/FileModeString.lean`'s `fileMode_logArgOk`). Proof:
`Proof/io/fs/FileMode__String.lean`.
-/
module

public import GeneratedProof.io.fs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`mode.String()`** returns some string, needing nothing: it reads only its receiver and never
panics (its `[32]byte` buffer holds every mode's letters: at most 13 type letters, then 9 permission
letters, or a hyphen and 9). -/
abbrev fs.FileMode.String.spec : Prop :=
  ∀ (mode : w32),
  {{ (True : IProp GF) }}
    (App (Val #(methods io.fs.FileMode.ty go!"String" #mode)) (Val #()))
  {{ (s : GoString), RET #s; True }}

end spec

end EtcdGrove
end Perennial
