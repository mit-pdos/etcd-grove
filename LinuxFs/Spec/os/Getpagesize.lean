/-
`os.Getpagesize()` (names-only in Perennial's `os`): the system's memory page size,
`syscall.Getpagesize()`, which is the constant 4096 on linux/amd64 (`syscall/syscall_linux_amd64.go`:
`func Getpagesize() int { return 4096 }`), the platform this repository's models assume. bbolt's
`internal/common` initializes `DefaultPageSize` with it (`page.go`). The trust boundary: an axiom,
`Proof/os/Getpagesize.lean`.
-/
module

public import LinuxFs.Code.os
public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev os.Getpagesize.spec : Prop :=
  {{ (True : IProp GF) }}
    (App (Val (@! os.Getpagesize)) (Val #()))
  {{ RET #(W64 4096); True }}

end spec

end EtcdGrove
end Perennial
