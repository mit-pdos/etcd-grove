/-
The model of Go's `log.Logger` that bbolt's default logger rests on (the trust boundary: `log`
is translated names-only). `isLog l`: the `*log.Logger` at `l` is set up (persistent); its
`Output` (`Spec/log/Logger__Output.lean`, an axiom) writes a line and returns. bbolt's default
logger writes to `io.Discard`, so nothing it logs is observable.
-/
module

public import GeneratedProof.go_etcd_io.bbolt
public import Perennial.Golang.Theory.Bytes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI

section model
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

axiom isLog (l : Loc) : IProp GF
axiom isLog_persistent (l : Loc) : Persistent (isLog (GF := GF) l)

attribute [instance] isLog_persistent

end model

end bbolt
end EtcdGrove
end Perennial
