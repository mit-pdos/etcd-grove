/-
`os.FileInfo` is an alias of `io/fs.FileInfo` (`type FileInfo = fs.FileInfo`), which
Perennial's translation of `os` keeps opaque (`os.FileInfo.ty`, with no underlying type), so a
variable of that type cannot be allocated. `OsFileInfoAssumptions` says its underlying type is
`fs.FileInfo`'s (and gives `fs.FileInfo`'s type assumptions), and that `os.FileMode`'s is `uint32`: a Goose gap (an alias should be translated as the type it names), taken as an
instance hypothesis until Perennial's `os` is retranslated.
-/
module

public import GeneratedProof.go_etcd_io.bbolt
public import Proof.go_etcd_io.bbolt.Init

@[expose] public section

namespace Perennial
namespace EtcdGrove

open Iris

section cls
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

class OsFileInfoAssumptions : Prop where
  underlying : go.UnderlyingDirectedEq _root_.Perennial.os.FileInfo.ty
    _root_.Perennial.io.fs.FileInfo.underlying
  /-- `fs.FileInfo`'s own (bbolt's `Assumptions` do not reach `io/fs`) -/
  fs_fileInfo : _root_.Perennial.io.fs.FileInfo.TypeAssumptions
  /-- a value of `fs.FileInfo`'s (opaque) underlying type is an interface in memory -/
  into_val : IntoValTypedUnderlying (GF := GF) GoInterface _root_.Perennial.io.fs.FileInfo.underlying
  /-- `os.FileMode` (an alias of `fs.FileMode`, a `uint32`), opaque as well -/
  fileMode : go.UnderlyingDirectedEq _root_.Perennial.os.FileMode.ty go.uint32

attribute [instance] OsFileInfoAssumptions.underlying OsFileInfoAssumptions.fs_fileInfo
  OsFileInfoAssumptions.into_val OsFileInfoAssumptions.fileMode

end cls

end EtcdGrove
end Perennial
