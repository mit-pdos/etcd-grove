/-
`fileutil.NewFileReader(f)` (filereader.go): `&fileReader{f}` as a `FileReader` (an interface value of
dynamic type `*fileReader`, its struct holding `f`). Proved in
`LinuxFs/Proof/go_etcd_io/etcd/client/pkg/v3/fileutil/NewFileReader.lean`. Lean-first.
-/
module

public import LinuxFs.GeneratedProof.go_etcd_io.etcd.client.pkg.v3.fileutil
public import LinuxFs.Proof.os.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

/-- See the file header. -/
abbrev go_etcd_io.etcd.client.pkg.v3.fileutil.NewFileReader.spec : Prop :=
  ∀ (f : Loc),
  {{ (True : IProp GF) }}
    (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.NewFileReader)) (Val #f))
  {{ (rl : Loc), RET #(interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.fileReader.ty) #rl);
      rl ↦ go_etcd_io.etcd.client.pkg.v3.fileutil.fileReader.mk f }}

end spec

end EtcdGrove
end Perennial
