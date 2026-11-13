/-
The package-initialization instances of raft's root package (the part's translation, names-only but
`IsEmptyHardState`/`MustSync`) and of the raft and protobuf packages it imports (`raftpb`, `quorum`,
`tracker`, `confchange`: the main tree's translations; protobuf-go's `internal/impl`,
`runtime/protoimpl`), for the part `LinuxFs/`, as the main tree's `Proof/go_etcd_io/raft/v3/Base.lean`
declares them, which the part cannot import (it imports the main raft root package, whose names the
part's raft root declares too). Their facts are `True` here. (The main tree's raft root fact is
stronger: the part's WAL does not read raft's variables yet; `emptyState`, which `IsEmptyHardState`
reads, would join it.) Their `wp_initialize'`: `LinuxFs/Proof/go_etcd_io/raft/v3/InitPb.lean` (a copy of
the main tree's) and the generated `Init.lean`s. WAL package init, 2026-11-13.
-/
module

public import LinuxFs.GeneratedProof.go_etcd_io.raft.v3
public import GeneratedProof.go_etcd_io.raft.v3.raftpb
public import GeneratedProof.go_etcd_io.raft.v3.quorum
public import GeneratedProof.go_etcd_io.raft.v3.tracker
public import GeneratedProof.go_etcd_io.raft.v3.confchange
public import GeneratedProof.google_golang_org.protobuf.internal.impl
public import GeneratedProof.google_golang_org.protobuf.runtime.protoimpl
public import LinuxFs.Proof.google_golang_org.protobuf.proto.PkgInit
public import LinuxFs.Proof.os.PkgInit
public import Perennial.Proof.strconv.Base
public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.context
public import Perennial.Proof.sync
public import Perennial.Proof.fmt
public import Perennial.Proof.slices
public import Perennial.Proof.cmp
public import Perennial.Proof.encoding.binary
public import Perennial.Proof.strings
public import Perennial.Proof.math
public import Perennial.Proof.crypto.rand
public import Perennial.Proof.bytes
public import Perennial.Proof.log
public import Perennial.Proof.io
public import Perennial.Proof.errors

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

namespace go_etcd_io.raft.v3

instance protobuf_impl_isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.google_golang_org.protobuf.internal.impl :=
  define_is_pkg_init iprop(True)
instance protobuf_impl_get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.protobuf.internal.impl :=
  build_get_is_pkg_init_wf
instance protoimpl_isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.google_golang_org.protobuf.runtime.protoimpl :=
  define_is_pkg_init iprop(True)
instance protoimpl_get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.protobuf.runtime.protoimpl :=
  build_get_is_pkg_init_wf
instance raftpb_isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb :=
  define_is_pkg_init iprop(True)
instance raftpb_get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb :=
  build_get_is_pkg_init_wf
instance quorum_isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.raft.v3.quorum :=
  define_is_pkg_init iprop(True)
instance quorum_get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.raft.v3.quorum :=
  build_get_is_pkg_init_wf
instance tracker_isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.raft.v3.tracker :=
  define_is_pkg_init iprop(True)
instance tracker_get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.raft.v3.tracker :=
  build_get_is_pkg_init_wf
instance confchange_isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.raft.v3.confchange :=
  define_is_pkg_init iprop(True)
instance confchange_get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.raft.v3.confchange :=
  build_get_is_pkg_init_wf
instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.raft.v3 :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.raft.v3 :=
  build_get_is_pkg_init_wf

end go_etcd_io.raft.v3

end init

end Perennial
