/-
`os.File.Readdirnames` (the standard library, names-only here: no file-system model). The trust boundary.
Lean-first (no Rocq counterpart); etcd PR #22046 (branch `pr-verify/etcd-22046`), for
`(*snap.Snapshotter).ReleaseSnapDBs`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `f.Readdirnames(n)` of a directory handle: some list of names (a read-only slice), and
nil or an error; the handle stays open. Nothing is said about the names (no file-system model). -/
abbrev os.File.Readdirnames.spec : Prop :=
  ∀ (f : Loc) (dir : GoString) (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.os ∗ fs.dirHandle f dir }}
    (App (Val (f @!! go.GoType.PointerType _root_.Perennial.os.File.ty @!! go!"Readdirnames")) (Val #n))
  {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err);
      fs.dirHandle f dir ∗ (∃ names : List GoString, sl ↦*{DFrac.discard} names) ∗
      fsResult err iprop(True) iprop(True) }}

end spec

end EtcdGrove
end Perennial
