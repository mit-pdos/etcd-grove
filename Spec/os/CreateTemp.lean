/-
`os.CreateTemp` (names-only here: no file-system model). Lean-first (no Rocq counterpart); etcd
PR #22046 (branch `pr-verify/etcd-22046`), for `(*snap.Snapshotter).SaveDBFrom`.
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

/-- `os.CreateTemp(dir, pattern)`: an open handle `f` of a new file named `p` (`f.Name()`), with
the right to remove `p`; or an error. -/
abbrev os.CreateTemp.spec : Prop :=
  ∀ (dir pattern : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.os }}
    (App (App (Val (@! _root_.Perennial.os.CreateTemp)) (Val #dir)) (Val #pattern))
  {{ (f : Loc) (err : GoInterface), RET (PairV #f #err);
      fsResult err iprop(∃ p : GoString, fs.dirHandle f p ∗ □ fs.fileName f p ∗ fs.removable p)
        iprop(True) }}

end spec

end EtcdGrove
end Perennial
