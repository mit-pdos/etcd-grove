/-
`fileutil.Exist(name)` (fileutil.go): `os.Stat(name)`, true iff it returns no error. Generic in the
`Stat` spec (the part's `os.Stat.wp_dirS`, `wp_absentS`, `wp_fileS`): for every triple
`{{ P }} os.Stat(name) {{ fi err, Q err }}`, `Exist` gives `Q err` for the `err` whose nil-ness
it returns. Proved in `LinuxFs/Proof/go_etcd_io/etcd/client/pkg/v3/fileutil/Exist.lean`. Lean-first.
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
abbrev go_etcd_io.etcd.client.pkg.v3.fileutil.Exist.spec : Prop :=
  ∀ (name : GoString) (P : IProp GF) (Q : GoInterface → IProp GF),
  ({{ P }} (App (Val (@! os.Stat)) (Val #name))
    {{ (fi : GoInterface) (err : GoInterface), RET (PairV #fi #err); Q err }}) →
  {{ P }}
    (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.Exist)) (Val #name))
  {{ (b : Bool), RET #b; ∃ err : GoInterface, ⌜b = decide (err = interface.nil)⌝ ∗ Q err }}

end spec

end EtcdGrove
end Perennial
