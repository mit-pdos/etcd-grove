/- Lean-first (no Rocq counterpart).

`hashString(s)` (check.go): some hash of `s` (FNV-1a; nothing is claimed of it).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.ModelDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI go_etcd_io.raft.v3
open github_com.anishathalye.porcupine

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]

/-- See the file header. -/
abbrev hashString.spec : Prop :=
  ∀ (s : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kv.hashString)) (Val #s))
  {{ (h : w64), RET #h; True }}

end spec

end kv
end EtcdGrove
end Perennial
