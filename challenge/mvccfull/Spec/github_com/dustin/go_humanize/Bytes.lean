/-
`go_humanize.Bytes`: the trust boundary (`github.com/dustin/go-humanize` is names-only). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.dustin.go_humanize.Assumptions]

/-- `humanize.Bytes(n)` returns some string. -/
abbrev go_humanize.Bytes.spec : Prop :=
  ∀ (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.dustin.go_humanize }}
    (App (Val (@! _root_.Perennial.github_com.dustin.go_humanize.Bytes)) (Val #n))
  {{ (str : GoString), RET #str; True }}

end spec

end EtcdGrove
end Perennial
