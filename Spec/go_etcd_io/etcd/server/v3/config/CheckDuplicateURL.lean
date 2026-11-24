/-
`config.CheckDuplicateURL(urlsmap)` (`config.go:331-343`); claim #34, stage 2,
2026-11-25: translated with its body). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.config.Defs
public import GeneratedProof.go_etcd_io.etcd.server.v3.config
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base
public import Proof.net.http.Boundary

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`CheckDuplicateURL(m)`** of a URLs map (read-only, with its URL slices): some boolean. -/
abbrev config.CheckDuplicateURL.spec : Prop :=
  ∀ (mp : Loc) (m : GMap GoString GoSlice) (urls : GoString → List _root_.Perennial.net.url.URL),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.config ∗ mp ↦$□ m ∗ [∗map] k ↦ sl ∈ m, sl ↦*□ urls k }}
    (App (Val (@! go_etcd_io.etcd.server.v3.config.CheckDuplicateURL)) (Val #mp))
  {{ (b : Bool), RET #b; True }}

end spec

end EtcdGrove
end Perennial
