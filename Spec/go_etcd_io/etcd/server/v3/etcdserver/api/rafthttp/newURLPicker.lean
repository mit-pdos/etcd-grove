/-
`newURLPicker(urls)` (`urlpick.go`; rafthttp stage 6b). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Picker

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`newURLPicker(urls)`** of a non-empty slice of URLs satisfying `P` (read-only): a picker of
URLs satisfying `P`. -/
abbrev rafthttp.newURLPicker.spec : Prop :=
  ∀ (urls : GoSlice) (us : List net.url.URL) (P : net.url.URL → Prop),
  us ≠ [] → (∀ u ∈ us, P u) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ urls ↦*□ us }}
    (App (Val (@! rafthttp.newURLPicker)) (Val #urls))
  {{ (pk : Loc), RET #pk; pickerOk pk P }}

end spec

end EtcdGrove
end Perennial
