/-
`membership.NewClusterFromURLsMap(lg, token, urlsmap, opts...)` (`cluster.go:81-95`; claim #34,
stage 2, 2026-11-25: translated with its body). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Build

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
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`NewClusterFromURLsMap(lg, token, m, opts...)`** of a URLs map `m` (read-only, each entry's URLs
`urls name`, plain), a zap logger and one option setting `maxLearners` to `ml`, the `fips140`
GODEBUG setting off, **the entries' ids distinct and none `0`** (`NewMember`'s; facts of the
configuration, decided by evaluation): a fresh cluster, owned (`clusterOwned`), whose members are the
entries' `memberOfURLs` (`memOfList`, in any order: Go's map order is unspecified), and whose id is
`clusterIdOf` of their sorted ids; no error. (Go's two error returns are not reached: a repeated id
would be formatted with `%v` of a `*Member`, by reflection, which the model does not cover; an id `0`
is excluded by the premise, `bootGo.initMapOk`'s.) -/
abbrev membership.NewClusterFromURLsMap.spec : Prop :=
  ∀ (lg : Loc) (token : GoString) (mp : Loc) (m : GMap GoString GoSlice)
    (urls : GoString → List _root_.Perennial.net.url.URL) (opts : GoSlice) (f : GoFunc) (ml : w64),
  crypto.fips140.GodebugFips140Off → (∀ k, (m.lookup k).isSome → ∀ u ∈ urls k, http.urlRootPlain u) →
  (m.domList.map (fun k => (membership.memberOfURLs k (urls k) token).id)).Nodup →
  W64 0 ∉ m.domList.map (fun k => (membership.memberOfURLs k (urls k) token).id) →
  GMap.size m ≤ 2 ^ 58 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗
      zapLoggerOk lg ∗ mp ↦$□ m ∗ ([∗map] k ↦ sl ∈ m, sl ↦*□ urls k) ∗
      opts ↦*□ [f] ∗ membership.clusterOptMax f ml }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.membership.NewClusterFromURLsMap))
      (Val #lg)) (Val #token)) (Val #mp)) (Val #opts))
  {{ (c : Loc), RET (PairV #c #(GoInterface.nil)); ⌜c ≠ null⌝ ∗
      ∃ (ms : GMap w64 Loc) (ids : List w64),
        ⌜membership.idsSorted (membership.memOfList
          (m.domList.map (fun k => membership.memberOfURLs k (urls k) token))) ids⌝ ∗
        membership.clusterOwned c ml ms
          (membership.memOfList (m.domList.map (fun k => membership.memberOfURLs k (urls k) token)))
          (membership.clusterIdOf ids) }}

end spec

end EtcdGrove
end Perennial
