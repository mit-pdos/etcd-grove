/-
`types.URLsMap.String()` (`urlsmap.go:57-67`; claim #34, stage 2, 2026-11-25: translated with its
body, `VerifyBootstrap`'s). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.client.pkg.v3.types.URLs
public import GeneratedProof.go_etcd_io.etcd.client.pkg.v3.types
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

/-- **The bytes one URL `u` of the entry `k` adds to `URLsMap.String()`**: the piece `k=http://host` (a plain
URL's string) and its `,` (claim #34 stage 2, 2026-11-25). -/
def types.urlPieceLen [GooseExts] (k : GoString) (u : _root_.Perennial.net.url.URL) : Nat :=
  k.length + (go!"http://" ++ u.Host').length + 2

/-- **The bytes of `URLsMap.String()`'s pieces, with their separators** (an upper bound of its length). -/
def types.urlsMapStrLen [GooseExts] (m : GMap GoString GoSlice)
    (urls : GoString → List _root_.Perennial.net.url.URL) : Nat :=
  (m.domList.map (fun k => ((urls k).map (types.urlPieceLen k)).sum)).sum

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`m.String()` of a URLs map** (read-only, with its URL slices, at most `2^62` URLs in all:
`sort.Strings`' bound; each URL plain, `http.urlRootPlain`, so that its `String()` is `http://` and the host;
the pieces `name=url,` shorter than `2^61` bytes in all, `types.urlsMapStrLen`: `strings.Join`'s bound; claim
#34 stage 2, 2026-11-25, ledger): some string (the entries `name=url`, sorted, joined by `,`); it reads only. -/
abbrev types.URLsMap.String.spec : Prop :=
  ∀ (mp : Loc) (m : GMap GoString GoSlice) (urls : GoString → List _root_.Perennial.net.url.URL),
  (m.domList.map (fun k => (urls k).length)).sum ≤ 2 ^ 62 →
  (∀ k, (m.lookup k).isSome → ∀ u ∈ urls k, http.urlRootPlain u) →
  types.urlsMapStrLen m urls < 2 ^ 61 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types ∗ mp ↦$□ m ∗ [∗map] k ↦ sl ∈ m, sl ↦*□ urls k }}
    (App (Val (mp @!! go_etcd_io.etcd.client.pkg.v3.types.URLsMap.ty @!! go!"String")) (Val #()))
  {{ (s : GoString), RET #s; True }}

end spec

end EtcdGrove
end Perennial
