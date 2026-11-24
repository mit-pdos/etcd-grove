/-
`types.URLs.StringSlice()`, with the strings of plain URLs: a variant of `URLs__StringSlice.lean`
(whose post gives the length only), for `membership.computeMemberID`, which hashes them. Lean-first (no
Rocq counterpart); etcd_safe's deployment check (2026-11-24).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base
public import Proof.go_etcd_io.etcd.client.pkg.v3.types.URLs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `us.StringSlice()` through a pointer `p` to the `URLs` value `sl` (read at any fraction, kept), the
URLs read-only (`sl ↦*□ us`): a fresh slice of as many strings, the string of a URL of only the scheme
`http` and a plain host (`http.urlRootPlain`) being `http://` and the host. -/
abbrev types.URLs.StringSlicePlain.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (sl : GoSlice) (us : List _root_.Perennial.net.url.URL),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types ∗
      p ↦{dq} sl ∗ sl ↦*□ us }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.types.URLs.ty @!!
      go!"StringSlice")) (Val #()))
  {{ (out : GoSlice) (ss : List GoString), RET #out; p ↦{dq} sl ∗ out ↦* ss ∗
      ⌜ss.length = us.length ∧ ∀ (i : Nat) (u : _root_.Perennial.net.url.URL), us[i]? = some u →
        http.urlRootPlain u → ss[i]? = some (go!"http://" ++ u.Host')⌝ }}

end spec

end EtcdGrove
end Perennial
