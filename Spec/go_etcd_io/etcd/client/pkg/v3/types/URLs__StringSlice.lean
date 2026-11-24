/-
`types.URLs.StringSlice()`. Lean-first (no Rocq counterpart); the server-construction unit, stage N0
(2026-10-16, D13: `notes/decisions.md`), for `NewServer`; translated and proved since 2026-11-21.
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

/-- `us.StringSlice()` through a pointer `p` to the `URLs` value `sl` (read at any fraction, kept),
the URLs read-only (`sl ↦*□ us`): a fresh slice of as many strings (`out[i] = us[i].String()`).
(prove-ps2-misc, 2026-11-21: proved over `url.URL.String`'s spec; until then a trust-boundary axiom
over `p ≠ null` alone, owning nothing of `*p`, with post `True`: the premise is the one caller's,
`NewServer` on its configuration's `ClientURLs` field, `bootCfgRO`'s `cfg.ClientURLs' ↦*□ U.client`;
the ledger's entry of that date.) (fmt stage 1, 2026-11-24) Each URL of only the scheme `http` and a
plain host (`http.urlRootPlain`) gives `http://host` (`url.URL.String`'s spec): `NewServer` bounds the
strings' lengths from its URLs' (`etcdURLsFit`, for `publishV3`'s `strings.Join` of them). -/
abbrev types.URLs.StringSlice.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (sl : GoSlice) (us : List _root_.Perennial.net.url.URL),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types ∗
      p ↦{dq} sl ∗ sl ↦*□ us }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.types.URLs.ty @!!
      go!"StringSlice")) (Val #()))
  {{ (out : GoSlice), RET #out; p ↦{dq} sl ∗
      ∃ ss : List GoString, out ↦* ss ∗ ⌜ss.length = us.length ∧
        ∀ (j : Nat) (u : _root_.Perennial.net.url.URL), us[j]? = some u → http.urlRootPlain u →
          ss[j]? = some (go!"http://" ++ u.Host')⌝ }}

end spec

end EtcdGrove
end Perennial
