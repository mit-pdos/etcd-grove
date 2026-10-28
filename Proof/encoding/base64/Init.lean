/-
Package initialization of `encoding.base64`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`base64Init`, `encoding/base64/Base.lean`; the auth plan's E2x, 2026-10-26):
`StdEncoding` holds a fixed `*Encoding` whose `EncodeToString` returns the standard encoding
(`stdEnc`) of its argument's bytes, stated as the method call's own WP (the type is axiomatized).
Its initializer runs its variables' untranslated initializers (`base64.go`); the trust-boundary
axiom `StdEncoding_init` states the one the fact reads (`NewEncoding(encodeStd)`, a fresh
`*Encoding` with the standard alphabet and padding, whose `EncodeToString` allocates its output
buffer, `Encode`s into it and returns it as a string: no panic, no write to its argument),
`opaqueInitsOk` the others.
-/
module

public import Proof.encoding.base64.Base
public import Proof.runtime.PkgInitExt

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

/-- `x ∈ [a, ..., x, ...]`, linear in the list (`simp` overflows on the long ones). -/
local macro "mem_tac" : tactic =>
  `(tactic| repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section opaqueInits
namespace encoding.base64
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `encoding.base64`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([URLEncoding.init,
        RawStdEncoding.init,
        RawURLEncoding.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

/-- `StdEncoding = NewEncoding(encodeStd)` (`base64.go`): a fixed `*Encoding` (Go never writes the variable after) whose `EncodeToString` returns the standard base64 encoding `stdEnc` of its argument's bytes, reading and keeping the slice. -/
axiom StdEncoding_init :
    {{ (True : IProp GF) }} (App (Val StdEncoding.init) (Val #()))
    {{ RET #(); _root_.Perennial.encoding.base64.base64Init (GF := GF) }}

end encoding.base64
end opaqueInits

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.encoding.base64.Assumptions]

namespace encoding.base64

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.encoding.base64 get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.encoding.base64 }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply StdEncoding_init as #HStdEncoding
  wp_apply (opaqueInitsOk URLEncoding.init (by mem_tac))
  wp_apply (opaqueInitsOk RawStdEncoding.init (by mem_tac))
  wp_apply (opaqueInitsOk RawURLEncoding.init (by mem_tac))
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.encoding.base64 get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.encoding.base64 }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end encoding.base64

end init

end Perennial
