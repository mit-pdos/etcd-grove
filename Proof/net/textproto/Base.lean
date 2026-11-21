/-
**`net/textproto`'s package fact** (prove-http3, 2026-11-21): the interned common header keys.

`canonicalMIMEHeaderKey` (go1.27.3 `net/textproto/reader.go:757`) runs
`commonHeaderOnce.Do(initCommonHeader)` and then reads the map `commonHeader`, which
`initCommonHeader` (`reader.go:811`) makes and fills with forty keys, each mapped to itself. The
fact is the `sync.Once` of that pattern (Perennial's `isOnce`): its action owns the variable
`commonHeader` (`commonHeaderVar`) and leaves it read-only for good, holding a read-only map whose
every value is its key (`commonHeaderOk`), which is all `CanonicalMIMEHeaderKey` needs of it (the
string it returns is the canonical key either way).

Perennial's `isOnce` is stated for heaps with later credits (`HasLC.hasLC`), as every spec of
this boundary (`Proof/net/http/Boundary.lean`); a package fact is stated for any `hlc`, so the
fact is `isOnce`'s with credits and `True` without (`textprotoInit`): no proof here runs without
credits.
-/
module

public import GeneratedProof.net.textproto
public import Perennial.Proof.sync.OnceDefs
public import Perennial.Proof.errors.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace net.textproto

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- What `initCommonHeader` needs: the variable `commonHeader`, at any map. -/
def commonHeaderVar : IProp GF :=
  iprop(∃ m : Loc, globalAddr commonHeader ↦ m)

/-- What `initCommonHeader` leaves, for good: `commonHeader` read-only, at a read-only map whose
every value is its key. -/
def commonHeaderOk : IProp GF :=
  iprop(∃ (m : Loc) (M : GMap GoString GoString), globalAddr commonHeader ↦□ m ∗ m ↦$□ M ∗
    ⌜∀ k v, M !! k = some v → v = k⌝)

instance commonHeaderOk_persistent : Persistent (commonHeaderOk (GF := GF)) := by
  unfold commonHeaderOk; infer_instance

/-- The fact, with later credits: `commonHeaderOnce` is the `Once` of `initCommonHeader`. -/
def textprotoInitLC : IProp GF :=
  sync.isOnce (globalAddr commonHeaderOnce) commonHeaderVar commonHeaderOk

instance textprotoInitLC_persistent : Persistent (textprotoInitLC (GF := GF)) := by
  unfold textprotoInitLC; infer_instance

end defs

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} {hlc : HasLC} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`net/textproto`'s fact**: `textprotoInitLC` on a heap with later credits, `True` without. -/
def textprotoInit : IProp GF :=
  match hlc, hG, sem with
  | .hasLC, hG, sem => textprotoInitLC (hG := hG) (sem := sem)
  | .hasNoLC, _, _ => iprop(True)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.net.textproto :=
  define_is_pkg_init textprotoInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.net.textproto :=
  build_get_is_pkg_init_wf

end init

section lc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- With later credits, the fact is `textprotoInitLC`. -/
theorem isPkgInitDef_textproto :
    isPkgInitDef (PROP := IProp GF) pkg_id.net.textproto = textprotoInitLC := rfl

end lc

end net.textproto

end Perennial
