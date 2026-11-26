/-
Package initialization of `github_com.rs.zerolog.internal.json`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`jsonInit`, `Base.lean`): the invariant of its hook cell `JSONMarshalFunc`
(`hookCell`, `Proof/runtime/InitInv.lean`), which zerolog's initializer, holding its package state, opens
for a plain store, and `noEscapeTable`, read-only for good. Its initializer allocates both (no
initializer for `JSONMarshalFunc`, so `nil`; a zero array for the table), initializes its imports and
runs its translated `init`, whose loop fills the table (`wp_init0`, `InitLoop.lean`). (dsv-retire-3,
2026-11-26: until then names only, zerolog's `wp_initialize'` a trust-boundary axiom.)
-/
module

public import Dsverify.Proof.github_com.rs.zerolog.internal.json.Base
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.math.Link
public import Perennial.Proof.strconv.Link
public import Perennial.Proof.time.Link
public import Perennial.Proof.unicode.utf8.Link
public import Proof.net.Init
public import Dsverify.Proof.github_com.rs.zerolog.internal.json.InitLoop
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

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.github_com.rs.zerolog.internal.json.Assumptions]

namespace github_com.rs.zerolog.internal.json

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.rs.zerolog.internal.json get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog.internal.json }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := GoArray Bool 256) noEscapeTable _ as HnoEscapeTable
  wp_apply wp_GlobalAlloc (V := GoFunc) JSONMarshalFunc _ as HJSONMarshalFunc
  wp_apply (_root_.Perennial.net.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.math _root_.Perennial.math.initialize'
      EtcdGrove.ExternalInit.math _root_.Perennial.math.wp_initialize' _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.fmt _root_.Perennial.fmt.initialize'
      EtcdGrove.ExternalInit.fmt _root_.Perennial.fmt.wp_initialize' _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.time _root_.Perennial.time.initialize'
      EtcdGrove.ExternalInit.time _root_.Perennial.time.wp_initialize' _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.strconv _root_.Perennial.strconv.initialize'
      EtcdGrove.ExternalInit.strconv _root_.Perennial.strconv.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.unicode.utf8 _root_.Perennial.unicode.utf8.initialize'
      EtcdGrove.ExternalInit.unicode_utf8 _root_.Perennial.unicode.utf8.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of noEscapeTable))
  -- the translated init.«0», by its spec
  wp_apply (wp_init0 _) $$ HnoEscapeTable as ⟨%tb, HnoEscapeTable⟩
  try wp_auto
  imod (EtcdGrove.grpcInternal.hookCell_alloc (hG := hG) (V := GoFunc) ⊤ _ _) $$ HJSONMarshalFunc with #CJSONMarshalFunc
  ipersist HnoEscapeTable
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  try imodintro
  unfold _root_.Perennial.github_com.rs.zerolog.internal.json.jsonInit
  iframe CJSONMarshalFunc
  iexists _
  iexact HnoEscapeTable

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.rs.zerolog.internal.json get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog.internal.json }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end github_com.rs.zerolog.internal.json

end init

end Perennial
