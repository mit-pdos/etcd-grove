/-
Package initialization of `go_uber_org.zap`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact: `_minTimeInt64` and `_maxTimeInt64` hold fixed times (prove-srvloops2, 2026-11-21: `zap.Time`
compares with them; until then `True`). Its initializer initializes its imports, allocates its variables and runs
their translated initializers (prove-initleft, 2026-11-21; until then the trust-boundary axiom
`opaqueInitsOk` covered them all): `errNoEncoderNameSpecified` (`errors.New`), the encoder constructors (a
map literal of two func literals), `_errArrayElemPool` (`pool.New`, proved), `_globalL = NewNop()`
(`zapcore.NewNopCore()`, `zapcore.AddSync(io.Discard)` over any writer, `zapcore.DefaultClock` from
zapcore's fact), `_globalS = _globalL.Sugar()` (a copy of the logger) and the interface assertion
`var _ internal.LeveledEnabler = AtomicLevel{}`, and (prove-srvloops2) `_minTimeInt64`/`_maxTimeInt64`
(`time.Unix`); and (prove-zap3, 2026-11-21) `_sinkRegistry = newSinkRegistry()`: a registry whose fresh mutex is locked
around the registration of the file sink, `normalizeScheme("file")` being `"file"` by `strings.ToLower`'s
spec.
-/
module

public import Proof.go_uber_org.zap.PkgInit
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.math.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Proof.time.Link
public import Proof.go_uber_org.zap.internal.Init
public import Proof.go_uber_org.zap.internal.bufferpool.Init
public import Proof.go_uber_org.zap.internal.pool.Init
public import Proof.go_uber_org.zap.internal.stacktrace.Init
public import Proof.go_uber_org.zap.zapcore.Init
public import Proof.net.url.Init
public import Proof.os.Init
public import Perennial.Proof.errors.NewVar
public import Spec.strings.ToLower
public import Spec.go_uber_org.zap.Defs

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

section zapinit
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_uber_org.zap.Assumptions]

/-- (prove-initleft) `zapcore.AddSync(w)` returns, whatever the writer (a type switch: `w` itself if
it is a `WriteSyncer`, else `writerWrapper{w}`). -/
theorem EtcdGrove.zap_wp_AddSync_init (w : GoInterface) :
    {{ (True : IProp GF) }} (App (Val (@! _root_.Perennial.go_uber_org.zap.zapcore.AddSync)) (Val #w))
    {{ (r : GoInterface), RET #r; True }} := by
  wp_start
  wp_auto
  rcases w with wo | _
  · wp_auto
    cases hws : go.typeSetContains wo.ty _root_.Perennial.go_uber_org.zap.zapcore.WriteSyncer.ty
    all_goals (wp_auto; iapply HΦ; itrivial)
  · wp_auto
    iapply HΦ
    itrivial

/-- (prove-initleft) `zap.NewNop()` before zap's `isPkgInit`: a new `Logger` (its body: `NewNopCore()`,
`AddSync(io.Discard)`, `zapcore.DefaultClock`, from io's and zapcore's facts), a `nopLoggerVal`
(prove-zap3: `zap.NewNop`'s spec is proved from it). -/
theorem EtcdGrove.zap_wp_NewNop_init :
    {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap.zapcore }}
      (App (Val (@! _root_.Perennial.go_uber_org.zap.NewNop)) (Val #()))
    {{ (l : Loc), RET #l; ∃ v : _root_.Perennial.go_uber_org.zap.Logger, l ↦ v ∗
        ⌜EtcdGrove.zap.nopLoggerVal v⌝ }} := by
  wp_start
  ihave #IO : (_root_.Perennial.io.isInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  iNamed IO
  icases HDiscard with ⟨%wd, #HDiscard⟩
  ihave #ZC := _root_.Perennial.go_uber_org.zap.zapcore.isInit_access $$ Hpkg2
  icases ZC with ⟨⟨%dc, #HDC⟩, -⟩
  wp_auto
  wp_func_call
  wp_call
  wp_auto
  wp_apply EtcdGrove.zap_wp_AddSync_init as %ws -
  try wp_auto
  iapply HΦ
  iexists _
  iframe
  ipureintro
  exact ⟨rfl, rfl, rfl, rfl, rfl, dc, rfl⟩

/-- (prove-initleft) `l.Sugar()` on a `Logger`: a copy of it (`clone`), its caller skip plus 2. -/
theorem EtcdGrove.zap_wp_Sugar_init (l : Loc) (v : _root_.Perennial.go_uber_org.zap.Logger) :
    {{ (l ↦ v : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType _root_.Perennial.go_uber_org.zap.Logger.ty @!! go!"Sugar")) (Val #()))
    {{ (s : Loc), RET #s; l ↦ v }} := by
  wp_start as Hl
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  iapply HΦ
  iframe

/-- (prove-zap3) `normalizeScheme("file")` is `("file", nil)`: `strings.ToLower` of an ASCII word with
no upper-case letter is the word itself (its spec, `strings.lowersTo`), whose first byte is a letter and
whose other bytes are letters. -/
theorem EtcdGrove.zap_wp_normalizeScheme_file (hTL : EtcdGrove.strings.ToLower.spec (GF := GF) (hG := hG)) :
    {{ (True : IProp GF) }}
      (App (Val (@! _root_.Perennial.go_uber_org.zap.normalizeScheme)) (Val #(go!"file")))
    {{ RET (PairV #(go!"file") #interface.nil); True }} := by
  wp_start
  wp_auto
  wp_apply hTL as %r %Hr
  have hr : r = go!"file" := (Hr go!"file" (by decide)).mpr (by decide)
  subst hr
  wp_auto
  ihave HI : (∃ i : w64, "i" ∷ i_ptr ↦ i ∗ "%Hi" ∷ ⌜1 ≤ sint.Z i ∧ sint.Z i ≤ 4⌝ : IProp GF) $$ [i]
  · iexists W64 1; iframe; ipureintro; decide
  wp_for HI
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
  try wp_auto
  wp_if_destruct
  · have hi : i = W64 1 ∨ i = W64 2 ∨ i = W64 3 := by
      have : sint.Z i < 4 := by have h := go.intoVal_inj Hif; simp at h; word
      rcases (show sint.Z i = 1 ∨ sint.Z i = 2 ∨ sint.Z i = 3 by omega) with h | h | h
      · left; word
      · right; left; word
      · right; right; word
    rcases hi with rfl | rfl | rfl
    all_goals (wp_auto; wp_for_post; iframe; iexists _; iframe; ipureintro; word)
  · rw [ite_eq_right_of_eq_false _ _ (by
      cases h : decide (sint.Z i < sint.Z (W64 ↑[W8 102, W8 105, W8 108, W8 101].length)) <;> simp_all)]
    wp_auto
    iapply HΦ
    itrivial

/-- (prove-zap3) `newSinkRegistry()` returns (a new registry: an empty factory map, `os.OpenFile`, and the
file sink registered by `RegisterSink`, under the registry's fresh mutex, `normalizeScheme("file")`
succeeding and the map holding no factory yet). -/
theorem EtcdGrove.zap_wp_newSinkRegistry_init (hTL : EtcdGrove.strings.ToLower.spec (GF := GF) (hG := hG)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync }}
      (App (Val (@! _root_.Perennial.go_uber_org.zap.newSinkRegistry)) (Val #()))
    {{ (sr : Loc), RET #sr; True }} := by
  wp_start as #Hsync
  wp_auto
  wp_apply wp_map_make1 (K := GoString) (V := GoFunc) as %m Hm
  try wp_auto
  iStructNamed «$r0»
  imod sync.init_Mutex iprop(True) ⊤ («$r0_ptr».[_root_.Perennial.go_uber_org.zap.sinkRegistry, go!"mu"])
    $$ mu [] with #Hmu
  · inext; itrivial
  try wp_auto
  wp_method_call
  wp_call
  rw [show _root_.Perennial.go_uber_org.zap.schemeFile = #(go!"file") from rfl]
  try wp_auto
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, -⟩
  try wp_auto
  wp_apply (EtcdGrove.zap_wp_normalizeScheme_file hTL)
  try wp_auto
  wp_apply wp_map_lookup2 $$ [$Hm] as Hm
  try wp_auto
  wp_apply (wp_mapInsert (K := GoString) (V := GoFunc) _) $$ Hm as Hm
  try wp_auto
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked]
  · itrivial
  try wp_auto
  iapply HΦ
  itrivial

end zapinit
end Perennial
