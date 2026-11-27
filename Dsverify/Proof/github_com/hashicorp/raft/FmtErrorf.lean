/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/FmtErrorf.lean (241f27e).
-/
/-
The specs of raft's five `fmt.Errorf` calls with a fixed format (decisions D24, D25, D26; hub request
MAINL-3; attacks: notes/axioms/fmt-errorf.md, fmt-errorf-cfg.md, in the lab). Three are proved here from
Perennial's `fmt.wp_Errorf` (`tnErr`, the lab's one axiom; `nextCfgErr`; `snapCfgErr`); `cfgErr` and
`rsErr` are not provable over Perennial's model (it is stuck on `%v` of a struct or a pointer): the fork's
call sites are rewritten to format explicitly (#48), and the two specs go once nothing uses them.
-/
module

public import Perennial.Spec.fmt.Errorf
public import Dsverify.Proof.github_com.hashicorp.raft.iface.Net
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Spec.fmt.Errorf

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.hashicorp.raft

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]
variable [raft_sem : github_com.hashicorp.raft.Assumptions]

/-- (D24, restated by D25 after its attack) `fmt.Errorf` at `leadershipTransfer`'s TimeoutNow failure
path, `fmt.Errorf("failed to make TimeoutNow RPC to %v: %v", id, err)`: the format literal is fixed
(only `%v`: no verb that makes `fmt` reflect into the error's memory), the first argument is a
`raft.ServerID` (a named type whose underlying type is `string`, with no methods: `%v` formats its
bytes and calls nothing), the second an `error` value with `errOk` whose dynamic type implements
`error` (its `Error` has the signature `Error() string`, D26) and has no `Format` method (so `%v` calls its `Error()`, which `errOk` says is safe, needs no resources and
returns a string). Same post as Perennial's `fmt.Errorf.spec` (whose model ignores the arguments):
a non-nil error with a callable `Error()`. Attack: notes/axioms/fmt-errorf.md. -/
abbrev fmt.Errorf.spec_tnErr : Prop :=
  ∀ (args_sl : GoSlice) (id : ServerID) (e : GoInterfaceOk),
    methodSet e.ty !! go!"Format" = none →
    methodSet e.ty !! go!"Error" = some (go.signature.Signature [] false [go.string]) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗
       args_sl ↦* [interface.mkOk ServerID.ty #id, GoInterface.ok e] ∗ errOk (GoInterface.ok e) }}
      (App (App (Val (@! fmt.Errorf)) (Val #(go!"failed to make TimeoutNow RPC to %v: %v")))
        (Val #args_sl))
    {{ (e2 : GoInterfaceOk), RET #(interface.ok e2);
        □ ∀ Φ : val → IProp GF, ▷ (∀ str : GoString, Φ #str) -∗
          WP (App (Val #(methods e2.ty go!"Error" e2.v)) (Val #())) {{ Φ }} }}

/-- An `errOk` error's `Error()` has `fmt.stringMethodSpec` (the later `stringMethodSpec` gives
its caller is stripped by the call's first step: `wp_frame_step_l'`). -/
theorem github_com.hashicorp.raft.errOk_stringMethodSpec (x : GoInterfaceOk) :
    errOk (GF := GF) (GoInterface.ok x) ⊢ fmt.stringMethodSpec x go!"Error" := by
  unfold errOk fmt.stringMethodSpec
  iintro ⟨%y, %hy, #H⟩
  cases hy
  imodintro
  iintro %Φ HΦ
  iapply (wp_mono (e := App (Val #(methods x.ty go!"Error" x.v)) (Val #()))
    (Φ := fun v => iprop((∀ s : GoString, Φ #s) ∗ ⌜∃ s : GoString, v = #s⌝)) (Ψ := Φ)
    (fun v => by
      iintro ⟨HΦ, %hs⟩
      obtain ⟨s, rfl⟩ := hs
      iapply HΦ))
  iapply (wp_frame_step_l' (e := App (Val #(methods x.ty go!"Error" x.v)) (Val #()))
    (R := iprop(∀ s : GoString, Φ #s))
    (Φ := fun v => iprop(⌜∃ s : GoString, v = #s⌝ : IProp GF)) (by rfl) LawfulSet.subset_refl)
  isplitl [HΦ]
  · iexact HΦ
  · iapply H
    iintro %s
    ipureintro
    exact ⟨s, rfl⟩

/-- (D25) `fmt.Errorf.spec_tnErr`, proved from Perennial's model of `fmt.Errorf` (which formats as Go
does: `%v` of the `ServerID` is its bytes, `%v` of the error calls its `Error()`, which `errOk` makes
safe). Not an axiom (it was one in the lab, at a Perennial whose `fmt` formatted nothing). -/
theorem fmt.wp_Errorf_tnErr : fmt.Errorf.spec_tnErr (GF := GF) (hG := hG) := by
  intro args_sl id e hF hE
  iintro %Φ ⟨#Hpkg, Hsl, #He⟩ HΦ
  iapply (fmt.wp_Errorf _ args_sl _ (DFrac.own 1)) $$ [Hsl]
  · iframe
    isplitr
    · iexact Hpkg
    iapply fmt.argsOk_intro (by rfl)
    simp only [fmt.argsOkAt]
    isplitr
    · iapply fmt.argOkAt_of_argWf
      intro ii hii
      cases hii
      refine EtcdGrove.fmt.argWf_of_argsWf (fmt.ArgsWf.cons_named_string _ _ _ ?_ ?_ ?_ ?_ fmt.ArgsWf.nil)
      · unfold ServerID.ty; simp [go.string]
      · unfold ServerID.ty; simp [fmt.IsIntType, go.int, go.int64, go.int32, go.int16, go.int8,
          go.uint, go.uint64, go.uint32, go.uint16, go.uint8]
      · exact go.IsUnderlying.is_underlying
      · exact fmt.NoFmtMethods.of_methodSetIs_nil _
    isplitl
    · iapply EtcdGrove.fmt.argOkAt_of_error
      isplitr
      · ipureintro; exact ⟨by decide, rfl⟩
      isplitl
      · iapply errOk_stringMethodSpec; iexact He
      · ipureintro; exact ⟨hF, hE⟩
    · itrivial
  inext
  iintro %err ⟨-, %s, -, Herr⟩
  iunfold fmt.errorfErr at Herr
  icases Herr with ⟨-, #HE, -⟩
  iapply HΦ
  imodintro
  iintro %Ψ HΨ
  iapply HE
  inext
  iapply HΨ

/-- (D35) `fmt.Errorf` at `checkConfiguration`'s no-voter error,
`fmt.Errorf("need at least one voter in configuration: %v", configuration)`: the format literal is fixed
(one `%v`), the argument is a `raft.Configuration` value (a struct with one field, `Servers []Server`;
`Configuration` and `Server` have no methods; `Server`'s fields are `Suffrage ServerSuffrage`, whose
`String()` is a pure switch on the value, and `ID`/`Address`, named strings without methods): `%v` reflects
over the struct, reads the `Servers` slice's elements (the caller lends read access, given back) and calls
`String()` on each suffrage. Post as Perennial's `fmt.Errorf.spec`: a non-nil error with a callable `Error()`.
Attack: notes/axioms/fmt-errorf-cfg.md.
**Not proved here** (port, 2026-11-27): the lab proved it from a Perennial `fmt` model that formatted
nothing (`errors.New(format)`); Perennial's model now formats, and is stuck (`notModelled`) on `%v` of a
struct, which Go prints by reflection (`pp.printValue`, not translated). Decided (#48, coordinator-E):
the fork's `checkConfiguration` formats the servers' fields explicitly, and its proof goes over
`fmt.wp_Errorf`; this spec goes once nothing uses it. -/
abbrev fmt.Errorf.spec_cfgErr : Prop :=
  ∀ (args_sl : GoSlice) (c : Configuration) (dq : DFrac) (ss : List Server),
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗
       args_sl ↦* [interface.mkOk Configuration.ty #c] ∗ c.Servers' ↦*{dq} ss }}
      (App (App (Val (@! fmt.Errorf)) (Val #(go!"need at least one voter in configuration: %v")))
        (Val #args_sl))
    {{ (x : Loc), RET #(interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x);
        c.Servers' ↦*{dq} ss ∗
        □ ∀ Φ : val → IProp GF, ▷ (∀ str : GoString, Φ #str) -∗
          WP (App (Val #(methods (go.GoType.PointerType errors.errorString.ty) go!"Error" #x)) (Val #()))
            {{ Φ }} }}

/-- (stage 4, API-S4-1) `fmt.Errorf` at `nextConfiguration`'s stale-change error,
`fmt.Errorf("configuration changed since %v (latest is %v)", change.prevIndex, currentIndex)`: the
format literal is fixed (two `%v`), both arguments are `uint64`s (`%v` formats the numbers and calls
nothing). Post: an `errors.New` leaf (a `*errorString`) with a callable `Error()` (`cfgChangeQ`'s third
arm, which hr3's `reconfigure` compares with `ErrNotLeader`). -/
abbrev fmt.Errorf.spec_nextCfgErr : Prop :=
  ∀ (args_sl : GoSlice) (a b : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗
       args_sl ↦* [interface.mkOk go.uint64 #a, interface.mkOk go.uint64 #b] }}
      (App (App (Val (@! fmt.Errorf)) (Val #(go!"configuration changed since %v (latest is %v)")))
        (Val #args_sl))
    {{ (x : Loc), RET #(interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x);
        □ ∀ Φ : val → IProp GF, ▷ (∀ str : GoString, Φ #str) -∗
          WP (App (Val #(methods (go.GoType.PointerType errors.errorString.ty) go!"Error" #x)) (Val #()))
            {{ Φ }} }}

/-- (stage 4, API-S4-1) `fmt.Errorf.spec_nextCfgErr`, from Perennial's `fmt.wp_Errorf` (two `uint64`s
are `ArgWf`; the format has no `%w`, so the error is an `*errorString`). Not an axiom. -/
theorem fmt.wp_Errorf_nextCfgErr : fmt.Errorf.spec_nextCfgErr (GF := GF) (hG := hG) := by
  intro args_sl a b
  iintro %Φ ⟨#Hpkg, Hsl⟩ HΦ
  iapply (fmt.wp_Errorf _ args_sl _ (DFrac.own 1)) $$ [Hsl]
  · iframe
    isplitr
    · iexact Hpkg
    iapply fmt.argsOk_of_argsWf
    exact fmt.ArgsWf.cons_int _ _ _ (.uint64 _) (fmt.ArgsWf.cons_int _ _ _ (.uint64 _) fmt.ArgsWf.nil)
  inext
  iintro %err ⟨-, %s, -, Herr⟩
  iunfold fmt.errorfErr at Herr
  icases Herr with ⟨-, #HE, Hm⟩
  obtain ⟨ds, hds, hw⟩ : ∃ ds, fmt.fmtDirectives go!"configuration changed since %v (latest is %v)" = some ds ∧ fmt.wrapArgs ds 2 = [] :=
    ⟨_, rfl, rfl⟩
  simp only [hds, List.length_cons, List.length_nil, Nat.reduceAdd, hw]
  icases Hm with ⟨%l, %hl, -⟩
  subst hl
  iapply HΦ
  imodintro
  iintro %Ψ HΨ
  iapply HE
  inext
  iapply HΨ

/-- (review T1-5) `fmt.Errorf` at `takeSnapshot`'s configuration-index error,
`fmt.Errorf("cannot take snapshot now, wait until the configuration entry at %v has been applied (have
applied %v)", committedIndex, snapReq.index)`: the format literal is fixed (two `%v`), both arguments
are `uint64`s (`%v` formats the numbers and calls nothing). Post: an `errors.New` leaf (a
`*errorString`), what `runSnapshots`' `errors.Is` needs (`errors.wp_Is_leaf`). -/
abbrev fmt.Errorf.spec_snapCfgErr : Prop :=
  ∀ (args_sl : GoSlice) (a b : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗
       args_sl ↦* [interface.mkOk go.uint64 #a, interface.mkOk go.uint64 #b] }}
      (App (App (Val (@! fmt.Errorf))
        (Val #(go!"cannot take snapshot now, wait until the configuration entry at %v has been applied (have applied %v)")))
        (Val #args_sl))
    {{ (x : Loc), RET #(interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x); True }}

/-- (review T1-5) `fmt.Errorf.spec_snapCfgErr`, from Perennial's `fmt.wp_Errorf`, as
`fmt.wp_Errorf_nextCfgErr`. Not an axiom. -/
theorem fmt.wp_Errorf_snapCfgErr : fmt.Errorf.spec_snapCfgErr (GF := GF) (hG := hG) := by
  intro args_sl a b
  iintro %Φ ⟨#Hpkg, Hsl⟩ HΦ
  iapply (fmt.wp_Errorf _ args_sl _ (DFrac.own 1)) $$ [Hsl]
  · iframe
    isplitr
    · iexact Hpkg
    iapply fmt.argsOk_of_argsWf
    exact fmt.ArgsWf.cons_int _ _ _ (.uint64 _) (fmt.ArgsWf.cons_int _ _ _ (.uint64 _) fmt.ArgsWf.nil)
  inext
  iintro %err ⟨-, %s, -, Herr⟩
  iunfold fmt.errorfErr at Herr
  icases Herr with ⟨-, #HE, Hm⟩
  obtain ⟨ds, hds, hw⟩ : ∃ ds, fmt.fmtDirectives go!"cannot take snapshot now, wait until the configuration entry at %v has been applied (have applied %v)" = some ds ∧ fmt.wrapArgs ds 2 = [] :=
    ⟨_, rfl, rfl⟩
  simp only [hds, List.length_cons, List.length_nil, Nat.reduceAdd, hw]
  icases Hm with ⟨%l, %hl, -⟩
  subst hl
  iapply HΦ
  itrivial

/-- (stage 4, package leader) `fmt.Errorf` at `leaderLoop`'s leadership transfer to a server without a
replication goroutine (not in the latest configuration), `fmt.Errorf("cannot find replication state for
%v", id)`: the format literal is fixed (one `%v`), the argument is a `*raft.ServerID` (a pointer: `%v`
formats its address, reads no memory and calls no method). Post: a non-nil error (sent on the transfer's
`doneCh`, whose receiver only compares it with `nil`).
**Not proved here** (port, 2026-11-27): as `fmt.Errorf.spec_cfgErr`, Perennial's `fmt` model is stuck on
`%v` of a pointer (Go's `printValue` prints its address). Decided (#48): the fork's `leaderLoop` formats
the dereferenced `ServerID` with `%s`; this spec goes once nothing uses it. -/
abbrev fmt.Errorf.spec_rsErr : Prop :=
  ∀ (args_sl : GoSlice) (p : Loc),
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗
       args_sl ↦* [interface.mkOk (go.GoType.PointerType ServerID.ty) #p] }}
      (App (App (Val (@! fmt.Errorf)) (Val #(go!"cannot find replication state for %v")))
        (Val #args_sl))
    {{ (e2 : GoInterfaceOk), RET #(interface.ok e2); True }}

end spec

end Perennial
