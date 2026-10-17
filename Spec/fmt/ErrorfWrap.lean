/-
`fmt.Errorf` with a `%w` verb: the trust boundary, the wrapping half (pr-verify etcd#21714:
`clientv3.newClient` wraps its dial and token errors with `fmt.Errorf("... [%s] ...: %w",
strings.Join(endpoints, ";"), err)`). `Spec/fmt/Errorf.lean`'s spec says only that the result's
`Error()` returns some string; this one also says what the result unwraps to, which is what
`errors.Is`/`errors.As` on it see (`fmt.wrapsErr`, `errorIsTree_wrap`). Lean-first (no Rocq
counterpart); on the verification branch `pr-verify/etcd-21714` only.
-/
module

public import Spec.fmt.Errorf

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.fmt.Assumptions]

/-- **The error `e` wraps `inner`** (persistent): `e` has an `Unwrap() error` method returning
`inner`, and no `Is(error) bool`, `As(any) bool` or `Unwrap() []error` method: Go's
`*fmt.wrapError` (method set `{Error, Unwrap}`), what `fmt.Errorf` returns for a format with one
`%w` verb. (The method-set facts are Go's typing, which the model lacks.) -/
def fmt.wrapsErr (e inner : GoInterfaceOk) : IProp GF :=
  iprop(⌜methodSet e.ty !! go!"Unwrap" = some (go.Signature [] false [go.error])⌝ ∗
    ⌜methodSet e.ty !! go!"Is" ≠ some (go.Signature [go.error] false [go.bool])⌝ ∗
    ⌜methodSet e.ty !! go!"As" ≠ some (go.Signature [go.any] false [go.bool])⌝ ∗
    {{ True }}
      (App (Val #(methods e.ty go!"Unwrap" e.v)) (Val #()))
    {{ RET #(GoInterface.ok inner); True }})

instance fmt.wrapsErr_persistent (e inner : GoInterfaceOk) :
    Persistent (fmt.wrapsErr (GF := GF) e inner) := by
  unfold fmt.wrapsErr; infer_instance

/-- A format whose only verbs are one `%s` and then one `%w` (the bytes `%` are those two verbs'
only): `newClient`'s two. -/
def fmt.fmtSW (format : GoString) : Prop :=
  ∃ a b c : GoString, format = a ++ go!"%s" ++ b ++ go!"%w" ++ c ∧
    W8 37 ∉ a ∧ W8 37 ∉ b ∧ W8 37 ∉ c

/-- **`fmt.Errorf(format, s, err)`** for a format of one `%s` and one `%w` (`fmtSW`), a string
`s` and a non-nil error `err` whose `Error()` returns some string: a non-nil error whose
`Error()` returns some string (the formatted message) and which wraps `err` (`fmt.wrapsErr`); the
arguments' slice comes back. -/
abbrev fmt.ErrorfWrap.spec : Prop :=
  ∀ (format s : GoString) (err : GoInterfaceOk) (args_sl : GoSlice) (dq : DFrac),
  fmt.fmtSW format →
  {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗
      args_sl ↦*{dq} [interface.mkOk go.string #s, GoInterface.ok err] ∗
      fmt.stringMethodSpec err go!"Error" }}
    (App (App (Val (@! _root_.Perennial.fmt.Errorf)) (Val #format)) (Val #args_sl))
  {{ (e : GoInterfaceOk), RET #(interface.ok e);
      args_sl ↦*{dq} [interface.mkOk go.string #s, GoInterface.ok err] ∗
      fmt.stringMethodSpec e go!"Error" ∗ fmt.wrapsErr e err }}

end spec

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`errors.Is` sees through the wrapping**: if `e` wraps `inner` and `inner`'s error tree is
`S` (`errorIsTree S M target`, what Perennial's `errors.Is` spec takes), then `e`'s tree is `S`
with `e` added. So `errors.Is(e, target)` walks to `inner` and on (Go's `errors.Is` follows
`Unwrap`): a caller testing the wrapped error with `errors.Is` gets what it got testing `inner`,
when `inner` is `target` (the first conjunct of Perennial's `errors.Is` postcondition, through
the walk) or an error of `inner`'s tree is. -/
theorem errorIsTree_wrap (S : GoError → Prop) (M : GoInterfaceOk → Prop) (target : GoError)
    (e inner : GoInterfaceOk) (hS : S (interface.ok inner)) :
    fmt.wrapsErr (GF := GF) e inner ∗ errors.errorIsTree (GF := GF) S M target ⊢
      errors.errorIsTree (GF := GF) (fun x => x = interface.ok e ∨ S x) M target := by
  iintro ⟨#Hw, #HT⟩
  unfold fmt.wrapsErr
  icases Hw with ⟨%hU, %hIs, %hAs, #HU⟩
  iintro !> %ii %hii
  rcases hii with hii | hii
  · cases hii
    unfold errors.errorIsNode
    simp only [hIs, hU, ↓reduceIte]
    isplitr
    · itrivial
    iintro !> %Φ _ HΦ
    iapply HU
    · itrivial
    iintro !> _
    iapply HΦ
    ipureintro; exact Or.inr hS
  · ihave #Hn := HT $$ %ii %hii
    unfold errors.errorIsNode
    icases Hn with ⟨#HIs, #HUw⟩
    isplitr
    · iexact HIs
    by_cases h1 : methodSet ii.ty !! go!"Unwrap" = some (go.Signature [] false [go.error])
    · simp only [h1, ↓reduceIte, named]
      iintro !> %Φ _ HΦ
      iapply HUw
      · itrivial
      iintro !> %e' %he'
      iapply HΦ
      ipureintro; exact Or.inr he'
    · by_cases h2 : methodSet ii.ty !! go!"Unwrap" =
          some (go.Signature [] false [go.GoType.SliceType go.error])
      · simp only [if_neg h1, if_pos h2, named]
        iintro !> %Φ _ HΦ
        iapply HUw
        · itrivial
        iintro !> %s %dq %es ⟨Hs, %hes⟩
        iapply HΦ
        iframe Hs
        ipureintro; intro x hx; exact Or.inr (hes x hx)
      · simp only [if_neg h1, if_neg h2, named]
        itrivial

end lemmas

end EtcdGrove
end Perennial
