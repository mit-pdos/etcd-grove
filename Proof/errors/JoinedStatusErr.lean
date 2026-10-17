/-
**Errors built by `errors.Join` from errors grpc's `status` accepts** (etcd#19935's
`watcher.Close`, which joins the errors of its streams' `close`): the predicate
`joinedStatusErrOk` that `errors.Join` (`Spec/errors/Join.lean`) and `errors.Is`
(`Spec/errors/IsJoinedStatusErr.lean`) are stated over, and the lemmas that a `nil` error and
an error `status` accepts (`statusErrOk`) are such errors. Shared definitions (outside the
spec/proof discipline). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Proof.errors

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `ii` is a `*errors.joinError`: the error `errors.Join` returns when one of its arguments is
not `nil` (a pointer to a struct holding the non-`nil` arguments; methods `Error()` and
`Unwrap() []error`, no `Is` or `As`). -/
def isJoinErrorPtr (ii : GoInterfaceOk) : Prop :=
  ∃ l : Loc, ii.ty = go.GoType.PointerType _root_.Perennial.errors.joinError.ty ∧ ii.v = #l

/-- **An error tree of `status` errors and `errors.Join`s** (persistent): `err` is in a set `S`
of errors closed under the `Unwrap` methods with their specs, for any target of `errors.Is`
(Perennial's `errorIsTree`, with `Is` methods that mean nothing in particular: `M := True`), and
every non-`nil` error of `S` is an error grpc's `status` accepts (`statusErrOk`: a leaf) or a
`*errors.joinError`. -/
def joinedStatusErrOk (err : GoInterface) : IProp GF :=
  iprop(∃ S : GoInterface → Prop, ⌜S err⌝ ∗
    □ (∀ target : GoInterface,
        _root_.Perennial.errors.errorIsTree (GF := GF) S (fun _ => True) target) ∗
    □ (∀ ii : GoInterfaceOk, ⌜S (GoInterface.ok ii)⌝ -∗
        statusErrOk (GF := GF) (GoInterface.ok ii) ∨ ⌜isJoinErrorPtr ii⌝))

instance joinedStatusErrOk_persistent (err : GoInterface) :
    Persistent (joinedStatusErrOk (GF := GF) err) := by
  unfold joinedStatusErrOk; infer_instance

/-- `nil` is a (one-error) tree. -/
theorem joinedStatusErrOk_nil : ⊢ joinedStatusErrOk (GF := GF) GoInterface.nil := by
  unfold joinedStatusErrOk
  iexists (· = GoInterface.nil)
  isplitr
  · ipureintro; rfl
  isplitr
  · imodintro; iintro %target; imodintro; iintro %ii %h; cases h
  · imodintro; iintro %ii %h; cases h

/-- An error `status` accepts is a one-error tree. -/
theorem joinedStatusErrOk_of_statusErrOk (err : GoInterface) :
    statusErrOk (GF := GF) err ⊢ joinedStatusErrOk (GF := GF) err := by
  iintro #Hs
  unfold joinedStatusErrOk
  iexists (· = err)
  isplitr
  · ipureintro; rfl
  isplitr
  · imodintro; iintro %target; imodintro; iintro %ii %h
    subst h
    ihave Hs' := Hs
    unfold statusErrOk
    icases Hs $$ %ii %rfl with ⟨-, %Hleaf, #Hm⟩
    obtain ⟨-, hU1, hU2⟩ := Hleaf
    unfold _root_.Perennial.errors.errorIsNode
    simp only [hU1, hU2, ↓reduceIte]
    isplitl
    · split
      · rename_i hIs
        unfold grpcErrMethodsOk
        icases Hm with ⟨-, HIs⟩
        ihave #HIs := HIs $$ %hIs
        imodintro
        iintro %Φ - HΦ
        iapply HIs
        inext
        iintro %b
        iapply HΦ
        ipureintro; intro _; trivial
      · itrivial
    · itrivial
  · imodintro; iintro %ii %h
    subst h
    ileft; iexact Hs

end defs

end EtcdGrove
end Perennial
