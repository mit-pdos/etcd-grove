/-
Lean-first (no Rocq counterpart).

# `k8s.io/apiserver/pkg/storage`: a failed precondition's message (stage 7g)

- `KPre.failMsg p uid rvs`: the message `(*Preconditions).Check` formats when the preconditions
  `p` fail on an object with the UID `uid` and resource version string `rvs` (`interfaces.go:145`:
  the UID's test first).
- `invalidErrMsg err key msg`: `NewInvalidObjError(key, msg)`'s error, with its inner
  `errors.New(msg)` (an `*errorString` holding `msg`, read-only); `invalidErrMsg_is` forgets the
  message (`invalidErrIs`).
- `wp_New_errorString_ro`: `errors.New(msg)` with its `errorString` read-only (as
  `wp_New_errorString_cell`, keeping the whole struct).
- `sprintfOut_lit`, `sprintfOut_v2`: the output of `Sprintf` on a literal without `%`, and on
  `pre%vmid%v` with two string arguments (local; candidates for Perennial's `fmt`,
  `notes/perennial-changes.md`).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.Defs
public import Perennial.Proof.errors.Base
public import Perennial.Proof.fmt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

/-- **`Check`'s message** when the preconditions `p` fail on an object with the UID `uid` and the
resource version string `rvs` (`interfaces.go:157-169`): the UID's mismatch if there is one, else
the resource version's. (Meaningful only when `p.ok uid rvs = false`.) -/
def KPre.failMsg (p : KPre) (uid rvs : GoString) : GoString :=
  if p.uid.all (· = uid) then
    go!"Precondition failed: ResourceVersion in precondition: " ++ p.rv.getD [] ++
      go!", ResourceVersion in object meta: " ++ rvs
  else
    go!"Precondition failed: UID in precondition: " ++ p.uid.getD [] ++
      go!", UID in object meta: " ++ uid

/-- `Sprintf` copies a literal without `%` to its output. -/
theorem sprintfOut_lit [GooseExts] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]
    {lit f : GoString} {args : List GoInterface} {out : GoString}
    (hl : W8 37 ∉ lit) (h : _root_.Perennial.fmt.SprintfOut (lit ++ f) args out) :
    ∃ out', out = lit ++ out' ∧ _root_.Perennial.fmt.SprintfOut f args out' := by
  induction lit generalizing out with
  | nil => exact ⟨out, rfl, h⟩
  | cons c l ih =>
    have hc : c ≠ W8 37 := fun e => hl (e ▸ List.mem_cons_self ..)
    obtain ⟨o1, rfl, h1⟩ := _root_.Perennial.fmt.SprintfOut.byte_inv hc h
    obtain ⟨o2, rfl, h2⟩ := ih (fun m => hl (List.mem_cons_of_mem _ m)) h1
    exact ⟨o2, rfl, h2⟩

/-- `Sprintf(pre + "%v" + mid + "%v", a, b)`, with `pre` and `mid` without `%` and two string
arguments (`StrArgValue`), is `pre ++ x ++ mid ++ y`. -/
theorem sprintfOut_v2 [GooseExts] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]
    [go.IntoValInj GoString] [go.string ↓u go.string]
    {pre mid x y out : GoString} {a b : GoInterfaceOk}
    (hp : W8 37 ∉ pre) (hm : W8 37 ∉ mid)
    (ha : _root_.Perennial.fmt.StrArgValue a x) (hb : _root_.Perennial.fmt.StrArgValue b y)
    (h : _root_.Perennial.fmt.SprintfOut (pre ++ W8 37 :: W8 118 :: (mid ++ [W8 37, W8 118]))
      [interface.ok a, interface.ok b] out) :
    out = pre ++ x ++ mid ++ y := by
  obtain ⟨o1, rfl, h1⟩ := sprintfOut_lit hp h
  obtain ⟨o2, rfl, h2⟩ := _root_.Perennial.fmt.SprintfOut.strArg_inv (.inr rfl) ha
    (fun _ => ha.1.not_isIntArgType) h1
  obtain ⟨o3, rfl, h3⟩ := sprintfOut_lit hm h2
  have h3' : _root_.Perennial.fmt.SprintfOut (W8 37 :: W8 118 :: []) [interface.ok b] o3 := h3
  have := _root_.Perennial.fmt.SprintfOut.v_str hb o3 h3'
  subst this
  simp

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`NewInvalidObjError(key, msg)`'s error** (persistent): a `*StorageError` with code `4`
(`ErrCodeInvalidObj`), the key, and the inner error `errors.New(msg)` (an `*errorString` holding
`msg`, read-only). -/
def invalidErrMsg (err : GoInterface) (key msg : GoString) : IProp GF :=
  iprop(∃ (l x : Loc), ⌜err = interface.mkOk
      (go.GoType.PointerType k8s_io.apiserver.pkg.storage.StorageError.ty) #l⌝ ∗
    l ↦□ k8s_io.apiserver.pkg.storage.StorageError.mk (W64 4) key (W64 0)
      (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) ∗
    x ↦□ _root_.Perennial.errors.errorString.mk msg)

instance invalidErrMsg_persistent (err : GoInterface) (key msg : GoString) :
    Persistent (invalidErrMsg (GF := GF) err key msg) := by
  unfold invalidErrMsg; infer_instance

/-- The message forgotten. -/
theorem invalidErrMsg_is (err : GoInterface) (key msg : GoString) :
    invalidErrMsg (GF := GF) err key msg ⊢ invalidErrIs err key := by
  unfold invalidErrMsg invalidErrIs
  iintro ⟨%l, %x, %he, #Hl, -⟩
  iexists l, _
  iframe Hl
  ipureintro; exact he

end defs

section wp
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [errors_sem : _root_.Perennial.errors.Assumptions]

open Iris.ProgramLogic Iris.Std Iris.ProofMode in
/-- **`errors.New(msg)`, its `errorString` read-only** (`wp_New_errorString_cell`'s proof, keeping
the whole struct). -/
theorem wp_New_errorString_ro (msg : GoString) :
    {{ (True : IProp GF) }}
      (App (Val (@! _root_.Perennial.errors.New)) (Val #msg))
    {{ (x : Loc), RET #(interface.mkOk
        (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x);
        x ↦□ _root_.Perennial.errors.errorString.mk msg }} := by
  wp_start
  wp_auto
  wp_alloc x as Hx
  ipersist Hx
  wp_auto
  iapply HΦ
  iexact Hx

end wp

end k8s
end EtcdGrove
end Perennial
