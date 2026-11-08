/-
Lean-first (no Rocq counterpart).

# The driver's model: lists and the store's history (stage 7e-3b of `notes/k8s-7e-scope.md`)

`examples/k8s/etcd3/k8setcd3.go`'s list (`mlist`, the Model's `list`) and the history of stores
its past-revision reads use, as the pure functions its helpers compute (their specs state them,
`Spec/.../k8s/etcd3/<fn>.lean`):

- the selectors: `labelSelL x`, `fieldSelForL x` (the Go values `predicate(in)` holds) and what
  they select, `selOkL x o` (`labelSel.Matches`/`fieldSel.Matches` on `getAttrs(o)`), and
  `predEmptyL x` (`SelectionPredicate.Empty`: no selector);
- `pastReadL` (a read at the requested revision), `keyInScopeL` (the scope, with the `/`
  boundary);
- the loop, `listLoopL x its`: `ListModel.loop` (7e-3a) on the items in scope, keyed by their store
  keys;
- `encL`, the continue token of `storage.EncodeContinue` on a key, a prefix and a revision: an
  opaque function (both the store and the Go model call the same `EncodeContinue`; no property of
  it is used, Q7e-1), defined only when the prefix is a non-empty prefix of the key (`encOkL`);
- `HSt`, the model's state: a store and its history (`hist[R-1]` the store at revision `R`),
  `histAtL` (`histAt`), `advanceL` (`advance`: the history grows iff the revision does);
- `mlistL x h` (`mlist(in, c)`) and **`kstepL`**, the model's step: `mlistL` for a list, else
  `mstepL` with the history advanced; **`kSpec h0`**, the driver's model, linkv's `PendSpec` of
  `kstepL` from the seeded `h0`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.KModel
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ListModel
public import Proof.k8s_io.apiserver.pkg.storage.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input Output item labelSel fieldSel)

section go
variable [GooseExts]

/-! ## The selectors -/

/-- `predicate(in)`'s label selector: `app = SelApp`, everything if `SelApp` is empty. -/
def labelSelL (x : Input) : labelSel := ⟨decide (x.SelApp' = []), x.SelApp'⟩

/-- `fieldSelFor(in)`. -/
def fieldSelForL (x : Input) : fieldSel :=
  if x.Field' = W64 1 then ⟨W64 1, go!"metadata.name", x.SelName', [], []⟩
  else if x.Field' = W64 2 then ⟨W64 1, go!"metadata.namespace", x.SelNS', [], []⟩
  else if x.Field' = W64 3 then ⟨W64 1, go!"spec.nodeName", x.SelNode', [], []⟩
  else if x.Field' = W64 4 then ⟨W64 1, go!"spec.nodeName", [], [], []⟩
  else if x.Field' = W64 5 then
    ⟨W64 2, go!"metadata.namespace", x.SelNS', go!"spec.nodeName", x.SelNode'⟩
  else ⟨W64 0, [], [], [], []⟩

/-- `getAttrs(o)`'s fields, as `fields.Set.Get` reads them (empty for any other field). -/
def objField (o : Obj) (f : GoString) : GoString :=
  if f = go!"metadata.name" then o.Name'
  else if f = go!"metadata.namespace" then o.Namespace'
  else if f = go!"spec.nodeName" then o.Node'
  else []

/-- `fieldSel.Matches` on `getAttrs(o)`'s fields. -/
def fieldSelOk (s : fieldSel) (o : Obj) : Bool :=
  (!decide (1 ≤ sint.Z s.n')).or (decide (objField o s.f1' = s.v1')) &&
    (!decide (2 ≤ sint.Z s.n')).or (decide (objField o s.f2' = s.v2'))

/-- `labelSel.Matches` on `getAttrs(o)`'s labels (`objLabels(o)`: `app`, if not empty). -/
def labelSelOk (s : labelSel) (o : Obj) : Bool :=
  s.all'.or (decide (o.App' ≠ []) && decide (o.App' = s.app'))

/-- What a list of `x` selects: `predicate(in).Matches(o)`. -/
def selOkL (x : Input) (o : Obj) : Bool := labelSelOk (labelSelL x) o && fieldSelOk (fieldSelForL x) o

/-- `predicate(in).Empty()`: no selector. -/
def predEmptyL (x : Input) : Bool := (labelSelL x).all' && decide ((fieldSelForL x).n' = W64 0)

/-! ## The list -/

/-- `pastRead(in, req)`: a read at the requested revision `req` (`Exact`, or the legacy match
recursive with a limit), not at the latest one. -/
def pastReadL (x : Input) (req : w64) : Bool :=
  if x.MinRV' = [] ∨ req = W64 0 then false
  else (decide (x.Match' = W64 2)).or
    (decide (x.Match' = W64 0) && x.Recursive' && decide (0 < sint.Z x.Limit'))

/-- `matchOpt(in)`: the match's `metav1.ResourceVersionMatch` (`""` for the legacy one). -/
def matchOptL (x : Input) : GoString :=
  if x.Match' = W64 1 then go!"NotOlderThan" else if x.Match' = W64 2 then go!"Exact" else []

/-- `strings.TrimSuffix(s, suf)`. -/
def trimSufL (s suf : GoString) : GoString :=
  if suf <:+ s then s.take (s.length - suf.length) else s

/-- `keyInScope(key, recursive, k)`. -/
def keyInScopeL (key : GoString) (r : Bool) (k : GoString) : Bool :=
  if r then decide ((trimSufL key go!"/" ++ go!"/") <+: k) else decide (k = key)

/-- The items of `its` in a list of `x`'s scope, keyed by their store keys, in order. -/
def scopeL (x : Input) (its : List item) : List (GoString × Obj) :=
  (its.map fun it => (storeKeyL it.key', it.obj')).filter
    fun ko => keyInScopeL x.ListKey' x.Recursive' ko.1

/-- A list's limit (none for a limit `≤ 0`). -/
def limitN (x : Input) : Nat := if 0 < sint.Z x.Limit' then (sint.Z x.Limit').toNat else 0

/-- `mlist`'s loop on the store items `its`. -/
def listLoopL (x : Input) (its : List item) : ListModel.LState w8 Obj :=
  ListModel.loop (selOkL x) (limitN x) (scopeL x its)

/-- `storage.EncodeContinue(key, prefix, rv)`'s token, where it is defined (`encOkL`). Opaque:
nothing about the token is used, only that the store and the model compute the same (Q7e-1). -/
opaque encL : GoString → GoString → w64 → GoString

/-- `EncodeContinue(key, prefix, rv)` has no error: `strings.TrimPrefix(key, prefix)` is not
`key` (and `json.Marshal` of a continue token never fails). -/
def encOkL (key pfx : GoString) : Bool := decide (pfx ≠ [] ∧ pfx <+: key)

/-- A list's answer from the store `st` read, its loop's state `s` and the prepared key. -/
def listOutL (x : Input) (st : GSt) (s : ListModel.LState w8 Obj) (prepared : GoString) : Output :=
  let key := go!"/registry" ++ s.last.getD [] ++ [W8 0]
  let pfx := go!"/registry" ++ prepared
  if s.more then
    if encOkL key pfx then
      ⟨W64 0, [], 0, [], [], [], [], [], [], 0, encItemsL s.items.reverse, st.rv,
        encL key pfx st.rv, predEmptyL x,
        if predEmptyL x then W64 (s.total : Int) - x.Limit' else 0, [], false⟩
    else otherL
  else ⟨W64 0, [], 0, [], [], [], [], [], [], 0, encItemsL s.items.reverse, st.rv, [], false, 0, [],
    false⟩

section vals
variable [GoSemanticsFunctions] [GoGlobalContext]

/-- `predicate(in)`: a list's selection predicate (the driver's selectors, `getAttrs`, the limit). -/
def predV (x : Input) : k8s_io.apiserver.pkg.storage.SelectionPredicate :=
  ⟨interface.mkOk github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.labelSel.ty #(labelSelL x),
    interface.mkOk github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.fieldSel.ty #(fieldSelForL x),
    functions github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.getAttrs [], zeroValDef, zeroValDef,
    x.Limit', zeroValDef, zeroValDef, zeroValDef⟩

/-- `listOptions(in)`: a list's `storage.ListOptions`. -/
def listOptsV (x : Input) : k8s_io.apiserver.pkg.storage.ListOptions :=
  ⟨x.MinRV', matchOptL x, predV x, x.Recursive', zeroValDef, zeroValDef, zeroValDef⟩

end vals

/-! ## The history -/

/-- The model's state: a store and its history (`hist[R-1]` the store at revision `R`; a
configuration's `st` and `hist`). -/
structure HSt where
  st : GSt
  hist : List GSt

instance HSt_decEq : DecidableEq HSt := fun a b =>
  decidable_of_iff (a.st = b.st ∧ a.hist = b.hist) (by cases a; cases b; simp)

/-- The empty store (`mstore{}`). -/
def zSt : GSt := ⟨[], 0⟩

/-- `histAt(h, r)`: the store at revision `r` (the last of the first `r`; the empty store for
`r = 0`). -/
def histAtL (hs : List GSt) (r : w64) : GSt := ((hs.take (uint.nat r)).getLast?).getD zSt

/-- `advance(c, st, pend)`'s store and history: the history grows iff the revision does. -/
def advanceL (h : HSt) (st : GSt) : HSt :=
  if st.rv ≠ h.st.rv then ⟨st, h.hist ++ [st]⟩ else ⟨st, h.hist⟩

theorem histAtL_nil (r : w64) : histAtL [] r = zSt := by simp [histAtL]

theorem histAtL_snoc_le (l : List GSt) (s : GSt) (r : w64) (h : uint.nat r ≤ l.length) :
    histAtL (l ++ [s]) r = histAtL l r := by
  unfold histAtL; rw [List.take_append_of_le_length h]

theorem histAtL_snoc_gt (l : List GSt) (s : GSt) (r : w64) (h : l.length < uint.nat r) :
    histAtL (l ++ [s]) r = s := by
  unfold histAtL; rw [List.take_of_length_le (by simp; omega)]; simp

/-- The store a list of `x` at the requested revision `req` reads. -/
def listStL (x : Input) (h : HSt) (req : w64) : GSt :=
  if pastReadL x req then histAtL h.hist req else h.st

/-- **`mlist(in, c)`**: `EOther` for a resource version that does not parse, `ETooLarge` for one
above the store's, `EOther` for a key `PrepareKey` rejects; else the loop on the store read. -/
def mlistL (x : Input) (h : HSt) : Output :=
  match parseRVD x.MinRV' with
  | none => otherL
  | some req =>
    if uint.nat h.st.rv < uint.nat req then tooLargeL
    else match k8s.prepareKeyM go!"/objs" x.ListKey' x.Recursive' with
      | none => otherL
      | some prepared =>
        listOutL x (listStL x h req) (listLoopL x (listStL x h req).items) prepared

/-- **The model's step**: a list answers `mlistL` and changes nothing; any other operation is
`mstepL`, with the history advanced (`step`'s `advance`). -/
def kstepL (x : Input) (h : HSt) : HSt × Output :=
  if x.Kind' = W64 4 then (h, mlistL x h)
  else (advanceL h (mstepL x h.st).1, (mstepL x h.st).2)

/-- **The driver's model** from the seeded store and its history `h0`. -/
abbrev kSpec (h0 : HSt) : linkv.PendSpec HSt Input Output := ⟨h0, kstepL, isWriteL⟩

/-- A write is no list: its step is `mstepL`'s, advanced (`closure`'s). -/
theorem kstepL_write (x : Input) (h : HSt) (hw : isWriteL x = true) :
    kstepL x h = (advanceL h (mstepL x h.st).1, (mstepL x h.st).2) := by
  have : x.Kind' ≠ W64 4 := by
    intro e; simp [isWriteL, e] at hw
  unfold kstepL; rw [if_neg this]

theorem advanceL_items (h : HSt) (st : GSt) : (advanceL h st).st = st := by
  unfold advanceL; split <;> rfl

theorem advanceL_hist_length (h : HSt) (st : GSt) :
    (advanceL h st).hist.length ≤ h.hist.length + 1 := by
  unfold advanceL; split <;> simp

end go

end k8s_etcd3
end EtcdGrove
end Perennial
