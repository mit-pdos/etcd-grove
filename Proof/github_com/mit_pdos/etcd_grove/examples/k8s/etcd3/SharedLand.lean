/-
Lean-first (no Rocq counterpart).

# Where a pending write lands (k8s-dist K9, `notes/k8s-dist-k9.md` §2.1, §2.2, §2.5)

The Lean twins of `export.go`'s `landings`, `shows` and `decodeItemRVs`, read off the Go, and the
vocabulary of `settle`'s spec:

- `RevsL`: a `Revs` as Lean values (`anchors`, sorted; `byKey`, `fastByKey`: `[]` for a key the map
  does not have);
- `decItemRVsL s`: `decodeItemRVs(s)`'s items (each object with its resource version), or none;
- `showsL x y key r`: `shows(in, out, key, r)`;
- `landingsL R rv w b full x y`: `landings(revs, c, w, b, full, in, out)` for a `c` at revision `rv`
  (`sort.Search` over the sorted anchors is `dropWhile`);
- `GoSettle R b full x y`: Go's `settle`, `SharedGo`'s `SettleWith` with `landingsL`;
- `revsOwn r R`: the `Revs` value `r` holds `R` (read-only).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.SharedDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.dist.SharedGo

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj Revs)

section pure
variable [GooseExts]

/-- A `Revs` as Lean values. -/
structure RevsL where
  anchors : List w64
  byKey : GoString → List w64
  fastByKey : GoString → List w64

/-- An object's item key (`Namespace + "/" + Name`). -/
def objKeyL (o : Obj) : GoString := o.Namespace' ++ go!"/" ++ o.Name'

/-- `decodeItemRVs(s)`: the objects `s` encodes (`encodeItems`), each with its resource version, or
none. -/
def decItemRVsL (s : GoString) : Option (List Obj) :=
  if h : s = [] then some []
  else if s.length < 16 then none
  else
    let r := s.drop 16
    let n := (bytesBE ((s.drop 8).take 8)).toNat
    if r.length < n then none
    else match decodeD (r.take n) with
      | none => none
      | some o =>
        (decItemRVsL (r.drop n)).map fun rest =>
          { o with ResourceVersion' := bytesBE (s.take 8) } :: rest
termination_by s.length
decreasing_by
  simp only [List.length_drop]
  have : s.length ≠ 0 := by simpa using h
  omega

/-- **`shows(in, out, key, r)`**: the answer `y` to `x` needs a write of `key` at `r` to have taken
effect. -/
def showsL (x : Input) (y : Output) (key : GoString) (r : w64) : Bool :=
  if x.Kind' = W64 5 then
    match decWEventsL y.WEvents' with
    | none => false
    | some evs =>
      if y.WFailed' then false
      else evs.any fun e => decide (e.t < 3) && decide (objKeyL e.o = key) &&
        decide (e.o.ResourceVersion' = r)
  else if x.Kind' = W64 4 then
    match decItemRVsL y.Items' with
    | none => false
    | some os =>
      if y.Err' ≠ W64 0 then false
      else os.any fun o => decide (objKeyL o = key) && decide (o.ResourceVersion' = r)
  else if x.Key' ≠ key then false
  else if y.Err' = W64 0 then decide (y.RV' = r)
  else decide (y.Err' = W64 2 ∨ y.Err' = W64 3 ∨ y.Err' = W64 5)

/-- `landings`' `add(r)` test. -/
def landOkL (rv : w64) (w : Input) (b : w64) (full : Bool) (x : Input) (y : Output) (r : w64) : Bool :=
  decide (uint.nat (rv + W64 1) < uint.nat r) &&
    ((full.or (decide (b ≠ W64 0) && decide (uint.nat r ≤ uint.nat b))).or (showsL x y w.Key' r))

/-- **`landings(revs, c, w, b, full, in, out)`** for `c` at revision `rv` (in the Go's order). -/
def landingsL (R : RevsL) (rv : w64) (w : Input) (b : w64) (full : Bool) (x : Input) (y : Output) :
    List w64 :=
  let ok := landOkL rv w b full x y
  let ls1 := [rv + W64 1] ++ ((if full then R.byKey else R.fastByKey) w.Key').filter ok
  let ls2 := if x.Key' = w.Key' ∧ y.Err' = W64 0 ∧ x.Kind' ≠ W64 4 ∧ x.Kind' ≠ W64 5
    then ls1 ++ [y.RV'].filter ok else ls1
  if full then
    ls2 ++ ((R.anchors.dropWhile fun a => decide (uint.nat a < uint.nat rv)).flatMap
      fun a => [a, a + W64 1]).filter ok
  else ls2

/-- **Go's `settle`**: `SettleWith` with `landingsL` (`b`: `bound`'s). -/
abbrev GoSettle (R : RevsL) (b : w64) (full : Bool) (x : Input) (y : Output) : GCfg → GCfg → Prop :=
  k8s_dist.SettleWith fun c w => (landingsL R c.st.st.rv w b full x y).map uint.nat

/-- The revisions `settle` may reach stay below `2^63` (each landing below `2^63 - 1`): every
revision `R` names, the answer's, and the configuration's. -/
def SettleOk (R : RevsL) (y : Output) (g : GCfg) : Prop :=
  (∀ a ∈ R.anchors, uint.nat a + 1 < 2 ^ 63) ∧ (∀ k, ∀ a ∈ R.byKey k, uint.nat a < 2 ^ 63) ∧
  (∀ k, ∀ a ∈ R.fastByKey k, uint.nat a < 2 ^ 63) ∧ uint.nat y.RV' < 2 ^ 63 ∧
  uint.nat g.st.st.rv + 1 < 2 ^ 63

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- A `map[string][]uint64` holding `f` (read-only; `[]` for a key it does not have). -/
def keyRevsOwn (m : GoMap) (f : GoString → List w64) : IProp GF :=
  iprop(∃ M : GMap GoString GoSlice, m ↦$□ M ∗ ⌜∀ k, M !! k = none → f k = []⌝ ∗
    [∗map] k ↦ sl ∈ M, sl ↦*□ f k)

/-- **The `Revs` value `r` holds `R`** (read-only; the anchors sorted). -/
def revsOwn (r : Revs) (R : RevsL) : IProp GF :=
  iprop(r.anchors' ↦*□ R.anchors ∗ ⌜R.anchors.Pairwise fun a b => uint.nat a < uint.nat b⌝ ∗
    keyRevsOwn r.byKey' R.byKey ∗ keyRevsOwn r.fastByKey' R.fastByKey)

instance keyRevsOwn_persistent (m : GoMap) (f : GoString → List w64) :
    Persistent (keyRevsOwn (GF := GF) m f) := by
  unfold keyRevsOwn; infer_instance

instance revsOwn_persistent (r : Revs) (R : RevsL) : Persistent (revsOwn (GF := GF) r R) := by
  unfold revsOwn; infer_instance

end defs

end k8s_etcd3
end EtcdGrove
end Perennial
