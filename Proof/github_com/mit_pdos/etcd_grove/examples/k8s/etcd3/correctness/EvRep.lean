/-
Lean-first (no Rocq counterpart).

# Watch events in the heap (k8s 7g step 5)

The predicates the watch specs (the driver's `consume`/`runWatch`/`realEvents`, the checker's
`WatchValidator`) are written in, over `RReplay.lean`'s `REv`:

- `evObjRep x o`: the event object `x` has the view `o`: a read-only `*Obj` (`deepRO`, what
  `reflect.DeepEqual` reads) or a read-only `*metav1.Status` with its `Status` field. No view is
  given to any other dynamic type (`.other` is `False`): the driver's events never hold one (the
  store's watch delivers objects and failure statuses only, `wevAt`), so the specs say nothing
  about them;
- `evRep v r`: the `watch.Event` `v` has the view `r` (its type, its object);
- `evsRO sl rs`: the `[]watch.Event` slice `sl` is read-only and holds events of views `rs`.

All three are persistent: an event is never written once received.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI k8sDeep
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj)

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The event object `x` has the view `o`** (see the file header). -/
def evObjRep (x : GoInterface) : REvObj → IProp GF
  | .obj o => deepRO x (.obj o)
  | .status s => iprop(∃ (p : Loc) (st : k8s_io.apimachinery.pkg.apis.«meta».v1.Status),
      ⌜x = interface.mkOk (go.GoType.PointerType k8s_io.apimachinery.pkg.apis.«meta».v1.Status.ty) #p ∧
        st.Status' = s⌝ ∗ p ↦□ st)
  | .other => iprop(False)

instance evObjRep_persistent (x : GoInterface) (o : REvObj) :
    Persistent (evObjRep (GF := GF) x o) := by
  cases o <;> unfold evObjRep <;> infer_instance

/-- **The `watch.Event` `v` has the view `r`** (persistent). -/
def evRep (v : k8s_io.apimachinery.pkg.watch.Event) (r : REv) : IProp GF :=
  iprop(⌜v.Type' = r.ty⌝ ∗ evObjRep v.Object' r.o)

instance evRep_persistent (v : k8s_io.apimachinery.pkg.watch.Event) (r : REv) :
    Persistent (evRep (GF := GF) v r) := by
  unfold evRep; infer_instance

/-- **The `[]watch.Event` slice `sl` holds events of views `rs`**, read-only (persistent). -/
def evsRO (sl : GoSlice) (rs : List REv) : IProp GF :=
  iprop(∃ vs : List k8s_io.apimachinery.pkg.watch.Event, sl ↦*□ vs ∗ [∗list] v;r ∈ vs;rs, evRep v r)

instance evsRO_persistent (sl : GoSlice) (rs : List REv) : Persistent (evsRO (GF := GF) sl rs) := by
  unfold evsRO; infer_instance

/-- No event: the nil slice. -/
theorem evsRO_nil : ⊢ evsRO (GF := GF) slice.nil [] := by
  unfold evsRO
  iexists []
  isplitl
  · iapply ownSlice_nil
  · iapply BigSepL2.bigSepL2_nil.2; itrivial

end defs

end k8s_correctness
end EtcdGrove
end Perennial
