/-
The DaemonSet lister's expansion (`listers/apps/v1/daemonset_expansion.go`: `GetPodDaemonSets`,
`GetHistoryDaemonSets`): what their specs are stated with. Lean-first; phase 4 of
`notes/k8s-daemonset-plan.md` (the label-selector boundary).

* `metaView`: an object's `ObjectMeta` fields the expansion reads (its namespace,
  name, labels: read only, the labels a non-`nil` map).
* `dsSel OK`: the client's contract on the stored DaemonSets: each one's namespace and
  `Spec.Selector` are readable, the selector holding some value (`labels.lsOwn`).
* `selPicks ns L S dns`: a DaemonSet of namespace `dns` and selector `S` is one the expansion
  picks for an object of namespace `ns` (`ns = none`: any) and labels `L`: same namespace, a
  valid (`selValid`), non-empty selector (`labels.Everything()` matches nothing here) that selects
  `L`.
* `flagged ls bs`: the elements of `ls` whose flag in `bs` is set, in order.
-/
module

public import Proof.k8s_io.apimachinery.pkg.apis.meta.v1.SelDefs
public import Proof.k8s_io.client_go.listers.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace appslisters

open Iris Iris.BI labels listers

section model
variable [FfiSyntax]

/-- The DaemonSets the expansion picks: same namespace (if any), a valid, non-empty selector
selecting the labels. -/
def selPicks (ns : Option GoString) (L : GMap GoString GoString) (S : Option SelV)
    (dns : GoString) : Prop :=
  (∀ n, ns = some n → dns = n) ∧ selValid S ∧ selEmpty S = false ∧ selMatch S L

/-- The elements of `ls` whose flag is set, in order. -/
def flagged {A : Type} : List A → List Bool → List A
  | x :: xs, b :: bs => if b then x :: flagged xs bs else flagged xs bs
  | _, _ => []

@[simp] theorem flagged_nil {A : Type} (ls : List A) : flagged ls [] = [] := by
  cases ls <;> rfl

/-- One more flag. -/
theorem flagged_snoc {A : Type} (ls : List A) (bs : List Bool) (b : Bool) (d : A)
    (hd : ls[bs.length]? = some d) :
    flagged ls (bs ++ [b]) = flagged ls bs ++ (if b then [d] else []) := by
  induction bs generalizing ls with
  | nil =>
    cases ls with
    | nil => cases hd
    | cons x xs =>
      simp only [List.length_nil, List.getElem?_cons_zero, Option.some.injEq] at hd
      subst hd
      cases b <;> cases xs <;> simp [flagged]
  | cons c cs ih =>
    cases ls with
    | nil => cases hd
    | cons x xs =>
      simp only [List.length_cons, List.getElem?_cons_succ] at hd
      have := ih xs hd
      cases c <;> simp [flagged, this]

end model

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **An object's metadata** the expansion reads: namespace, name, and a non-`nil` labels map. -/
def metaView (m : Loc) (ns name : GoString) (L : GMap GoString GoString) : IProp GF :=
  iprop(structFieldRef k8s_io.apimachinery.pkg.apis.«meta».v1.ObjectMeta go!"Namespace" m ↦□ ns ∗
    structFieldRef k8s_io.apimachinery.pkg.apis.«meta».v1.ObjectMeta go!"Name" m ↦□ name ∗
    ∃ lm : Loc, structFieldRef k8s_io.apimachinery.pkg.apis.«meta».v1.ObjectMeta go!"Labels" m ↦□ lm ∗
      lm ↦${DFrac.discard} L)

instance metaView_persistent (m : Loc) (ns name : GoString) (L : GMap GoString GoString) :
    Persistent (metaView (GF := GF) m ns name L) := by
  unfold metaView; infer_instance

/-- **A stored DaemonSet's namespace and selector** (read only). -/
def dsView (d : Loc) (dns : GoString) (S : Option SelV) : IProp GF :=
  iprop(structFieldRef k8s_io.apimachinery.pkg.apis.«meta».v1.ObjectMeta go!"Namespace"
      (structFieldRef k8s_io.api.apps.v1.DaemonSet go!"ObjectMeta" d) ↦□ dns ∗
    ∃ ls : Loc, structFieldRef k8s_io.api.apps.v1.DaemonSetSpec go!"Selector"
      (structFieldRef k8s_io.api.apps.v1.DaemonSet go!"Spec" d) ↦□ ls ∗ lsOwn (GF := GF) ls S)

instance dsView_persistent (d : Loc) (dns : GoString) (S : Option SelV) :
    Persistent (dsView (GF := GF) d dns S) := by
  unfold dsView; infer_instance

/-- **The client's contract on the stored DaemonSets**: each readable (`dsView`). -/
def dsSel (OK : GoInterface → IProp GF) : IProp GF :=
  iprop(□ ∀ d : Loc, OK (ptrObj k8s_io.api.apps.v1.DaemonSet.ty d) -∗
    ∃ (dns : GoString) (S : Option SelV), dsView d dns S)

instance dsSel_persistent (OK : GoInterface → IProp GF) : Persistent (dsSel OK) := by
  unfold dsSel; infer_instance

open Classical in
open Iris.ProofMode in
/-- **One more DaemonSet visited**: its view and flag added to the visited ones'. -/
theorem visited_snoc (ls : List Loc) (bs : List Bool) (d : Loc) (hd : ls[bs.length]? = some d)
    (ns : Option GoString) (L : GMap GoString GoString) (dns : GoString) (S : Option SelV) (b : Bool)
    (hb : b = decide (selPicks ns L S dns)) :
    □ ([∗list] k ↦ d ∈ ls.take bs.length, ∃ (dns : GoString) (S : Option SelV),
        dsView (GF := GF) d dns S ∗ ⌜bs[k]? = some (decide (selPicks ns L S dns))⌝) ∗
      dsView d dns S ⊢
    □ ([∗list] k ↦ d ∈ ls.take (bs ++ [b]).length, ∃ (dns : GoString) (S : Option SelV),
        dsView d dns S ∗ ⌜(bs ++ [b])[k]? = some (decide (selPicks ns L S dns))⌝) := by
  iintro ⟨#H, #Hd⟩
  have hlt : bs.length < ls.length := by
    rcases (List.getElem?_eq_some_iff.1 hd) with ⟨h, -⟩; exact h
  rw [List.length_append, List.length_singleton, List.take_add_one, hd, Option.toList_some]
  imodintro
  iapply BigSepL.bigSepL_snoc.2
  isplitl
  · iapply (BigSepL.bigSepL_mono (fun {k x} hk => ?_)) $$ H
    have hk' : k < bs.length := by
      have := (List.getElem?_eq_some_iff.1 hk).1; simp at this; omega
    iintro ⟨%dns', %S', #Hv, %Hb⟩
    iexists dns', S'
    iframe #
    ipureintro
    rw [List.getElem?_append_left hk']; exact Hb
  · iexists dns, S
    iframe #
    ipureintro
    have : (List.take bs.length ls).length = bs.length := by simp; omega
    rw [this, List.getElem?_append_right (by omega)]
    simp [hb]

end defs

end appslisters
end EtcdGrove
end Perennial
