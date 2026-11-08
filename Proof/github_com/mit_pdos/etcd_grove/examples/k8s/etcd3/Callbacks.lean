/-
Lean-first (no Rocq counterpart).

# The driver's callbacks (stage 6d of `notes/k8s-etcd3-plan.md`)

A `Delete`'s `validateDeletion` (`validateFor(rejects, reject)`) and a `GuaranteedUpdate`'s
`tryUpdate` (`tryUpdateFor(in)`, through `updated`), as pure functions of the object (stage 7e: the
rejection is on the object's node, as the correctness test's): `rejD has reject o` (an object on
the node `reject` is rejected, if `has`) and `updD in o` (rejected on `in.Reject` if
`in.HasReject`, otherwise `updObj`: the object with `in`'s value, node and app and, if it had no
name, the key's namespace and name, `splitKeyL`; or unchanged if `in.NoOp`).

`validateD`/`tryUpdateD` are their closures' specs, with the exact error (the value of
`errDeleteRejected`/`errUpdateRejected`); `validateD_ok`/`tryUpdateD_ok` give the store's
`validateOk`/`tryUpdateOk` of them, for a store of `driverSpec`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjSpec
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Base
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Steps
public import Spec.strings.Cut

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProofMode k8s
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Obj)

/-- Whether the callbacks reject an object on the node `node`: `rejects && node == reject` (stage
7e: the test's callbacks reject on a drawn node). -/
def rejects (has : Bool) (reject node : GoString) : Bool := has && decide (node = reject)

/-- `splitKey(key)`: the namespace and the name, the key cut at its first `/` (`strings.Cut`). -/
def splitKeyL (key : GoString) : GoString × GoString := ((cutL key go!"/").1, (cutL key go!"/").2.1)

section upd
variable [GooseExts]

/-- **`validateFor(rejects, reject)`, as a function**: an object on the node `reject` is rejected
(if `rejects`), with the error `eD` (`errDeleteRejected`'s). -/
def rejD (eD : GoInterface) (has : Bool) (reject : GoString) (o : DObj) (_ : Nat) :
    Option GoInterface :=
  if rejects has reject o.node then some eD else none

/-- **`updated(in, o)`'s object, on Go's record**: unless `in.NoOp`, the value, node and app of
`in`, and, for the zero object (no name; met with `ignoreNotFound`), the key's namespace and name
(`splitKeyL`); the UID and resource version kept. -/
def updGo (inp : Input) (v : Obj) : Obj :=
  if inp.NoOp' then v
  else
    { v with
      Namespace' := if v.Name' = [] then (splitKeyL inp.Key').1 else v.Namespace'
      Name' := if v.Name' = [] then (splitKeyL inp.Key').2 else v.Name'
      Value' := inp.Val', Node' := inp.Node', App' := inp.App' }

/-- `updGo` keeps the resource version. -/
theorem updGo_rv (inp : Input) (v : Obj) : (updGo inp v).ResourceVersion' = v.ResourceVersion' := by
  unfold updGo; split <;> rfl

/-- `updGo` does not look at the resource version. -/
theorem updGo_toObj (inp : Input) (o : DObj) (n : w64) :
    updGo inp (o.toObj n) = { updGo inp (o.toObj 0) with ResourceVersion' := n } := by
  unfold updGo DObj.toObj; split <;> rfl

/-- `strings.Cut`'s parts are no longer than the string. -/
theorem cutL_length (s sep : GoString) :
    (cutL s sep).1.length ≤ s.length ∧ (cutL s sep).2.1.length ≤ s.length := by
  unfold cutL
  split <;> simp <;> omega

/-- The input's fields an update writes fit a `DObj` (`tryUpdateFor`'s premise: they are drawn
short, `GenIn`). -/
def inFits (inp : Input) : Prop :=
  inp.Key'.length < 256 ∧ inp.Node'.length < 256 ∧ inp.App'.length < 256

/-- `updated(in, o)`'s object: `updGo`'s, which fits for an input that does (`inFits`); else
(never: `tryUpdateFor`'s premise) the object unchanged. -/
def updObj (inp : Input) (o : DObj) : DObj :=
  if h : fitsD (updGo inp (o.toObj 0)) then DObj.ofObj _ h else o

theorem updGo_fits (inp : Input) (o : DObj) (n : w64) (hi : inFits inp) :
    fitsD (updGo inp (o.toObj n)) := by
  obtain ⟨hk, hn, ha⟩ := hi
  obtain ⟨f1, f2, f3, f4, f5⟩ := o.fits
  have hc := cutL_length inp.Key' go!"/"
  unfold updGo fitsD DObj.toObj splitKeyL
  split
  · exact ⟨f1, f2, f3, f4, f5⟩
  · simp only
    refine ⟨?_, ?_, f3, hn, ha⟩ <;> split <;> omega

/-- **`updObj`'s record is `updGo`'s**, for an input that fits. -/
theorem updObj_toObj (inp : Input) (o : DObj) (n : w64) (hi : inFits inp) :
    (updObj inp o).toObj n = updGo inp (o.toObj n) := by
  unfold updObj
  rw [dif_pos (updGo_fits inp o 0 hi), updGo_toObj inp o n]
  rfl

/-- **`tryUpdateFor(in)`, as a function**: rejected as `rejD` on the input's node, with the error
`eU` (`errUpdateRejected`'s), otherwise `updObj`. -/
def updD (eU : GoInterface) (inp : Input) (o : DObj) (_ : Nat) : Except GoInterface DObj :=
  if rejects inp.HasReject' inp.Reject' o.node then .error eU else .ok (updObj inp o)

end upd

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- **`validateFor(reject)`'s closure** (persistent): on a `*Obj` (the store's objects, the
model's copies), `nil` or the value of `errDeleteRejected`, as `rejects`. -/
def validateD (has : Bool) (reject : GoString) (vf : GoFunc) : IProp GF :=
  iprop(□ ∀ (ctx : GoInterface) (p : Loc) (v : Obj) (Ψ : val → IProp GF),
    p ↦ v -∗
    ▷ (∀ err : GoInterface, p ↦ v -∗
        (if rejects has reject v.Node' then
          globalAddr github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.errDeleteRejected ↦□ err
        else ⌜err = GoInterface.nil⌝) -∗ Ψ #err) -∗
    WP (App (App (Val #vf) (Val #ctx))
      (Val #(interface.mkOk (go.GoType.PointerType objTyD) #p))) {{ Ψ }})

instance validateD_persistent (has : Bool) (reject : GoString) (vf : GoFunc) :
    Persistent (validateD (GF := GF) has reject vf) := by
  unfold validateD; infer_instance

/-- **`tryUpdateFor(in)`'s closure** (persistent): on an object, `updObj`'s (a new object, with
the input's resource version) with no TTL, or the value of `errUpdateRejected`. (The input fits,
`inFits`: `tryUpdateFor`'s premise.) -/
def tryUpdateD (inp : Input) (uf : GoFunc) : IProp GF :=
  iprop(□ ∀ (x : GoInterface) (o : DObj) (r : w64) (Ψ : val → IProp GF),
    objAtD x o (rvStr r) -∗
    ▷ (∀ (ret : GoInterface) (ttlp : Loc) (err : GoInterface),
        (if rejects inp.HasReject' inp.Reject' o.node then
          globalAddr github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.errUpdateRejected ↦□ err
        else ⌜err = GoInterface.nil ∧ ttlp = null⌝ ∗ objAtD ret (updObj inp o) (rvStr r)) -∗
        Ψ (PairV (PairV #ret #ttlp) #err)) -∗
    WP (App (App (Val #uf) (Val #x))
      (Val #(k8s_io.apiserver.pkg.storage.ResponseMeta.mk (W64 0) r))) {{ Ψ }})

instance tryUpdateD_persistent (inp : Input) (uf : GoFunc) :
    Persistent (tryUpdateD (GF := GF) inp uf) := by
  unfold tryUpdateD; infer_instance

/-- An error variable's value is not `nil`. -/
theorem errVar_ne_nil (x : GoString) {msg : GoString} (err : GoInterface) :
    github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.errVarOk (GF := GF) x msg ∗ globalAddr x ↦□ err ⊢ ⌜err ≠ GoInterface.nil⌝ := by
  iintro ⟨⟨%e, #He, -⟩, #Hx⟩
  icombine He Hx gives %Heq
  ipureintro
  rw [← Heq]
  nofun

/-- **The store's `validateOk` of `validateFor(reject)`'s closure.** -/
theorem validateD_ok (c : StoreCfg GF DObj) (hc : c.S = driverSpec) (eD : GoInterface)
    (has : Bool) (reject : GoString) (vf : GoFunc) :
    github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.errVarOk (GF := GF) github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.errDeleteRejected
        go!"k8setcd3: deletion rejected" ∗
      globalAddr github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.errDeleteRejected ↦□ eD ∗
      validateD has reject vf ⊢ validateOk c (rejD eD has reject) vf := by
  iintro ⟨#He, #HeD, #Hv⟩
  unfold validateOk
  rw [hc]
  iunfold validateD at Hv
  simp only [driverSpec, driverCodec]
  imodintro
  iintro %ctx %x %o %r %Ψ Ho HΨ
  iunfold objAtD at Ho
  icases Ho with ⟨%p, %n, %Hx, Hp⟩
  obtain ⟨rfl, Hpn, Hrv⟩ := Hx
  iapply Hv $$ Hp
  inext
  iintro %err Hp Herr
  iapply HΨ $$ [Hp]
  · iunfold objAtD
    iexists p, n
    iframe Hp
    ipureintro; exact ⟨rfl, Hpn, Hrv⟩
  unfold rejD
  have hnode : (o.toObj n).Node' = o.node := rfl
  cases hr : rejects has reject o.node
  · isimp only [hnode, hr, Bool.false_eq_true, ↓reduceIte] at Herr
    simp only [hr, Bool.false_eq_true, ↓reduceIte]
    iexact Herr
  · isimp only [hnode, hr, ↓reduceIte] at Herr
    simp only [hr, ↓reduceIte]
    ihave %Hne := errVar_ne_nil _ err $$ [$He $Herr]
    icombine HeD Herr gives %Heq
    ipureintro; exact ⟨Hne, Heq.symm⟩

/-- **The store's `tryUpdateOk` of `tryUpdateFor(in)`'s closure.** -/
theorem tryUpdateD_ok (c : StoreCfg GF DObj) (hc : c.S = driverSpec) (eU : GoInterface)
    (inp : Input) (uf : GoFunc) :
    github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.errVarOk (GF := GF) github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.errUpdateRejected
        go!"k8setcd3: update rejected" ∗
      globalAddr github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.errUpdateRejected ↦□ eU ∗
      tryUpdateD inp uf ⊢ tryUpdateOk c (updD eU inp) uf := by
  iintro ⟨#He, #HeU, #Hu⟩
  unfold tryUpdateOk
  rw [hc]
  iunfold tryUpdateD at Hu
  simp only [driverSpec, driverCodec]
  imodintro
  iintro %x %o %r %Ψ Ho HΨ
  iapply Hu $$ Ho
  inext
  iintro %ret %ttlp %err Hr
  iapply HΨ
  unfold updD
  cases hr : rejects inp.HasReject' inp.Reject' o.node
  · isimp only [hr, Bool.false_eq_true, ↓reduceIte] at Hr
    simp only [hr, Bool.false_eq_true, ↓reduceIte]
    icases Hr with ⟨%Hn, Ho'⟩
    iframe
    ipureintro; exact Hn
  · isimp only [hr, ↓reduceIte] at Hr
    simp only [hr, ↓reduceIte]
    ihave %Hne := errVar_ne_nil _ err $$ [$He $Hr]
    icombine HeU Hr gives %Heq
    ipureintro; exact ⟨Hne, Heq.symm⟩

end defs

end k8s_etcd3
end EtcdGrove
end Perennial
