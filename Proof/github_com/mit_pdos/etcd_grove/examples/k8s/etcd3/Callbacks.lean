/-
Lean-first (no Rocq counterpart).

# The driver's callbacks (stage 6d of `notes/k8s-etcd3-plan.md`)

A `Delete`'s `validateDeletion` (`validateFor(reject)`) and a `GuaranteedUpdate`'s `tryUpdate`
(`tryUpdateFor(in)`, through `updated`), as pure functions of the object: `rejD reject o` (an
object of value `reject` is rejected, none if `reject` is empty) and `updD in o` (rejected as
`rejD in.Reject`, otherwise the object with value `in.Val` and, if it had none, the name `in.Key`,
or unchanged if `in.NoOp`).

`validateD`/`tryUpdateD` are their closures' specs, with the exact error (the value of
`errDeleteRejected`/`errUpdateRejected`); `validateD_ok`/`tryUpdateD_ok` give the store's
`validateOk`/`tryUpdateOk` of them, for a store of `driverSpec`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjSpec
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Base
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Steps

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProofMode k8s
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input)

/-- Whether the callbacks reject an object of value `v`: `reject != "" && v == reject`. -/
def rejects (reject v : GoString) : Bool := decide (reject ≠ []) && decide (v = reject)


section upd
variable [GooseExts]

/-- **`validateFor(reject)`, as a function**: an object of value `reject` is rejected, with the
error `eD` (`errDeleteRejected`'s). -/
def rejD (eD : GoInterface) (reject : GoString) (o : DObj) (_ : Nat) : Option GoInterface :=
  if rejects reject o.val then some eD else none

/-- `updated(in, o)`'s name: the key's, for the zero object (no name; met with
`ignoreNotFound`). -/
def updName (inp : Input) (o : DObj) : GoString := if o.name = [] then inp.Key' else o.name

/-- `updated(in, o)`'s object: the value `in.Val` and the name `updName`, unless `in.NoOp` (the
UID kept). A key of 256 bytes or more (never drawn: `GenIn`) keeps the name, to stay a `DObj`. -/
def updObj (inp : Input) (o : DObj) : DObj :=
  if inp.NoOp' then o
  else if h : (updName inp o).length < 256 then ⟨(updName inp o, o.uid, inp.Val'), h, o.2.2⟩
  else ⟨(o.name, o.uid, inp.Val'), o.2⟩

/-- `updObj`'s fields, for a key shorter than 256 bytes. -/
theorem updObj_fields (inp : Input) (o : DObj) (hk : inp.Key'.length < 256) :
    (updObj inp o).name = (if inp.NoOp' then o.name else if o.name = [] then inp.Key' else o.name) ∧
    (updObj inp o).uid = o.uid ∧
    (updObj inp o).val = (if inp.NoOp' then o.val else inp.Val') := by
  by_cases hn : inp.NoOp' = true
  · simp [updObj, hn]
  · have hl : (updName inp o).length < 256 := by
      unfold updName; split
      · exact hk
      · exact o.2.1
    have hn' : inp.NoOp' = false := by simpa using hn
    unfold updObj
    simp only [hn', Bool.false_eq_true, ↓reduceIte]
    simp only [hl, ↓reduceDIte]
    exact ⟨rfl, trivial, trivial⟩

/-- **`tryUpdateFor(in)`, as a function**: rejected as `rejD` on `in.Reject`, with the error `eU`
(`errUpdateRejected`'s), otherwise `updObj`. -/
def updD (eU : GoInterface) (inp : Input) (o : DObj) (_ : Nat) : Except GoInterface DObj :=
  if rejects inp.Reject' o.val then .error eU else .ok (updObj inp o)

end upd

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- **`validateFor(reject)`'s closure** (persistent): on a `*Obj` (the store's objects, the
model's copies), `nil` or the value of `errDeleteRejected`, as `rejects`. -/
def validateD (reject : GoString) (vf : GoFunc) : IProp GF :=
  iprop(□ ∀ (ctx : GoInterface) (p : Loc) (name uid vl : GoString) (n : w64) (Ψ : val → IProp GF),
    p ↦ github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.mk name uid vl n -∗
    ▷ (∀ err : GoInterface, p ↦ github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj.mk name uid vl n -∗
        (if rejects reject vl then
          globalAddr github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.errDeleteRejected ↦□ err
        else ⌜err = GoInterface.nil⌝) -∗ Ψ #err) -∗
    WP (App (App (Val #vf) (Val #ctx))
      (Val #(interface.mkOk (go.GoType.PointerType objTyD) #p))) {{ Ψ }})

instance validateD_persistent (reject : GoString) (vf : GoFunc) :
    Persistent (validateD (GF := GF) reject vf) := by
  unfold validateD; infer_instance

/-- **`tryUpdateFor(in)`'s closure** (persistent): on an object, `updObj`'s (a new object, with
the input's resource version) with no TTL, or the value of `errUpdateRejected`. (`in.Key` is
shorter than 256 bytes: `tryUpdateFor`'s premise.) -/
def tryUpdateD (inp : Input) (uf : GoFunc) : IProp GF :=
  iprop(□ ∀ (x : GoInterface) (o : DObj) (r : w64) (Ψ : val → IProp GF),
    objAtD x o (rvStr r) -∗
    ▷ (∀ (ret : GoInterface) (ttlp : Loc) (err : GoInterface),
        (if rejects inp.Reject' o.val then
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
    (reject : GoString) (vf : GoFunc) :
    github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.errVarOk (GF := GF) github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.errDeleteRejected
        go!"k8setcd3: deletion rejected" ∗
      globalAddr github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.errDeleteRejected ↦□ eD ∗
      validateD reject vf ⊢ validateOk c (rejD eD reject) vf := by
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
  cases hr : rejects reject o.val
  · isimp only [hr, Bool.false_eq_true, ↓reduceIte] at Herr
    simp only [hr, Bool.false_eq_true, ↓reduceIte]
    iexact Herr
  · isimp only [hr, ↓reduceIte] at Herr
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
  cases hr : rejects inp.Reject' o.val
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
