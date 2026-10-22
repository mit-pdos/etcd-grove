/-
Lean-first (no Rocq counterpart).

# The driver's callbacks (stage 6d of `notes/k8s-etcd3-plan.md`)

A `Delete`'s `validateDeletion` (`validateFor(reject)`) and a `GuaranteedUpdate`'s `tryUpdate`
(`tryUpdateFor(in)`, through `updated`), as pure functions of the object: `rejD reject o` (an
object of value `reject` is rejected, none if `reject` is empty) and `updD in o` (rejected as
`rejD in.Reject`, otherwise the object with value `in.Val`, or unchanged if `in.NoOp`).

`validateD`/`tryUpdateD` are their closures' specs, with the exact error (the value of
`errDeleteRejected`/`errUpdateRejected`); `validateD_ok`/`tryUpdateD_ok` give the store's
`validateOk`/`tryUpdateOk` of them, for a store of `driverSpec`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.ObjSpec
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.Base
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Steps

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI Iris.ProofMode k8s
open github_com.mit_pdos.etcd_grove.examples.k8setcd3 (Input)

/-- Whether the callbacks reject an object of value `v`: `reject != "" && v == reject`. -/
def rejects (reject v : GoString) : Bool := decide (reject ≠ []) && decide (v = reject)


section upd
variable [FfiSyntax]

/-- **`validateFor(reject)`, as a function**: an object of value `reject` is rejected, with the
error `eD` (`errDeleteRejected`'s). -/
def rejD (eD : GoInterface) (reject : GoString) (o : DObj) (_ : Nat) : Option GoInterface :=
  if rejects reject o.1.2 then some eD else none

/-- `updated(in, o)`'s object: the value `in.Val`, unless `in.NoOp`. -/
def updObj (inp : Input) (o : DObj) : DObj :=
  ⟨(o.1.1, if inp.NoOp' then o.1.2 else inp.Val'), o.2⟩

/-- **`tryUpdateFor(in)`, as a function**: rejected as `rejD` on `in.Reject`, with the error `eU`
(`errUpdateRejected`'s), otherwise `updObj`. -/
def updD (eU : GoInterface) (inp : Input) (o : DObj) (_ : Nat) : Except GoInterface DObj :=
  if rejects inp.Reject' o.1.2 then .error eU else .ok (updObj inp o)

end upd

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

/-- **`validateFor(reject)`'s closure** (persistent): on an object, `nil` or the value of
`errDeleteRejected`, as `rejD`. -/
def validateD (reject : GoString) (vf : GoFunc) : IProp GF :=
  iprop(□ ∀ (ctx x : GoInterface) (o : DObj) (r : w64) (Ψ : val → IProp GF),
    objAtD x o (rvStr r) -∗
    ▷ (∀ err : GoInterface, objAtD x o (rvStr r) -∗
        (if rejects reject o.1.2 then
          globalAddr github_com.mit_pdos.etcd_grove.examples.k8setcd3.errDeleteRejected ↦□ err
        else ⌜err = GoInterface.nil⌝) -∗ Ψ #err) -∗
    WP (App (App (Val #vf) (Val #ctx)) (Val #x)) {{ Ψ }})

instance validateD_persistent (reject : GoString) (vf : GoFunc) :
    Persistent (validateD (GF := GF) reject vf) := by
  unfold validateD; infer_instance

/-- **`tryUpdateFor(in)`'s closure** (persistent): on an object, `updObj`'s (a new object, with
the input's resource version) with no TTL, or the value of `errUpdateRejected`. -/
def tryUpdateD (inp : Input) (uf : GoFunc) : IProp GF :=
  iprop(□ ∀ (x : GoInterface) (o : DObj) (r : w64) (Ψ : val → IProp GF),
    objAtD x o (rvStr r) -∗
    ▷ (∀ (ret : GoInterface) (ttlp : Loc) (err : GoInterface),
        (if rejects inp.Reject' o.1.2 then
          globalAddr github_com.mit_pdos.etcd_grove.examples.k8setcd3.errUpdateRejected ↦□ err
        else ⌜err = GoInterface.nil ∧ ttlp = null⌝ ∗ objAtD ret (updObj inp o) (rvStr r)) -∗
        Ψ (PairV (PairV #ret #ttlp) #err)) -∗
    WP (App (App (Val #uf) (Val #x))
      (Val #(k8s_io.apiserver.pkg.storage.ResponseMeta.mk (W64 0) r))) {{ Ψ }})

instance tryUpdateD_persistent (inp : Input) (uf : GoFunc) :
    Persistent (tryUpdateD (GF := GF) inp uf) := by
  unfold tryUpdateD; infer_instance

/-- An error variable's value is not `nil`. -/
theorem errVar_ne_nil (x : GoString) (err : GoInterface) :
    github_com.mit_pdos.etcd_grove.examples.k8setcd3.errVarOk (GF := GF) x ∗ globalAddr x ↦□ err ⊢ ⌜err ≠ GoInterface.nil⌝ := by
  iintro ⟨⟨%e, #He, -⟩, #Hx⟩
  icombine He Hx gives %Heq
  ipureintro
  rw [← Heq]
  nofun

/-- **The store's `validateOk` of `validateFor(reject)`'s closure.** -/
theorem validateD_ok (c : StoreCfg GF DObj) (hc : c.S = driverSpec) (eD : GoInterface)
    (reject : GoString) (vf : GoFunc) :
    github_com.mit_pdos.etcd_grove.examples.k8setcd3.errVarOk (GF := GF) github_com.mit_pdos.etcd_grove.examples.k8setcd3.errDeleteRejected ∗
      globalAddr github_com.mit_pdos.etcd_grove.examples.k8setcd3.errDeleteRejected ↦□ eD ∗
      validateD reject vf ⊢ validateOk c (rejD eD reject) vf := by
  iintro ⟨#He, #HeD, #Hv⟩
  unfold validateOk
  rw [hc]
  iunfold validateD at Hv
  simp only [driverSpec, driverCodec]
  imodintro
  iintro %ctx %x %o %r %Ψ Ho HΨ
  iapply Hv $$ Ho
  inext
  iintro %err Ho Herr
  iapply HΨ $$ Ho
  unfold rejD
  cases hr : rejects reject o.1.2
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
    github_com.mit_pdos.etcd_grove.examples.k8setcd3.errVarOk (GF := GF) github_com.mit_pdos.etcd_grove.examples.k8setcd3.errUpdateRejected ∗
      globalAddr github_com.mit_pdos.etcd_grove.examples.k8setcd3.errUpdateRejected ↦□ eU ∗
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
  cases hr : rejects inp.Reject' o.1.2
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

end k8setcd3
end EtcdGrove
end Perennial
