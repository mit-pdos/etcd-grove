/-
**The typed clients' lemmas**: a resource's strategy functions as the server's operations take
them (`prepareOk`, `mutateOk`, `graceOk`, from the functions' specs), and the resource of an
object a write returns. Lean-first.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.WriteLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apimodel

open Iris Iris.BI Iris.ProofMode

section pure
variable [FfiSyntax]

theorem createApply_res (r : Res) (ns : GoString) (o : Obj) (σ : St)
    (t : k8s_io.apimachinery.pkg.apis.«meta».v1.Time) : (createApply r ns o σ t).1.res = o.res := by
  unfold createApply
  simp only [Obj.res_modMeta, prepareD_res, createNs_res]

/-- A create's object is the request's resource. -/
theorem CreateOut_ok_res {cfgFail admin : Bool} {r : Res} {ns : GoString} {o : Obj} {σ σ' : St}
    {w : Bool} {o' : Obj} (h : CreateOut cfgFail admin r ns o σ (.ok (w, o')) σ') : o'.res = o.res := by
  rcases h with ⟨-, h, -⟩ | ⟨e, -, h, -⟩ | ⟨-, t, -, h⟩
  · cases h
  · cases h
  · cases h; exact createApply_res r ns o σ t

theorem updateApply_res (r : Res) (st obj : Obj) (σ : St) : (updateApply r st obj σ).1.res = obj.res := by
  unfold updateApply
  simp only [Obj.res_modMeta]

/-- An update's object is the table's resource, if the mutation's are. -/
theorem UpdateOut_ok_res {cfgFail admin : Bool} {r : Res} {ns : GoString} {o : Obj}
    {mutR : Obj → Obj → Option Obj → Prop} {σ σ' : St} {w : Bool} {o' : Obj} (hwf : σ.wf)
    (hmut : ∀ st o'', mutR st o (some o'') → o''.res = r)
    (h : UpdateOut cfgFail admin r ns o mutR σ (.ok (w, o')) σ') : o'.res = r := by
  rcases h with ⟨-, h, -⟩ | ⟨e, -, h, -⟩ | ⟨-, st, hst, ⟨-, h, -⟩ | ⟨obj, hm, -, h⟩⟩
  · cases h
  · cases h
  · cases h; exact (wf_stored hwf hst).1
  · cases h; rw [updateApply_res]; exact hmut st obj hm

theorem dsStatusMut_res {st o o'' : Obj} (h : dsStatusMut st o (some o'')) :
    o''.res = .daemonSets := by
  cases st <;> cases o <;> simp [dsStatusMut] at h
  subst h; rfl

theorem replaceMut_res {st o o'' : Obj} (h : replaceMut st o (some o'')) : o'' = o := by
  unfold replaceMut at h
  cases h; rfl

end pure

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A create strategy's spec as `create` takes it. -/
theorem prepareOk_of (r : Res) (f : GoFunc)
    (h : ∀ (x : GoInterface) (o : Obj),
      {{ (objAt (GF := GF) x (DFrac.own 1) o) ∗ ⌜o.res = r⌝ }} (App (Val #f) (Val #x))
      {{ RET #(); objAt x (DFrac.own 1) (prepareD o) }}) :
    ⊢ prepareOk (GF := GF) r f := by
  unfold prepareOk
  iintro %x %o %hr
  imodintro
  iintro %Φ Hx HΦ
  wp_apply (h x o) $$ [$Hx] as Hx
  · ipureintro; exact hr
  iapply HΦ
  iexact Hx

/-- An update's mutation's spec as `update` takes it. -/
theorem mutateOk_of (r : Res) (mutR : Obj → Obj → Option Obj → Prop) (f : GoFunc)
    (h : ∀ (x y : GoInterface) (st req : Obj),
      {{ (objAt (GF := GF) x (DFrac.own 1) st) ∗ objAt y (DFrac.own 1) req ∗ ⌜st.res = r ∧ req.res = r⌝ }}
        (App (App (Val #f) (Val #x)) (Val #y))
      {{ (z : GoInterface), RET #z; (⌜z = interface.nil ∧ mutR st req none⌝) ∨
          (∃ o, ⌜mutR st req (some o) ∧ o.res = r⌝ ∗ objAt z (DFrac.own 1) o) }}) :
    ⊢ mutateOk (GF := GF) r mutR f := by
  unfold mutateOk
  iintro %x %y %st %req %hr
  imodintro
  iintro %Φ ⟨Hx, Hy⟩ HΦ
  wp_apply (h x y st req) $$ [$Hx $Hy] as %z Hz
  · ipureintro; exact hr
  iapply HΦ
  iexact Hz

/-- Pod's grace function's spec as `remove` takes it. -/
theorem graceOk_pods (f : GoFunc)
    (h : ∀ (x : GoInterface) (d : kd.core.Pod) (opts : k8s_io.apimachinery.pkg.apis.«meta».v1.DeleteOptions)
      (dq : DFrac) (dop : kd.meta.DeleteOptions),
      {{ (objAt (GF := GF) x (DFrac.own 1) (.pod d)) ∗ kd.meta.DeleteOptions.own opts dq dop }}
        (App (App (Val #f) (Val #x)) (Val #opts))
      {{ RET #(podGraceD d dop.GracePeriodSeconds'); objAt x (DFrac.own 1) (.pod d) ∗
          kd.meta.DeleteOptions.own opts dq dop }}) :
    ⊢ graceOk (GF := GF) .pods f := by
  unfold graceOk
  iintro %x %st %opts %dq %dop %hr
  cases st with
  | pod d =>
    imodintro
    iintro %Φ ⟨Hx, Ho⟩ HΦ
    wp_apply (h x d opts dq dop) $$ [$Hx $Ho] as ⟨Hx, Ho⟩
    rw [show graceOf Res.pods (Obj.pod d) dop.GracePeriodSeconds' = podGraceD d dop.GracePeriodSeconds' from rfl]
    iapply HΦ
    iframe
  | node d => simp [Obj.res] at hr
  | ds d => simp [Obj.res] at hr
  | cr d => simp [Obj.res] at hr

/-- A grace function of 0 (`noGrace`) as `remove` takes it, for a resource without one. -/
theorem graceOk_zero (r : Res) (hr : r ≠ .pods) (f : GoFunc)
    (h : ∀ (o : GoInterface) (opts : k8s_io.apimachinery.pkg.apis.«meta».v1.DeleteOptions),
      {{ (True : IProp GF) }} (App (App (Val #f) (Val #o)) (Val #opts)) {{ RET #(W64 0); True }}) :
    ⊢ graceOk (GF := GF) r f := by
  unfold graceOk
  iintro %x %st %opts %dq %dop %hres
  imodintro
  iintro %Φ ⟨Hx, Ho⟩ HΦ
  wp_apply (h x opts)
  have hg : graceOf r st dop.GracePeriodSeconds' = W64 0 := by
    cases r <;> cases st <;> first | rfl | exact absurd rfl hr
  rw [hg]
  iapply HΦ
  iframe

end lemmas

end apimodel
end EtcdGrove
end Perennial
