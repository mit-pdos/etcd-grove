/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/read/isStopped.lean`. Lean-first (no Rocq
counterpart); the request path's unit 4a.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.read.isStopped
public import Spec.errors.Is

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.read

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.read.Assumptions]

/-- `errors.Is(err, g)` of an `applyErrIs` error at the `errors.New` variable `g`. -/
theorem read_wp_Is_var (hIs : errors.Is.spec (GF := GF) (hG := hG)) (err : GoInterface)
    (e : GoInterfaceOk) (hl : errLeaf e) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ applyErrIs err }}
      (App (App (Val (@! _root_.Perennial.errors.Is)) (Val #err)) (Val #(GoInterface.ok e)))
    {{ (b : Bool), RET #b; True }} := by
  iintro %Φ ⟨#Hp, #Herr⟩ HΦ
  ihave #HT := applyErrIs_tree err $$ Herr
  ihave ⟨%S, %M, #Htree, %HS⟩ := HT $$ %(GoInterface.ok e)
  have hpt : ptrTarget (GoInterface.ok e) := fun tii h => by cases h; exact hl.1
  iapply hIs S M err (GoInterface.ok e) hpt (HS.2 hpt) $$ [] HΦ
  iframe #; ipureintro; exact HS.1

theorem read.isStopped.wp_proof (hIs : errors.Is.spec (GF := GF) (hG := hG)) :
    read.isStopped.spec (GF := GF) (hG := hG) := by
  intro err
  wp_start as #Herr
  ihave Hinit : (go_etcd_io.etcd.server.v3.etcdserver.read.readInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, -, -, #HS, -, -, #HR, -, -⟩
  iunfold errVarLeaf at HS HR
  icases HS with ⟨%eS, #HeS, %HlS, -⟩
  icases HR with ⟨%eR, #HeR, %HlR, -⟩
  ihave #Perr : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  wp_auto
  wp_apply read_wp_Is_var hIs err eR HlR as %b1 -
  · iframe #
  cases b1
  · wp_auto
    wp_apply read_wp_Is_var hIs err eS HlS as %b2 -
    · iframe #
    wp_end
  · wp_end

end proof

end EtcdGrove
end Perennial
