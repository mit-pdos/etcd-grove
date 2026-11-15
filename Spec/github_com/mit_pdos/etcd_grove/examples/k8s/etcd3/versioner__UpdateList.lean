/- Lean-first (no Rocq counterpart).

`versioner{}.UpdateList(obj, resourceVersion, continueValue, remainingItemCount)` (k8setcd3.go) on
an `*ObjList`: the list's metadata becomes the arguments, its items unchanged. Proved (stage 7e-2,
`notes/k8s-7e-2-draft.md` §6).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ListSpecD

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI k8s

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev versioner.UpdateList.spec : Prop :=
  ∀ (pl : Loc) (os : List (DObj × GoString)) (rv rv' : w64) (cont cont' : GoString) (rem : Loc)
    (remV rem0 : Option w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗
      (driverListSpec (GF := GF)).listAtItems pl os rv cont rem0 ∗ remIs rem remV }}
    (App (App (App (App (Val #(methods github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.versioner.ty
      go!"UpdateList" #(github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.versioner.mk)))
      (Val #(interface.mkOk (go.GoType.PointerType
        github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList.ty) #pl : GoInterface)))
      (Val #rv')) (Val #cont')) (Val #rem))
  {{ RET #GoInterface.nil; (driverListSpec (GF := GF)).listAtItems pl os rv' cont' remV }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
