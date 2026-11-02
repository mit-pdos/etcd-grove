/-
The shape of the errors bbolt compares (`err == berrors.ErrMaxSizeReached` in
`db.allocate`): comparing two interfaces of one pointer type compares their pointers, which
needs the values to be locations (`errWF`; Go's are, a pointer-typed interface holding a
pointer). `errors.New` and `fmt.Errorf` return pointers (`wp_New_ptr`, `wp_Errorf_ptr`:
Perennial's specs with that said); a `syscall.Errno` is no pointer.
-/
module

public import Proof.go_etcd_io.bbolt.Init
public import Perennial.Proof.fmt
public import Proof.os.ErrWF

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode

section shape
variable [ext : FfiSyntax] [go_gctx : GoGlobalContext]

theorem errWF_newErr (e : GoInterface) (h : IsNewErr e) : errWF e := by
  obtain ⟨t, l, rfl⟩ := h; exact errWF_ptr t l

end shape

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `errors.New(msg)` returns a pointer (`errors.wp_New`, with its shape). -/
theorem wp_New_ptr [package_sem : errors.Assumptions] (msg : GoString) :
    {{ (True : IProp GF) }}
      (App (Val (@! errors.New)) (Val #msg))
    {{ (err : GoInterfaceOk), RET #(interface.ok err);
        ⌜IsNewErr (interface.ok err)⌝ ∗
        □ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
          WP (App (Val #(methods err.ty go!"Error" err.v)) (Val #())) {{ Φ }} }} := by
  wp_start
  wp_auto
  wp_alloc x as Hx
  iStructNamed Hx
  ipersist s
  wp_auto
  iapply HΦ
  isplitr
  · ipureintro; exact ⟨_, x, rfl⟩
  imodintro
  iintro %Φ HΦ
  dsimp only
  rw [method_unfold]
  wp_auto
  iexact HΦ

/-- `fmt.Errorf(format, args...)` returns a pointer (`fmt.wp_Errorf`, with its shape). -/
theorem wp_Errorf_ptr [package_sem : fmt.Assumptions] (format : GoString) (args_sl : GoSlice)
    (args : List GoAny) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦* args }}
      (App (App (Val (@! fmt.Errorf)) (Val #format)) (Val #args_sl))
    {{ (err : GoInterfaceOk), RET #(interface.ok err); ⌜IsNewErr (interface.ok err)⌝ }} := by
  wp_start as _
  wp_apply wp_New_ptr as %err ⟨%Hp, -⟩
  iapply HΦ
  ipureintro; exact Hp

end wps

end bbolt
end EtcdGrove
end Perennial
