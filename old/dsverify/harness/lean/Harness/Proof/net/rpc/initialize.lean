/-
The proof of `Spec/net/rpc/initialize.lean`.
-/
module

public import Harness.Spec.net.rpc.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions] [net.rpc.RpcKit]

set_option goose.wp.extras true in
theorem net.rpc.initialize'.wp_proof
    (wp_http_initialize : net.http.initialize'.spec (GF := GF) (hG := hG))
    (wp_sync_initialize : sync.initialize'.spec (GF := GF) (hG := hG))
    (wp_net_initialize : net.initialize'.spec (GF := GF) (hG := hG))
    (wp_errors_initialize : errors.initialize'.spec (GF := GF) (hG := hG)) :
    net.rpc.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := GoInterface) net.rpc.errFrame go.error as HeF
  wp_apply wp_GlobalAlloc (V := Loc) net.rpc.DefaultServer
    (go.GoType.PointerType net.rpc.Server.ty) as HDS
  wp_apply wp_GlobalAlloc (V := Loc) net.rpc.codec
    (go.GoType.PointerType net.rpc.Codec.ty) as Hcodec
  wp_apply wp_GlobalAlloc (V := sync.Mutex) net.rpc.codecMu sync.Mutex.ty as HcodecMu
  wp_apply wp_GlobalAlloc (V := GoInterface) net.rpc.errHTTP go.error as HeH
  wp_apply wp_GlobalAlloc (V := GoInterface) net.rpc.ErrShutdown go.error as HeS
  wp_apply wp_http_initialize _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #Hhttp⟩
  wp_apply wp_sync_initialize _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #Hsync⟩
  wp_apply wp_net_initialize _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hnet⟩
  wp_apply wp_errors_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Herrors⟩
  iapply wp_fupd
  wp_apply errors.wp_New_errorString as %xS #ES
  wp_apply errors.wp_New_errorString as %xH #EH
  wp_func_call
  wp_call
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface) go.string
    (go.GoType.InterfaceType [])) as %mp Hmp
  wp_apply errors.wp_New_errorString as %xF #EF
  irename «$r0» => Hs
  generalize «$r0_ptr» = s at *
  iStructNamed Hs
  imod ghost_map_alloc_strong_empty (K := GoString) (V := GoInterface) (GF := GF)
    (fun _ => True) PredInfinite.true with ⟨%γ, -, Hγ⟩
  imod sync.init_Mutex (net.rpc.servicesInv mp γ) ⊤
      (structFieldRef net.rpc.Server go!"mu" s) $$ [mu] [Hmp Hγ] with #Hmu
  · iexact mu
  · inext; unfold net.rpc.servicesInv; iexists ∅; iframe Hmp Hγ
  imod sync.init_Mutex net.rpc.codecInv ⊤ (globalAddr net.rpc.codecMu) $$ [HcodecMu] [Hcodec]
    with #HcMu
  · iexact HcodecMu
  · inext; unfold net.rpc.codecInv; ileft; iexact Hcodec
  ipersist HDS
  ipersist HeS
  ipersist HeH
  ipersist HeF
  ipersist services
  imodintro
  isplitr
  · ipureintro; exact isPanic_intoVal ()
  iframe Hown
  is_pkg_init_finish
  imodintro
  unfold net.rpc.isInit errors.newVar
  isplitl
  · iexists xS
    iframe HeS ES
  isplitl
  · iexists xH
    iframe HeH EH
  isplitl
  · iexists xF
    iframe HeF EF
  isplitl
  · iexact HcMu
  isplitl
  · iexists s
    iframe HDS
    unfold net.rpc.isServer net.rpc.isServerG
    iexists γ, mp
    iframe services Hmu
  itrivial

end proof

end Perennial
