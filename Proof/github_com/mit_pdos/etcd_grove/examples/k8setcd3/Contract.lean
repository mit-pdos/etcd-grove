/-
Lean-first (no Rocq counterpart).

# The driver meets the store's contract (stage 6c of `notes/k8s-etcd3-plan.md`)

`driver_contractOk`: the driver's codec, versioner, identity transformer and decoder (the
interface values `codecI`, `versionerI`, `identityI`, `decoderI`, as `Main` passes them to
`etcd3.New`) and `runtime.SetZeroValue` meet `driverSpec` (`contractOk`), from the specs of their
methods (`runtime.Encode`'s through `codec.Encode`'s), given the objects' type facts (`tyOk`, a
premise as the method-set facts of `v3rpc.ServerMethodSets`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.ObjSpec
public import Spec.k8s_io.apimachinery.pkg.runtime.Encode
public import Spec.k8s_io.apimachinery.pkg.runtime.SetZeroValue
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.codec__Encode
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.versioner__UpdateObject
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.versioner__PrepareObjectForStorage
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.versioner__ObjectResourceVersion
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.versioner__ParseResourceVersion
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.identity__TransformFromStorage
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.identity__TransformToStorage
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.decoder__Decode

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s

section defs
variable [ext : FfiSyntax] [go_gctx : GoGlobalContext]

/-- The driver's codec, as `Main` passes it (`codec{}`). -/
def codecI : GoInterface := interface.mkOk github_com.mit_pdos.etcd_grove.examples.k8setcd3.codec.ty #(github_com.mit_pdos.etcd_grove.examples.k8setcd3.codec.mk)
/-- Its versioner (`versioner{}`). -/
def versionerI : GoInterfaceOk := interface.mk github_com.mit_pdos.etcd_grove.examples.k8setcd3.versioner.ty #(github_com.mit_pdos.etcd_grove.examples.k8setcd3.versioner.mk)
/-- Its transformer (`identity{}`). -/
def identityI : GoInterfaceOk := interface.mk github_com.mit_pdos.etcd_grove.examples.k8setcd3.identity.ty #(github_com.mit_pdos.etcd_grove.examples.k8setcd3.identity.mk)
/-- Its decoder (`decoder{}`). -/
def decoderI : GoInterfaceOk := interface.mk github_com.mit_pdos.etcd_grove.examples.k8setcd3.decoder.ty #(github_com.mit_pdos.etcd_grove.examples.k8setcd3.decoder.mk)

end defs

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]
variable [k8s_io.apimachinery.pkg.runtime.Assumptions]

theorem driver_encodeOk (wp_Encode : runtime.Encode.spec (GF := GF) (hG := hG))
    (wp_cEncode : codec.Encode.spec (GF := GF) (hG := hG)) :
    isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.runtime ∗
      isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 ⊢
    encodeOk (driverSpec (GF := GF)) codecI := by
  iintro ⟨#Hrt, #Hpkg⟩
  unfold encodeOk codecI
  simp only [driverSpec, driverCodec]
  imodintro
  iintro %x %o %Φ Hx HΦ
  iunfold objAtD at Hx
  icases Hx with ⟨%p, %n, %Hxp, Hp⟩
  obtain ⟨rfl, hp, hrv⟩ := Hxp
  iapply (wp_Encode (interface.mk github_com.mit_pdos.etcd_grove.examples.k8setcd3.codec.ty
      #(github_com.mit_pdos.etcd_grove.examples.k8setcd3.codec.mk))
      (interface.mkOk (go.GoType.PointerType objTyD) #p)
      (p ↦ github_com.mit_pdos.etcd_grove.examples.k8setcd3.Obj.mk o.1.1 o.1.2 n)
      (p ↦ github_com.mit_pdos.etcd_grove.examples.k8setcd3.Obj.mk o.1.1 o.1.2 n)
      (encodeWith tagV1 o.1.1 o.1.2)) $$ [Hp] [HΦ]
  · iframe Hrt Hp
    iintro %b %Ψ HP Hb HΨ
    dsimp only [interface.mk]
    wp_apply wp_cEncode p (DFrac.own 1) o.1.1 o.1.2 n b [] $$ [$HP $Hb] as ⟨HP, Hb⟩
    iapply HΨ
    iframe HP
    isimp only [List.nil_append] at Hb
    iexact Hb
  inext
  iintro %sl %err ⟨%He, Hsl, Hp⟩
  iapply HΦ $$ [Hp] [Hsl]
  · iunfold objAtD
    iexists p, n
    iframe Hp
    ipureintro; exact ⟨rfl, hp, hrv⟩
  · ileft
    iframe Hsl
    ipureintro; exact He

theorem driver_versionerOk
    (wp_Upd : versioner.UpdateObject.spec (GF := GF) (hG := hG))
    (wp_Prep : versioner.PrepareObjectForStorage.spec (GF := GF) (hG := hG))
    (wp_ORV : versioner.ObjectResourceVersion.spec (GF := GF) (hG := hG))
    (wp_Parse : versioner.ParseResourceVersion.spec (GF := GF) (hG := hG)) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 ⊢
    versionerOk (driverSpec (GF := GF)) versionerI := by
  iintro #Hpkg
  unfold versionerOk versionerI
  simp only [driverSpec, driverCodec]
  isplitl
  · imodintro
    iintro %x %o %rv %Φ Hx HΦ
    iunfold objAtD at Hx
    icases Hx with ⟨%p, %n, %Hxp, Hp⟩
    obtain ⟨rfl, hp, rfl⟩ := Hxp
    wp_apply wp_ORV p (DFrac.own 1) o.1.1 o.1.2 n $$ [$Hp] as Hp
    iapply HΦ $$ [Hp]
    · iunfold objAtD
      iexists p, n
      iframe Hp
      ipureintro; exact ⟨rfl, hp, rfl⟩
    rw [parseRVD_rvStr]
    ipureintro; exact ⟨rfl, rfl⟩
  isplitl
  · imodintro
    iintro %x %o %rv %Φ Hx HΦ
    iunfold objAtD at Hx
    icases Hx with ⟨%p, %n, %Hxp, Hp⟩
    obtain ⟨rfl, hp, rfl⟩ := Hxp
    wp_apply wp_Prep p o.1.1 o.1.2 n $$ [$Hp] as Hp
    iapply HΦ
    isplitl
    · iunfold objAtD
      iexists p, (W64 0)
      iframe Hp
      ipureintro; exact ⟨rfl, hp, rfl⟩
    ipureintro; rfl
  isplitl
  · imodintro
    iintro %x %o %rv %m %Φ Hx HΦ
    iunfold objAtD at Hx
    icases Hx with ⟨%p, %n, %Hxp, Hp⟩
    obtain ⟨rfl, hp, rfl⟩ := Hxp
    wp_apply wp_Upd p o.1.1 o.1.2 n m $$ [$Hp] as Hp
    iapply HΦ
    isplitl
    · iunfold objAtD
      iexists p, m
      iframe Hp
      ipureintro; exact ⟨rfl, hp, rfl⟩
    ipureintro; rfl
  · imodintro
    iintro %str %Φ HΦ
    wp_apply wp_Parse str as %n %err Hr
    iapply HΦ
    cases hp : parseRVD str with
    | none =>
      simp only
      icases Hr with ⟨%h, -⟩
      ipureintro; exact h
    | some m =>
      simp only
      iexact Hr

theorem driver_transformerOk
    (wp_From : identity.TransformFromStorage.spec (GF := GF) (hG := hG))
    (wp_To : identity.TransformToStorage.spec (GF := GF) (hG := hG)) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 ⊢
    transformerOk (driverSpec (GF := GF)) identityI := by
  iintro #Hpkg
  unfold transformerOk identityI
  simp only [driverSpec, driverCodec]
  isplitl
  · imodintro
    iintro %ctx %vsl %v %dctx %Φ #Hv HΦ
    wp_apply wp_From ctx vsl dctx
    iapply HΦ
    iframe Hv
    ipureintro; exact ⟨rfl, rfl⟩
  · imodintro
    iintro %ctx %dsl %d %dctx %Φ #Hd HΦ
    wp_apply wp_To ctx dsl dctx
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists d
    iframe Hd
    ipureintro; rfl

theorem driver_decoderOk (wp_Dec : decoder.Decode.spec (GF := GF) (hG := hG)) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 ⊢
    decoderOk (driverSpec (GF := GF)) decoderI := by
  iintro #Hpkg
  unfold decoderOk decoderI
  imodintro
  iintro %dsl %d %x %o %rv %rev %Φ #Hd Hx HΦ
  simp only [driverSpec, driverCodec] at *
  iunfold objAtD at Hx
  icases Hx with ⟨%p, %n, %Hxp, Hp⟩
  obtain ⟨rfl, hp, rfl⟩ := Hxp
  wp_apply wp_Dec dsl DFrac.discard d p o.1.1 o.1.2 n rev $$ [$Hd $Hp] as %err ⟨-, Hr⟩
  iapply HΦ
  cases hdec : decodeD d with
  | none =>
    rw [decodeObjD_none d hdec]
    icases Hr with ⟨%He, #Hes, Hp⟩
    simp only
    iframe Hes
    isplitr
    · ipureintro; exact He
    iexists o, rvStr n
    iunfold objAtD
    iexists p, n
    iframe Hp
    ipureintro; exact ⟨rfl, hp, rfl⟩
  | some nv =>
    rcases nv with ⟨n', v'⟩
    rw [decodeObjD_of d n' v' hdec]
    simp only
    icases Hr with ⟨%He, Hp⟩
    isplitr
    · ipureintro; exact He
    iunfold objAtD
    iexists p, rev
    iframe Hp
    ipureintro; exact ⟨rfl, hp, rfl⟩

theorem driver_zeroOk (wp_SetZero : runtime.SetZeroValue.spec (GF := GF) (hG := hG)) :
    isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.runtime ⊢
    zeroOk (driverSpec (GF := GF)) := by
  iintro #Hpkg
  unfold zeroOk
  imodintro
  iintro %x %o %rv %Φ Hx HΦ
  simp only [driverSpec] at *
  iunfold objAtD at Hx
  icases Hx with ⟨%p, %n, %Hxp, Hp⟩
  obtain ⟨rfl, hp, -⟩ := Hxp
  wp_apply wp_SetZero objTyD p github_com.mit_pdos.etcd_grove.examples.k8setcd3.Obj _ $$ [$Hp]
    as Hp
  · iframe #
    ipureintro; exact hp
  iapply HΦ
  isplitr
  · ipureintro; rfl
  iunfold objAtD
  iexists p, (W64 0)
  isplitr
  · ipureintro; exact ⟨rfl, hp, rfl⟩
  have hz : (zero_val github_com.mit_pdos.etcd_grove.examples.k8setcd3.Obj) =
      github_com.mit_pdos.etcd_grove.examples.k8setcd3.Obj.mk driverCodec.zero.1.1
        driverCodec.zero.1.2 (W64 0) := rfl
  rw [← hz]
  iexact Hp

/-- **The driver meets the store's contract** (see the file header). -/
theorem driver_contractOk (wp_Encode : runtime.Encode.spec (GF := GF) (hG := hG))
    (wp_cEncode : codec.Encode.spec (GF := GF) (hG := hG))
    (wp_Upd : versioner.UpdateObject.spec (GF := GF) (hG := hG))
    (wp_Prep : versioner.PrepareObjectForStorage.spec (GF := GF) (hG := hG))
    (wp_ORV : versioner.ObjectResourceVersion.spec (GF := GF) (hG := hG))
    (wp_Parse : versioner.ParseResourceVersion.spec (GF := GF) (hG := hG))
    (wp_From : identity.TransformFromStorage.spec (GF := GF) (hG := hG))
    (wp_To : identity.TransformToStorage.spec (GF := GF) (hG := hG))
    (wp_Dec : decoder.Decode.spec (GF := GF) (hG := hG))
    (wp_SetZero : runtime.SetZeroValue.spec (GF := GF) (hG := hG))
    (hty : (driverSpec (GF := GF)).tyOk) :
    isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.runtime ∗
      isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 ⊢
    contractOk (driverSpec (GF := GF)) codecI versionerI identityI decoderI := by
  iintro ⟨#Hrt, #Hpkg⟩
  unfold contractOk
  isplitr
  · ipureintro; exact hty
  isplitr
  · iapply driver_encodeOk wp_Encode wp_cEncode
    iframe Hrt Hpkg
  isplitr
  · iapply driver_versionerOk wp_Upd wp_Prep wp_ORV wp_Parse
    iexact Hpkg
  isplitr
  · iapply driver_transformerOk wp_From wp_To
    iexact Hpkg
  isplitr
  · iapply driver_decoderOk wp_Dec
    iexact Hpkg
  iapply driver_zeroOk wp_SetZero
  iexact Hrt

end proof

end k8setcd3
end EtcdGrove
end Perennial
