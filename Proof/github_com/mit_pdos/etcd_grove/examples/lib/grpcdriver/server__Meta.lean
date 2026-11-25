/- Lean-first (no Rocq counterpart).

# `(*server).Meta`'s proof

No incoming metadata: `""`, the join of no values. Otherwise `md.Get("x-driver")` is the slice the
map holds at the key (`x-driver` is lower case), or `nil`: `md`'s values at it, or none; joined, below
`stringValueMax` by `metaSpec`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.server__Meta
public import Spec.google_golang_org.grpc.metadata.FromIncomingContext
public import Spec.google_golang_org.grpc.metadata.MD__Get
public import Spec.google_golang_org.protobuf.types.known.wrapperspb.String
public import Perennial.Spec.strings.Join
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode EtcdGrove

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

theorem server.Meta.wp_proof
    (wp_FromIncoming : EtcdGrove.metadata.FromIncomingContext.spec (GF := GF) (hG := hG))
    (wp_MDGet : EtcdGrove.metadata.MD.Get.spec (GF := GF) (hG := hG))
    (wp_Join : strings.Join.spec (GF := GF) (hG := hG))
    (wp_String : google_golang_org.protobuf.types.known.wrapperspb.String.spec (GF := GF) (hG := hG)) :
    server.Meta.spec (GF := GF) (hG := hG) := by
  intro s ctx r v md Φ Ψe
  wp_start as ⟨Hrecv, #Hin, HΨ⟩
  ihave #Hmeta : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.metadata $$ []
  · iPkgInit
  ihave #Hstr : isPkgInit (PROP := IProp GF) pkg_id.strings $$ []
  · iPkgInit
  isimp only [metaSpec] at HΨ
  icases HΨ with ⟨%Hbound, HΦ'⟩
  wp_auto
  wp_apply (wp_FromIncoming ctx md) $$ [$Hmeta $Hin] as %mp %ok Hres
  icases Hres with (%Hno | ⟨%md0, %m, %Hc, Hm, Hsls⟩)
  · obtain ⟨rfl, rfl⟩ := Hno
    wp_auto
    wp_apply wp_String go!"" (by decide) as %l Hl
    wp_auto
    have he : (go!",".intercalate (metadata.mdVals none mdKeyS)) = go!"" := rfl
    rw [he]
    iapply HΦ
    isplitr
    · ipureintro; rfl
    iframe
  obtain ⟨rfl, rfl, Hiff⟩ := Hc
  irename : (md_ptr ↦ mp : IProp GF) => Hmdp
  ipersist Hmdp
  ipersist Hm
  wp_auto
  wp_apply wp_MDGet md_ptr mp m mdKeyS $$ [] as %sl %Hsl
  · iframe #
  obtain ⟨rk, Hrk, Hsl⟩ := Hsl
  have hrk : rk = mdKeyS := (Hrk mdKeyS (by decide)).2 (by decide)
  subst hrk
  have hlt : ∀ xs : List GoString, (go!",".intercalate xs).length < stringValueMax →
      (go!",".intercalate xs).length < 2 ^ 61 :=
    fun xs h => Nat.lt_trans h (by decide)
  rcases Hsl with ⟨rfl, hnone⟩ | hsome
  · have hmd : metadata.mdVals (some md0) mdKeyS = [] := by
      have : md0 mdKeyS = none := (Hiff mdKeyS).1 hnone
      simp [metadata.mdVals, this]
    rw [hmd] at Hbound ⊢
    wp_apply wp_Join slice.nil ([] : List GoString) (DFrac.own 1) go!"," $$ [] as -
    · isplitr
      · iexact Hstr
      isplitr
      · iapply ownSlice_nil
      ipureintro; exact hlt _ Hbound
    wp_auto
    wp_apply wp_String _ Hbound as %l Hl
    wp_auto
    iapply HΦ
    isplitr
    · ipureintro; rfl
    iframe
  · ihave ⟨⟨%vs, Hvs, %Hne, %Hmd0⟩, -⟩ :=
      (BigSepM.bigSepM_lookup_acc (Φ := fun (k : GoString) (sl : GoSlice) =>
        iprop(∃ vs : List GoString, sl ↦* vs ∗ ⌜vs ≠ []⌝ ∗ ⌜md0 k = some vs⌝)) hsome).1 $$ Hsls
    have hmd : metadata.mdVals (some md0) mdKeyS = vs := by
      simp [metadata.mdVals, Hmd0]
    rw [hmd] at Hbound ⊢
    wp_apply wp_Join sl vs (DFrac.own 1) go!"," $$ [Hvs] as -
    · isplitr
      · iexact Hstr
      iframe
      ipureintro; exact hlt _ Hbound
    wp_auto
    wp_apply wp_String _ Hbound as %l Hl
    wp_auto
    iapply HΦ
    isplitr
    · ipureintro; rfl
    iframe

end proof

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial
