/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/pbutil/MustUnmarshalMessagePb.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.pbutil.MustUnmarshalMessagePb
public import Spec.google_golang_org.protobuf.proto.UnmarshalPb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.pbutil.Assumptions]

theorem pbutil.MustUnmarshalMessagePb.wp_proof
    (wp_Unmarshal : proto.UnmarshalPb.spec (GF := GF) (hG := hG)) :
    pbutil.MustUnmarshalMessagePb.spec (GF := GF) (hG := hG) := by
  intro T hreg l d bs dq c₀ hm hu hdo hbs
  wp_start as ⟨Hd, Hb⟩
  wp_auto
  wp_apply wp_Unmarshal T hreg d bs dq l $$ [$Hd $Hb] as %err ⟨Hd, %Hok, Hdec⟩
  have he : err = GoInterface.nil := Hok ⟨c₀, hm, hu, hbs⟩
  subst he
  wp_auto
  ihave ⟨%c, Hm, %Hc⟩ := Hdec $$ %rfl
  obtain ⟨-, -, -, Heq⟩ := Hc
  rw [Heq c₀ hm hu hbs]
  iapply HΦ
  iframe
  iapply T.data.decC_dec l c₀ hdo
  iexact Hm

end proof

end EtcdGrove
end Perennial
