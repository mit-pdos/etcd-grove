/-
`(*Replica).newInstance`, `(*Replica).newInstanceDefault`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.EpBase
public import Perennial.Proof.time.Results

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model epaxosProof

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [GooseExts]

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : TreemapHyp GF]

theorem wp_newInstance (r : Loc) (q n : w32) (cmds : GoSlice) (cb lb' : w32) (st : w8) (seq : w32)
    (deps : GoSlice) :
    {{ pkgInit_epaxos (GF := GF) }}
      (App (App (App (App (App (App (App (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty
        @!! go!"newInstance")) (Val #q)) (Val #n)) (Val #cmds)) (Val #cb)) (Val #lb')) (Val #st))
        (Val #seq)) (Val #deps))
    {{ (p : Loc), RET #p; ⌜p ≠ null⌝ ∗ ∃ (t : w64) (idp : Loc),
        p ↦ epaxos.Instance.mk cmds cb lb' st seq deps null (W64 0) (W64 0) interface.nil t idp ∗
        idp ↦ epaxos.instanceId.mk q n }} := by
  wp_start
  wp_auto
  wp_apply time.wp_Now as %t -
  wp_apply time.Time.wp_UnixNano' as %ns -
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ «$r0»
  iapply HΦ
  iframe «$r0» «$v11»
  ipureintro; exact Hnn

theorem wp_newInstanceDefault (r : Loc) (q n : w32) :
    {{ pkgInit_epaxos (GF := GF) }}
      (App (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"newInstanceDefault"))
        (Val #q)) (Val #n))
    {{ (p : Loc), RET #p; ⌜p ≠ null⌝ ∗ ∃ (t : w64) (idp : Loc),
        p ↦ epaxos.Instance.mk slice.nil (W32 (-1)) (W32 (-1)) stNONE (W32 (-1)) slice.nil null
          (W64 0) (W64 0) interface.nil t idp ∗
        idp ↦ epaxos.instanceId.mk q n }} := by
  wp_start
  wp_auto
  wp_apply wp_newInstance as %p Hp
  iapply HΦ
  unfold stNONE; iexact Hp

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
