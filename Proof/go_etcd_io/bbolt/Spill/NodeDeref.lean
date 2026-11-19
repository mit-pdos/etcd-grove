/-
`node.dereference` (U9b, `notes/bbolt-proof-plan.md`; unit-internal, stated and proved here):
`n.dereference()` on a live node `n` of the bucket `bl` copies its key and every inode's key and
value to fresh heap slices (`nodeDerefd`), then dereferences its children: afterwards the nodes
below `n` hold no view slice (`covered`), and nothing but node records changed (`derefStep`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.DerefHeap
public import Proof.go_etcd_io.bbolt.Spill.DerefCopy
public import Proof.go_etcd_io.bbolt.Rebalance.Objs
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Key
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Value
public import Spec.go_etcd_io.bbolt.internal.common.Inode__SetKey
public import Spec.go_etcd_io.bbolt.internal.common.Inode__SetValue
public import Spec.go_etcd_io.bbolt.internal.common.Assert
public import Spec.go_etcd_io.bbolt.TxStats__IncNodeDeref
public import Proof.go_etcd_io.bbolt.Spill.NodeDerefDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem node.dereference.wp_proof (hK : internal.common.Inode.Key.spec (GF := GF) (hG := hG))
    (hV : internal.common.Inode.Value.spec (GF := GF) (hG := hG))
    (hSK : internal.common.Inode.SetKey.spec (GF := GF) (hG := hG))
    (hSV : internal.common.Inode.SetValue.spec (GF := GF) (hG := hG))
    (hA : internal.common.Assert.spec (GF := GF) (hG := hG))
    (hInc : TxStats.IncNodeDeref.spec (GF := GF) (hG := hG)) :
    node.dereference.spec (GF := GF) (hG := hG) := by
  intro K tx r m X bl n B HB Hn Hl Hpre Hfresh
  have Hp : X.t.bs !! bl = some B ∧ (B.ns !! n).isSome ∧ n ∈ X.live ∧ derefPre X ∧
    liveFresh X := ⟨HB, Hn, Hl, Hpre, Hfresh⟩
  iintro %Φ Hw HΦ
  iapply (node.dereference.wp_aux hK hV hSK hSV hA hInc) $$ %K %tx %r %m %X %bl %n %B %Hp Hw
  inext
  iintro %X' HX'
  iapply HΦ
  iexists X'
  iexact HX'

end proof

end bbolt
end EtcdGrove
end Perennial
