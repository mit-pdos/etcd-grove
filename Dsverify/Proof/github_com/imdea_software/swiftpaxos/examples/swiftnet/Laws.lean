/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/Laws.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The configuration's and the membership's writer laws as intended (HUB-REQUEST 1,
notes/hub-requests.md): `Base.lean`'s `confIs_write` and `memIs_write` parse as
`(|==> confIs γc c) ∗ monoListAuthOwn γc 1 [c]` (`|==>` binds tighter than `∗`), which is false;
these are the statements with the update over both conjuncts.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.Base

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section laws
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF]

theorem confIs_write' (γc : GName) (c : Conf) :
    ⌜c.valid⌝ ∗ monoListAuthOwn (A := Conf) γc 1 [] ⊢
      |==> (confIs γc c ∗ monoListAuthOwn (A := Conf) γc 1 [c]) := by
  iintro ⟨%Hv, H⟩
  imod monoListAuthOwn_update (γ := γc) [c] List.nil_prefix $$ H with ⟨Ha, #Hlb⟩
  imodintro
  unfold confIs
  iframe Ha Hlb
  ipureintro; exact Hv

theorem memIs_write' (γm : GName) (l : List GoString) :
    ⌜l.Nodup ∧ ∀ a ∈ l, a ∈ replicaAddrs⌝ ∗ monoListAuthOwn (A := List GoString) γm 1 [] ⊢
      |==> (memIs γm l ∗ monoListAuthOwn (A := List GoString) γm 1 [l]) := by
  iintro ⟨%Hv, H⟩
  imod monoListAuthOwn_update (γ := γm) [l] List.nil_prefix $$ H with ⟨Ha, #Hlb⟩
  imodintro
  unfold memIs
  iframe Ha Hlb
  ipureintro; exact Hv

end laws

end Perennial.github_com.imdea_software.swiftpaxos
