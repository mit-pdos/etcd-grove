/-
`runChecks`' writer at the start (`examples/mvccrand/mvccrand.go`): its lessor resources
(`writerLe`, `WriterLease.lean`) from `NewLessor`'s post and the store's. Lean-first (no Rocq
counterpart).

`NewLessor`'s backend contract for the lessor's writes (`lessorApplyOk`) lends the lessor's user
half of `le.b` (`lessorBeOn`) in the write right `R` (here `apply.bkRT` of the tester's backend and
`lessorBeOn` itself), and one write-back token per write (`T := wbTok`); the writer's lease grants
take `Ops` of them. **Placeholder** (`writerLe_beOn_M1`): `writerLe` holds `R` *and* `lessorBeOn`
(for `Revoke`), two copies of the one client half `NewLessor` gives.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.RunChecksWorld
public import Spec.go_etcd_io.etcd.server.v3.lease.NewLessor

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.mvccrand mvcc mvcc.api

section model
variable [GooseExts]

theorem pendItems_start : pendItems mvccStart.log [] = ∅ := by
  rw [pendItems_nil]
  exact GMap.ext (fun _ => rfl)

end model

section writer
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- The lease bucket's part of the tracked buckets' idle half. -/
theorem lease_part (γB : backend.BNames) (r : GMap GoString backend.BktData) :
    backend.rbOwnIn (GF := GF) γB (fun _ => True) r ⊢ backend.rbPart γB (· = leaseName) r := by
  iintro H
  ihave H := backend.rbOwnIn_part γB _ r $$ H
  ihave H := (backend.rbPart_set γB (fun _ => True) (fun n => n = leaseName ∨ n ≠ leaseName) r
    (fun n => by simp only [true_iff]; exact Classical.em _)).1 $$ H
  icases (backend.rbPart_split γB (· = leaseName) (· ≠ leaseName) r
    (fun _ h1 h2 => h2 h1)).1 $$ H with ⟨H, -⟩
  iexact H

/-- A reader slot of the lessor of `γl`, at its pin. -/
theorem lessorRd_of (lp : Loc) (γl : GName) :
    lease.lessorInv (GF := GF) lp γl ∗ lease.lessorRdOf γl ⊢ lease.lessorRd lp γl := by
  iintro ⟨#Hinv, Hrd⟩
  iunfold lease.lessorRdOf at Hrd
  icases Hrd with ⟨%lp', #Hpin, Hrd⟩
  iunfold lease.lessorInv at Hinv
  icases Hinv with ⟨-, #Hpin0, -⟩
  ihave %Heq := lease.lessorPin_agree γl lp lp' $$ [Hpin0 Hpin]
  · iframe Hpin0 Hpin
  subst Heq
  iexact Hrd

/-- **Placeholder: the second copy of the lessor's user half of `le.b`.** `writerLe`
(`WriterLease.lean`) holds the write right `R`, which `lessorApplyOk` requires to lend the lessor's
`lessorBeOn lp B.be` (`rwLens`), and `lessorBeOn lp B.be` itself (`lessor.Revoke.spec` takes it);
`NewLessor` gives one (the other half of `le.b` is the lessor's lock's). -/
theorem writerLe_beOn_M1 (lp be : Loc) : ⊢ lease.lessorBeOn (GF := GF) lp be := by
  sorry -- M1-REPLACE: writerLe needs lessorBeOn twice (in R, lent through lessorApplyOk's rwLens, and for Revoke); NewLessor gives one half

/-- **The writer's lessor resources at the start** (see the file header). -/
theorem writerLe_start (w : Loc) (wv : writer) (γ : RandNames) (γB : backend.BNames) (b : Loc)
    (gx : GName) (lim : w64) (f : GoFunc) (lp : Loc) (rd : GoFunc) (k : Nat)
    (r : GMap GoString backend.BktData) (hle : wv.le' = lease.lessorIface lp) (hf : f ≠ func.nil) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
      lease.lessorInv lp (mvccLeases γ.kv) ∗ lease.lessorCfg lp ∗
      lease.lessorGuard (mvccLeases γ.kv) (fun _ => iprop(True)) ∗ lessorApplyOk lp ∗
      □ backend.isBackend γB (rcP lim) (mvccW gx) iprop(True) b ∗ backend.plHookRO γB f ∗
      lease.lessorRdOf (mvccLeases γ.kv) ∗ lease.leaseRevokers (mvccLeases γ.kv) [] ∗
      backend.rdTok γB (rcP lim) b ∗ backend.bOpen γB backend.rdOpen ∗ lease.lessorBeOn lp b ∗
      ownToks γB.wb k ∗ lease.rdOwn (mvccLeases γ.kv) rd ∗ mvccDeleter rd γ.kv ∗
      backend.rbOwnIn γB (fun _ => True) r ∗ wF go!"nextID" w ↦ (0 : w64) ⊢
    writerLe w wv γ (rcKB γB b gx lim) f [] (0 : w64) k (backend.wbTok γB)
      iprop(apply.bkRT (rcKB γB b gx lim) ∗ lease.lessorBeOn lp b) := by
  iintro ⟨#Hlpkg, #Hlinv, #Hlcfg, #Hguard, #Happly, #Hisb, #Hro, Hlrd, Hrvk, Hrt, Hor, Hbeon,
    Hwb, Hrdo, Hdel, Hrbo, Hnext⟩
  iunfold lessorApplyOk at Happly
  ihave #Hisb' : backend.isBackend (GF := GF) (rcKB γB b gx lim).γB (rcKB γB b gx lim).P (mvccW gx)
      iprop(True) (rcKB γB b gx lim).be $$ []
  · rw [rcKB_P, rcKB_γB, rcKB_be]; iexact Hisb
  ihave #Hro' : backend.plHookRO (GF := GF) (rcKB γB b gx lim).γB f $$ []
  · rw [rcKB_γB]; iexact Hro
  ihave #Hlb := Happly $$ %(rcKB γB b gx lim) %(mvccW gx) %iprop(True) %f
    %(lease.lessorBeOn lp b) Hisb' Hro' %hf []
  · iunfold rwLens
    iintro !> H
    iframe H
    iintro H; iexact H
  ihave Hlrd := lessorRd_of lp (mvccLeases γ.kv) $$ [Hlrd]
  · iframe Hlinv Hlrd
  ihave Hbe2 := writerLe_beOn_M1 (GF := GF) lp b
  iunfold writerLe
  iexists lp, rd, r
  isplitr
  · iunfold writerLeRO
    iframe Hlpkg Hlinv Hlcfg Hguard
    isplitr
    · ipureintro; exact hle
    rw [rcKB_γB, show leaseName = go!"lease" from rfl]
    iexact Hlb
  iframe Hlrd Hrvk Hrdo Hdel Hnext
  isplitl [Hrt Hor Hbeon]
  · iunfold apply.bkRT
    rw [rcKB_γB, rcKB_P, rcKB_be]
    iframe Hrt Hor Hbeon
  isplitl [Hwb]
  · iapply wbToks_list γB k $$ Hwb
  iframe Hbe2
  isplitl [Hrbo]
  · iapply lease_part γB r $$ Hrbo
  ipureintro
  refine ⟨rcP_lease lim, by decide, fun id h => by simp at h⟩

end writer

end mvccrand
end EtcdGrove
end Perennial
