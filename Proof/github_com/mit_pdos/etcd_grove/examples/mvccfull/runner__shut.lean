/- Lean-first (no Rocq counterpart). The proof of `runner.shut`: proved.

The outline: `KV.Close.contract` (`mvccClosed`), `check`; `inc_census`; `lessor.Stop`;
`backend.Close.spec` (`commitReq` of `True`; at `dbCloseOk` the `nil` arm, its file `bFile`'s path
agreeing with `bkKeep`'s), `check`; `inc_stop_image`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__shut
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.check
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Stop
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__Close
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Writer

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem runner.shut.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hCR : mvcc.api.mvccClosed_rest.law (GF := GF))
    (hstop : mvccImage_stop.law (GF := GF))
    (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_Stop : lease.lessor.Stop.spec (GF := GF) (hG := hG))
    (wp_bClose : backend.backend.Close.spec (GF := GF) (hG := hG)) :
    runner.shut.spec (GF := GF) (hG := hG) := by
  intro x ks cfg wr h γh mp path bk lp kv γk σ L r k hdbc hσ hr
  haveI := hpers.1
  wp_start as ⟨#Hctx, Hkv, Hle, Hbe, #Hmv, Hopen, Hrdrs, Hmb, Hσ, Hbk, Hstop, Hrb⟩
  iunfold writerCtx at Hctx
  icases Hctx with ⟨#Hrn, -, -, -, #Hpb, -, #Hpl, -⟩
  iunfold rnCtx at Hrn
  icases Hrn with ⟨#Hpkg, #Hpm, -⟩
  ihave %Hkvs := hsh.1 kv γk $$ Hmv
  obtain ⟨kty, kvv, hkveq, hK⟩ := Hkvs
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hKClose⟩ := hK
  subst hkveq
  wp_auto
  wp_apply (hKClose γk) $$ [Hopen] as Hcl
  · iframe #; iframe
  (try wp_auto)
  wp_apply wp_check
  · ipureintro; simp
  (try wp_auto)
  imod inc_census hCR γk bk path k $$ [Hcl Hrdrs Hmb Hbk] with ⟨Hmb, Hone, #Hisb, #Hsc, Hbf⟩
  · iframe
  wp_apply (wp_Stop lp) $$ [Hstop]
  · iframe #; iframe
  (try wp_auto)
  ihave #Hreq : backend.commitReq bk.γB bk.P iprop(True) bk.be iprop(True) iprop(True) $$ []
  · iapply backend.commitReq_true
  wp_apply (wp_bClose bk.γB bk.P (mvccW bk.gx) iprop(True) bk.be iprop(True) iprop(True))
    $$ [Hone] as %err ⟨-, %D, Hsv, Hocl⟩
  · iframe #; iframe
  icases Hocl with (⟨%Herr, %path', Hbf', Hfile⟩ | %Hbad)
  rotate_left
  · exact absurd hdbc Hbad
  subst Herr
  ihave %Hp := backend.bFile_agree bk.γB path path' $$ [Hbf Hbf']
  · iframe
  subst Hp
  imod inc_stop_image hstop (interface.mkOk kty kvv) γk bk D σ r L hσ hr
    $$ [Hmb Hsv Hσ Hrb] with ⟨%u, Himg, %HrD⟩
  · iframe #; iframe
  (try wp_auto)
  wp_apply wp_check
  · ipureintro; simp
  (try wp_auto)
  iapply HΦ
  iframe Hkv Hle Hbe
  iexists D, u
  iframe
  ipureintro; exact HrD

end proof

end mvccfull
end EtcdGrove
end Perennial
