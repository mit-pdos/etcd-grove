/- Lean-first (no Rocq counterpart). The proof of `stream.recvOne`: Draft, to come (`sorry`).

The callees in call order: `Chan` (through `shapes.law`), the channel's receives
(`wsChan_recv.law`, the poll's bound from a registration's `wsSentLb` or `wsSentLb_zero.law`),
`receive`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.stream__recvOne
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.stream__receive
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.StreamLemmas

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

theorem stream.recvOne.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hrecv : mvcc.api.wsChan_recv.law (GF := GF) (hG := hG))
    (hzero : mvcc.api.wsSentLb_zero.law (GF := GF) (hG := hG))
    (wp_stream_receive : stream.receive.spec (GF := GF) (hG := hG)) :
    stream.recvOne.spec (GF := GF) (hG := hG) := by
  intro T q rs
  haveI : ∀ ws γ ι, Persistent (isMvccWatchStream (GF := GF) ws γ ι) := hpers.2.1
  haveI : ∀ ι n, Persistent (wsSentLb (GF := GF) ι n) := hpers.2.2.1
  wp_start as ⟨Hctx, Hrcv⟩
  iunfold streamCtx at Hctx
  icases Hctx with ⟨Hep, #Fx, #Fm, #Fkv, #Fws, #Fwm, #Hws, #Hinv, #Hmu, Hstop⟩
  iunfold rcvOwn at Hrcv
  icases Hrcv with ⟨Hrd, Hhr, Hwr, Hhalf⟩
  iunfold epCtx at Hep
  icases Hep with ⟨Hrn, Hinc, Hregs⟩
  iunfold rnCtx at Hrn
  icases Hrn with ⟨#Hpkg, #Hmpkg, Hrn⟩
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HL⟩
  iunfold smuInv at HL
  icases HL with ⟨%rs0, %W, %Hl, %P, HB⟩
  iunfold smuBody at HB
  icases HB with ⟨Hwm, ⟨%osl, %ids, Hord, Hids, Hcap, %Hids⟩, Hevl, Hreg, Hrcv0, #Hlb, %Hknown, Hwats⟩
  ihave %Hrs := ghostVar_agree T.σs.rcv _ _ _ _ $$ Hrcv0 Hhalf
  subst Hrs
  icases regs_sentLb hpers hzero Hl rs0 T.σs.ws W $$ Hwats with ⟨Hwats, %n, #Hn, %Hkn⟩
  ihave %Hsh := hsh.2.2.2 T.ws T.ep.ι.kv T.σs.ws $$ Hws
  obtain ⟨wsty, wsv, hws, -, hCh, -, -, -, -, -⟩ := Hsh
  icases hrecv T.ws T.ep.ι.kv T.σs.ws $$ Hws with ⟨#Hch, #Hrecvb, #Hpoll⟩
  rw [hws]
  (try wp_auto)
  sorry

end proof

end mvccfull
end EtcdGrove
end Perennial
