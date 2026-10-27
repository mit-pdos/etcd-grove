/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/common/Serve.lean` (2026-10-22, D33).
Lean-first (no Rocq counterpart).

The steps (the examples' `Main`s' after `Start`): `v3rpc.Server(s, nil, nil, opt)` (its `grpcCfgOk`
from the started server's views, `grpcCfgOk_of_started_w`, which also gives 64 of the watchable
store's readers; `opt` the keepalive policy, a neutral option, D28, as linkv3p's `startMember`);
`net.Listen("tcp", addr)`, whose error is returned; the caller's ghost step (`grpcUp` from
`Server`'s and `Listen`'s results); `go gs.Serve(l)` with the right to serve it gave.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.common.Serve
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Server
public import Spec.google_golang_org.grpc.KeepaliveEnforcementPolicy
public import Spec.net.Listen
public import Proof.go_etcd_io.etcd.client.v3.ServeFromStart

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace common

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.common.Assumptions]

theorem Serve.wp_proof
    (wp_KEP : grpc.KeepaliveEnforcementPolicy.spec (GF := GF) (hG := hG))
    (wp_Server : v3rpc.Server.spec (GF := GF) (hG := hG))
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_Serve : grpc.Server.Serve.spec (GF := GF) (hG := hG)) :
    Serve.spec (GF := GF) (hG := hG) := by
  intro CS s addr E ρ γr cfg Q Hlg Htos Hwpi Hms Hbuq
  wp_start as ⟨Haddr, #Hreq, #Hrd, #Hsf, HWR, #Hnrl, Hlg3, Hbemu, Hgo, Hwp, HG⟩
  -- `io.EOF`, from its package's fact; the imports' package facts
  ihave #Heof : v3rpc.eofVar (GF := GF) $$ []
  · iapply v3rpc.eofVar_of_init
    iPkgInit
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  ihave #Pv3 : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc $$ []
  · iPkgInit
  (try wp_auto)
  -- `v3rpc.Server(s, nil, nil, opt)`: its configuration from `NewServer`'s and `Start`'s
  ihave ⟨%C, #Hgc, %HC, HWRs⟩ : ∃ C : v3rpc.GrpcCfg GF, v3rpc.grpcCfgOk s C ∗
      ⌜C.A = v3rpc.srvKVAns s E ρ γr (W64 0) [] .none ∧ C.E = E⌝ ∗
      [∗list] _x ∈ List.replicate 64 (), mvcc.watchReader C.wsl E.s C.γ $$ [HWR]
  · iapply (client.grpcCfgOk_of_started_w s E ρ γr cfg [] Hlg 64)
    iframe; iframe #
    rw [Htos]
    iapply ownSlice_nil
  -- the server option: the keepalive policy, neutral (D28; D-T5)
  wp_apply wp_KEP as %kv %Hkv
  wp_apply wp_slice_literal (V := GoInterface) [kv]
  try (isplitr; (ipureintro; rfl))
  iintro %gslp ⟨Hgsl, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  imod ownSlice_persist _ _ _ $$ Hgsl with #Hgsl
  wp_apply (wp_Server Hms s C _ _ [kv] Hbuq) $$ [Hlg3 Hbemu Hgo Hwp]
    as %gs ⟨%q, %p, %pw, %il, %im, %iu, %ims, %is, %svcs, %regs, %sregs, %cid, %mid, %R, %d',
      Hgsn, %Hregs, #Hq, #Hkvs, #Hws, %HR, #Hil, #Him, #Hiu, #Hims, #His, Hlg4, Hbemu2, Hgo2,
      Hwpi2⟩
  · iframe; iframe #
    isplitr
    · ipureintro; rw [Hwpi]; simp
    ipureintro; intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    subst hv; exact Hkv
  -- `net.Listen("tcp", addr)`
  wp_apply (wp_Listen go!"tcp" addr) $$ [Haddr] as %lis %lerr Hlis
  · iframe; ipureintro; rfl
  icases Hlis with (⟨%Hlerr, Hlis⟩ | %Hlerr)
  rotate_left
  · cases lerr with
    | nil => exact absurd rfl Hlerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ileft; ipureintro; simp
  subst Hlerr
  wp_auto
  -- the caller's ghost step, between `Listen` and `go gs.Serve(l)`
  obtain ⟨hRs, hRE, hRw, hRγ⟩ := HR
  ihave Hup : grpcUp s E ρ γr gs lis addr cid mid R $$ [Hgsn Hlg4 Hbemu2 Hgo2 Hwpi2 HWRs Hlis]
  · iunfold grpcUp
    iexists C, q, p, pw, il, im, iu, ims, is, svcs, regs, sregs, d'
    iframe; iframe #
    ipureintro
    exact ⟨HC.1, HC.2, Hregs.1, Hregs.2, hRs, by rw [hRE, HC.2], hRw, hRγ⟩
  imod HG $$ %gs %lis %cid %mid %R Hup with ⟨Hserv, HQ⟩
  -- `go gs.Serve(l)`
  wp_apply wp_fork $$ [Hserv]
  · wp_apply (wp_Serve gs lis) $$ [$Hserv] as %serr -
    ipureintro; exact isPanic_intoVal serr
  (try wp_auto)
  iapply HΦ
  iright
  isplitr; · ipureintro; rfl
  iexists cid, mid, R
  iexact HQ

end proof

end common
end EtcdGrove
end Perennial
