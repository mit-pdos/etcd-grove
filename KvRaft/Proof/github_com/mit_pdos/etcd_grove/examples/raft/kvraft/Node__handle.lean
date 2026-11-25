/-
The proof of `KvRaft/Spec/.../kvraft/Node__handle.lean`: the dispatch by kind, each branch's call at
its seam (`Replica.propose`/`read` over `rep`, `GetConfChange` over `cf` with the conf law and raft's
`node.ProposeConfChange`, raft's disruption calls, `Node.status` and `PutStatus`), the payload's
shape from its fact (`reqOk`).
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Node__handle
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Replica__propose
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Replica__read
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.decode
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.GetConfChange
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.PutStatus
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Node__status
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Node__current
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Node__restart
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Stats__add
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.getUint64
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.getBytes
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.withTimeout
public import KvRaft.Spec.go_etcd_io.raft.v3.node__ProposeConfChange
public import KvRaft.Spec.go_etcd_io.raft.v3.node__TransferLeadership
public import KvRaft.Spec.go_etcd_io.raft.v3.node__Campaign
public import KvRaft.Spec.go_etcd_io.raft.v3.node__ForgetLeader
public import KvRaft.Spec.go_etcd_io.raft.v3.node__Status

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Iris.ProofMode Net go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

theorem Node.handle.wp_proof (F : KvFacts GF) (rep : Loc → w64 → IProp GF) (stp : NodeStopper GF)
    (cf : GoInterface → List w8 → IProp GF)
    (wp_current : Node.current.spec (GF := GF) (hG := hG) F rep stp)
    (wp_restart : Node.restart.spec (GF := GF) (hG := hG) F rep stp)
    (wp_propose : Replica.propose.spec (GF := GF) (hG := hG) F rep)
    (wp_read : Replica.read.spec (GF := GF) (hG := hG) F rep)
    (wp_decode : decode.spec (GF := GF) (hG := hG))
    (wp_GetConfChange : GetConfChange.spec (GF := GF) (hG := hG) cf)
    (wp_PutStatus : PutStatus.spec (GF := GF) (hG := hG))
    (wp_status : Node.status.spec (GF := GF) (hG := hG) F rep stp)
    (wp_add : Stats.add.spec (GF := GF) (hG := hG))
    (wp_getUint64 : getUint64.spec (GF := GF) (hG := hG))
    (wp_getBytes : getBytes.spec (GF := GF) (hG := hG))
    (wp_withTimeout : withTimeout.spec (GF := GF) (hG := hG))
    (wp_ProposeConfChange : node.ProposeConfChange.spec (GF := GF) (hG := hG))
    (wp_TransferLeadership : node.TransferLeadership.spec (GF := GF) (hG := hG))
    (wp_Campaign : node.Campaign.spec (GF := GF) (hG := hG))
    (wp_ForgetLeader : node.ForgetLeader.spec (GF := GF) (hG := hG))
    (wp_Status : node.Status.spec (GF := GF) (hG := hG)) :
    Node.handle.spec (GF := GF) (hG := hG) F rep stp cf := by
  intro nd γ N id kind p pl dq tmo Hpl
  wp_start as ⟨#Hnd, #Hcl, #Hcc, Hp, #Hok⟩
  ihave #Hnd' := Hnd
  iunfold isNodeS at Hnd'
  icases Hnd' with ⟨%cfg, %Mc, %sp, %f, #Hcfg, %Hid, #HMc, #Hsp, #Hs, #HnewT, #Hstep, %Htr, -, #Hmu⟩
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  try wp_auto
  -- (2026-11-24, G5) the current incarnation's replica, read once
  wp_apply wp_current nd γ N id $$ [$Hpkg $Hnd] as %r ⟨%n, #Hrn, #Hrep, #Hn⟩
  try wp_auto
  wp_if_destruct
  · -- ReqPropose
    rw [reqOk_propose]
    wp_apply wp_decode p pl dq $$ [$Hpkg $Hp] as Hp
    unfold decodeRet
    cases raft_kvreconf.decodeOp pl with
    | none =>
      try wp_auto
      iapply HΦ
      ileft; ipureintro; rfl
    | some r0 =>
    obtain ⟨i, k, key, v⟩ := r0
    try wp_auto
    wp_apply wp_propose r id p pl dq tmo $$ [$Hpkg $Hrep $Hp $Hok] as %v %ok Hans
    try wp_auto
    wp_apply wp_string_to_bytes v as %vb ⟨Hvb, -⟩
    try wp_auto
    cases ok
    · iapply HΦ
      ileft; ipureintro; rfl
    iapply HΦ
    iright
    iexists v
    rw [ansOk_propose]
    simp only [if_true]
    iframe Hvb Hans
  wp_if_destruct
  · -- ReqRead
    rw [reqOk_read]
    icases Hok with ⟨%seq, %key, %Hpl', #Hro⟩
    subst Hpl'
    have Hkl : (key.length : Int) < 2 ^ 63 := by
      simp only [List.length_append, putB, u64Le_length] at Hpl; omega
    wp_apply wp_getUint64 p dq seq (putB key) $$ [$Hpkg $Hp] as %r1 ⟨Hr1, -⟩
    try wp_auto
    rw [← List.append_nil (putB key)]
    wp_apply wp_getBytes r1 dq key [] Hkl $$ [$Hpkg $Hr1] as %kv %rest ⟨Hkv, -, -⟩
    try wp_auto
    wp_apply wp_bytes_to_string $$ Hkv with Hkv
    try wp_auto
    wp_apply wp_read r id seq key tmo $$ [$Hpkg $Hrep $Hro] as %v %ok Hans
    try wp_auto
    wp_apply wp_string_to_bytes v as %vb ⟨Hvb, -⟩
    try wp_auto
    cases ok
    · iapply HΦ
      ileft; ipureintro; rfl
    iapply HΦ
    iright
    iexists v
    rw [ansOk_read]
    simp only [if_true]
    iframe Hvb
    iexists seq, key
    iframe Hans
    ipureintro; simp
  wp_if_destruct
  · -- ReqConf
    rw [reqOk_conf]
    icases Hok with %Hcok
    wp_apply wp_GetConfChange p pl dq $$ [$Hpkg $Hp] as %c %ok Hcf
    try wp_auto
    cases ok
    · try wp_auto
      iapply HΦ
      ileft; ipureintro; rfl
    try wp_auto
    wp_apply wp_add sp (W64 7) (by decide) (by decide) $$ [$Hpkg $Hs]
    try wp_auto
    wp_apply wp_withTimeout _ $$ [$Hpkg $Hcc] as %ctx' %cd %cancel ⟨#Hcancel, #Hctx, -⟩
    try wp_auto
    ihave #Hnc : nodeCtx ctx' cd $$ []
    · unfold nodeCtx; iright; iexact Hctx
    simp only [if_true]
    iunfold confLaw at Hcl
    imod Hcl $$ %r %c %pl Hrep Hcf %Hcok with ⟨%o, %cc, %dq', Hccp, %Hm, Hau⟩
    wp_apply wp_ProposeConfChange n γ N id c o cc dq' ctx' cd Htr $$ [$Hraft $Hn $Hnc $Hccp Hau]
      as %err -
    · iframe %Hm
      iexact Hau
    try wp_auto
    wp_apply Hcancel
    try wp_auto
    cases err with
    | nil =>
      try wp_auto
      iapply HΦ
      iright
      iexists []
      rw [ansOk_other F id (W8 3) pl [] (by decide) (by decide)]
      ihave Hnil := ownSlice_nil (V := w8) (GF := GF) (DFrac.own 1)
      iframe Hnil
      ipureintro; rfl
    | ok i =>
      try wp_auto
      iapply HΦ
      ileft; ipureintro; rfl
  wp_if_destruct
  · -- ReqDisrupt
    rw [reqOk_disrupt]
    icases Hok with %Hd
    obtain ⟨what, to, rfl⟩ := Hd
    wp_apply wp_getUint64 p dq what (u64Le to) $$ [$Hpkg $Hp] as %r1 ⟨Hr1, -⟩
    try wp_auto
    rw [← List.append_nil (u64Le to)]
    wp_apply wp_getUint64 r1 dq to [] $$ [$Hpkg $Hr1] as %r2 ⟨-, -⟩
    try wp_auto
    wp_if_destruct
    · -- (2026-11-24, G5) what = 3: the replica restarted in its process
      wp_apply wp_restart nd γ N id $$ [$Hpkg $Hnd]
      try wp_auto
      iapply HΦ
      iright
      iexists []
      rw [ansOk_other F id (W8 4) _ [] (by decide) (by decide)]
      ihave Hnil := ownSlice_nil (V := w8) (GF := GF) (DFrac.own 1)
      iframe Hnil
      ipureintro; rfl
    wp_apply wp_withTimeout _ $$ [$Hpkg $Hcc] as %ctx' %cd %cancel ⟨#Hcancel, #Hctx, -⟩
    try wp_auto
    ihave #Hnc : nodeCtx ctx' cd $$ []
    · unfold nodeCtx; iright; iexact Hctx
    wp_if_destruct
    · wp_apply wp_Status n γ N id $$ [$Hraft $Hn] as %st -
      try wp_auto
      wp_apply wp_TransferLeadership n γ N id _ to ctx' cd Htr $$ [$Hraft $Hn $Hnc]
      try wp_auto
      wp_apply Hcancel
      try wp_auto
      iapply HΦ
      iright
      iexists []
      rw [ansOk_other F id (W8 4) _ [] (by decide) (by decide)]
      ihave Hnil := ownSlice_nil (V := w8) (GF := GF) (DFrac.own 1)
      iframe Hnil
      ipureintro; rfl
    wp_if_destruct
    · wp_apply wp_Campaign n γ N id ctx' cd $$ [$Hraft $Hn $Hnc] as %err -
      try wp_auto
      wp_apply Hcancel
      try wp_auto
      iapply HΦ
      iright
      iexists []
      rw [ansOk_other F id (W8 4) _ [] (by decide) (by decide)]
      ihave Hnil := ownSlice_nil (V := w8) (GF := GF) (DFrac.own 1)
      iframe Hnil
      ipureintro; rfl
    · wp_apply wp_ForgetLeader n γ N id ctx' cd Htr $$ [$Hraft $Hn $Hnc] as %err -
      try wp_auto
      wp_apply Hcancel
      try wp_auto
      iapply HΦ
      iright
      iexists []
      rw [ansOk_other F id (W8 4) _ [] (by decide) (by decide)]
      ihave Hnil := ownSlice_nil (V := w8) (GF := GF) (DFrac.own 1)
      iframe Hnil
      ipureintro; rfl
  wp_if_destruct
  · -- ReqStatus
    wp_apply wp_status nd γ N id $$ [$Hpkg $Hnd] as %s ⟨%M, %c, HM, #Hcs, %HSt⟩
    wp_apply wp_PutStatus s M (DFrac.own 1) c HSt $$ [$Hpkg $HM $Hcs] as %sl ⟨%bs, Hbs, -⟩
    try wp_auto
    iapply HΦ
    iright
    iexists bs
    rw [ansOk_other F id (W8 5) _ bs (by decide) (by decide)]
    iframe Hbs
    ipureintro; rfl
  · -- another kind: no answer
    try wp_auto
    iapply HΦ
    ileft; ipureintro; rfl

end proof

end kvraft
end EtcdGrove
end Perennial
