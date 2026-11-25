/-
The proof of `KvRaft/Spec/.../kvraft/RequestWithin.lean`: `RequestVia`'s spec with the dialer
`DialTCP`, its one call made from `DialTCP`'s spec and the caller's dial update (a dial error is an
`*OpError`, not `nil`).
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.RequestWithin
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.RequestVia
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.DialTCP

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Iris.ProofMode Net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [package_sem' : net.Assumptions] [field_sem : net.FieldAssumptions]

theorem RequestWithin.wp_proof (wp_RequestVia : RequestVia.spec (GF := GF) (hG := hG))
    (wp_DialTCP : DialTCP.spec (GF := GF) (hG := hG)) :
    RequestWithin.spec (GF := GF) (hG := hG) := by
  intro addr kind tmo total payload pl dqp W Rd Fl eof ed et Hpl
  wp_start as ⟨Hp, #Heof, #Hed, #Het, %Ha, Hupd⟩
  wp_auto
  wp_apply wp_RequestVia (functions github_com.mit_pdos.etcd_grove.examples.raft.kvraft.DialTCP [])
      addr kind tmo total payload pl dqp W Rd Fl eof ed Hpl $$ [Hp Hupd] as %b %ok Hpost
  · iframe Hp Heof Hed
    iintro %d %Φ' HΦ'
    wp_apply wp_DialTCP addr d et ed Fl (fun cn => connRes cn false (helloClientB :: putB (reqBytes kind tmo pl)) W Rd) $$ [Hupd]
      as %c %err Hres
    · iframe Het Hed Hupd
      ipureintro; exact Ha
    iapply HΦ'
    icases Hres with (⟨%He, %cn, #Hc, Hcr⟩ | ⟨HFl, %x, %e, #Hx, #Hop, -⟩)
    · ileft
      isplitr
      · ipureintro; exact He
      iexists cn, false, addr
      iframe Hc Hcr
    · iright
      iframe HFl
      iunfold net.opErr at Hop
      icases Hop with ⟨%pe, %nw, %Herr, -⟩
      ipureintro
      rw [Herr.1]
      intro h
      cases h
  try wp_auto
  iapply HΦ
  iexact Hpost

end proof

end kvraft
end EtcdGrove
end Perennial
