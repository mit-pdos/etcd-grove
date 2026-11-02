/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/Cluster__Read.lean`. Lean-first (no
Rocq counterpart; `notes/spec-first-study/kvreconf-read-spec.md`).

`Replica.answer` answers a read with the key's value at the replica's applied index, which may be
past the read index raft confirmed, so the read's linearization point is not the confirmation: it
is the first change of the store's history, from the start of the call on, after which the key has
the returned value. Which value that is is known only at the return, so the call creates a
prophecy (`primitive.NewProph`) and resolves it with its answer before returning (gokv's
`trusted_proph.ResolveBytes`). At the start (`kvr_read_start`, `ReadSlot.lean`) the read registers
a slot with its caller's update, the history then and the prophesied answer (`ansOf`); the
history's growth (`kvr_propAu`, by `readReg_grow`) fires the update once the key's value is the
answer. Each attempt is a read at a random member from the history at the start (`Replica.read`,
unchanged); on an answer `v`, the key's value in a committed history extending the start, the
resolution says `v` is the prophesied answer, and the result is taken from the slot
(`kvr_read_take`), under two laters: three later credits (one for the start, two carried through
the retries, as `Cluster.do`'s).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster__Read
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster__randomMember
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__read
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Stats__add
public import Spec.github_com.mit_pdos.gokv.trusted_proph.ResolveBytes
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.ReadSlot
public import Perennial.Proof.github_com.goose_lang.primitive.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KvrStor GF]

attribute [local instance] kvrStorageModel

theorem Cluster.Read.wp_proof
    (wp_randomMember : Cluster.randomMember.spec (GF := GF) (hG := hG))
    (wp_read : Replica.read.spec (GF := GF) (hG := hG))
    (wp_add : Stats.add.spec (GF := GF) (hG := hG))
    (wp_ResolveBytes : github_com.mit_pdos.gokv.trusted_proph.ResolveBytes.spec (GF := GF)
      (hG := hG)) :
    Cluster.Read.spec (GF := GF) (hG := hG) := by
  intro γr vs c key Ψ Hkey
  wp_start as ⟨#Hcc, Hau⟩
  ihave #Hcc' := Hcc
  iunfold isClusterC at Hcc'
  iNamed Hcc'
  ihave #Hcl' := Hcl
  iunfold kvrCluster at Hcl'
  icases Hcl' with ⟨-, -, -, -, #Hinv⟩
  wp_auto_lc 3
  wp_apply github_com.goose_lang.primitive.wp_NewProph as %pvs %p Hp
  -- the read's slot, with its caller's update and the prophesied answer
  imod kvr_read_start γr key (ansOf pvs) Ψ ⊤ CoPset.subseteq_top kvrMask_sub_rkv
    $$ Hinv Hlc1 Hau with ⟨%γΦ, %H0, Hel, #Hsp, #HH0⟩
  try wp_auto
  ihave HI : iprop(£ 1 ∗ £ 1 ∗ proph p pvs ∗ γΦ ↪[γr.rds] (⟨key, H0, ansOf pvs⟩ : ReadRec))
    $$ [Hlc2 Hlc3 Hp Hel]
  · iframe Hlc2 Hlc3 Hp Hel
  wp_for HI
  wp_apply wp_randomMember γr vs c $$ [$Hcc] as %r ⟨%rid, #Hr⟩
  wp_apply wp_read γr vs rid r key (W64 100000000) H0 Hkey $$ [$Hr $HH0] as %v %ok Hres
  try wp_auto
  cases ok
  · -- no answer: another attempt
    simp only [Bool.false_eq_true, ↓reduceIte]
    try wp_auto
    ihave #Hctr := isStats_field (c.[RCluster, go!"Stats"]) go!"Retries" (by decide) $$ Hstats
    wp_apply wp_add _ _ $$ [$Hpkg $Hctr]
    wp_for_post
    iframe
  · -- the answer `v`: the prophecy resolved with it, the result from the read's slot
    simp only [↓reduceIte]
    icases Hres with ⟨%L, #HL, %HLv⟩
    icases HI with ⟨Hlc1, Hlc2, Hp, Hel⟩
    try wp_auto
    wp_apply wp_string_to_bytes v as %sl ⟨Hsl, -⟩
    wp_apply +noauto wp_ResolveBytes p pvs sl v _ $$ [$Hp $Hsl] as %pvs' ⟨%Hpvs, -, -⟩
    have Hans : (⟨key, H0, ansOf pvs⟩ : ReadRec).ans = some v := by
      show ansOf pvs = some v
      rw [Hpvs]; exact ansOf_cons v pvs'
    imod kvr_read_take γr γΦ ⟨key, H0, ansOf pvs⟩ Ψ L v ⊤ CoPset.subseteq_top Hans HLv.1 HLv.2
      $$ Hinv Hel Hsp HL with HQ
    imod lc_fupd_elim_later $$ Hlc1 HQ with HQ
    imod lc_fupd_elim_later $$ Hlc2 HQ with HQ
    try wp_auto
    wp_for_post
    iapply HΦ $$ HQ

end proof

end kvreconf
end EtcdGrove
end Perennial
