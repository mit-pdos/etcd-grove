/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/leaseexpiryN/run.lean` (`notes/leaseN-plan.md`,
2026-11-16). Lean-first (no Rocq counterpart).

- The serve loop (leaseN's, at the revocable mode): each member served (`etcdstart.Serve` with
  `etcdstart.kv_lease_served_go`: the live grant and the listing registered at its client address at its
  lessor's history, the thread token given back); with the lessor's reader invariant (from `memberUp`'s
  `srvLeaseRd`), the served member's facts (`srvdL`) accumulate as a persistent big-sep.
- The grant loop: through a new client of each member (`etcdstart.NewClient`), `grant` at the live
  grant's spec, whose reply's lease is live in the member's lessor from an index (`leaseLiveFrom`); the
  client and the lease id stored in the slices `clis` and `ids`; each pair's facts (`grantedAt`: the
  client, the listing's registration, the lessor's snapshot holding the lease, its reader invariant)
  accumulate as a persistent big-sep.
- The check loop: for each pair, `gone` at the snapshot's index (`true`: the lease absent at an index
  `k` at or after it), then `leases` at `k` (the listing is a snapshot at an index at or after `k`, where
  the lease is still absent, `lease.lessorAt_absent_stays`: an id is granted once), so `listed` is
  false and the panic is not reached.
Every error returns `Failed` (`1`); the end `Checked` (`0`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.run
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.grant
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.leases
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.listed
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.gone
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Serve
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.NewClient
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Served
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.ServedLease
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorHist
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.ServedLeaseLinked

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_leaseexpiryN

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver etcdstart

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **A served member's lease facts** (the serve loop's accumulated fact), at its client address: the
live grant and the listing registered there at its lessor `γl`'s history, and the lessor's reader
invariant (`V`: a client watch environment, which `NewClient`'s spec takes). -/
def srvdL (addr : GoString) : IProp GF :=
  iprop(∃ (EM : EtcdModel GF) (γl : GName) (V : client.WEnv GF),
    isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseGrant" (etcdLeaseGrantSpecLive (EM := EM) γl) ∗
    isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseLeases" (etcdLeaseLeasesSpecLive γl) ∗
    lease.lessorRdInv γl)

instance srvdL_persistent (addr : GoString) : Persistent (srvdL (GF := GF) addr) := by
  unfold srvdL; infer_instance

/-- **A granted lease's facts** (the grant loop's accumulated fact): the client `cl` of the member
the lease `id` was granted through, the listing registered at the client's endpoints at the member's
lessor `γl`'s history, a snapshot of that history holding the lease, and the reader invariant. -/
def grantedAt (cl : Loc) (id : w64) : IProp GF :=
  iprop(∃ (eps : List GoString) (V : client.WEnv GF) (γl : GName) (i : Nat) (σ : lease.LSnap),
    ⌜(σ.1.lookup id).isSome⌝ ∗ isNewClient cl eps V ∗
    isGrpcRpcs eps go!"/etcdserverpb.Lease/LeaseLeases" (etcdLeaseLeasesSpecLive γl) ∗
    lease.lessorAt γl i σ ∗ lease.lessorRdInv γl)

instance grantedAt_persistent (cl : Loc) (id : w64) : Persistent (grantedAt (GF := GF) cl id) := by
  unfold grantedAt; infer_instance

end defs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.Assumptions]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
/-- See the file header. -/
theorem run.wp_proof
    (wp_Serve : etcdstart.Serve.spec (GF := GF) (hG := hG))
    (wp_NewClient : etcdstart.NewClient.spec (GF := GF) (hG := hG))
    (wp_grant : grant.spec (GF := GF) (hG := hG))
    (wp_leases : leases.spec (GF := GF) (hG := hG))
    (wp_listed : listed.spec (GF := GF) (hG := hG))
    (wp_gone : gone.spec (GF := GF) (hG := hG)) :
    run.spec (GF := GF) (hG := hG) := by
  intro CS srvsl msl lg ss xs γn hxl Hpe Hlm Htb HLv Hrb48 Hbuq Hrf Hlp Hms hAs
  wp_start as ⟨#Hlgz, Hss, #Hmsl, Htok, Hcfree, Hups⟩
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  ihave #Pv3 : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc $$ []
  · iPkgInit
  ihave #Pst : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart $$ []
  · iPkgInit
  ihave %Hupl := BigSepL2.bigSepL2_length $$ Hups
  ihave %Hssl := ownSlice_len $$ Hss
  ihave %Hmsll := ownSlice_len $$ Hmsl
  have hmsZ : sint.Z msl.len = (xs.length : Int) := by have := Hmsll.1; simp at this; word
  imod ownSlice_persist _ _ _ $$ Hss with #Hss
  (try wp_auto)
  -- the serve loop
  ihave IH : (∃ (n jv : w64) (mv : GMember),
      "i" ∷ i_ptr ↦ n ∗ "j" ∷ j_ptr ↦ jv ∗ "m" ∷ m_ptr ↦ mv ∗ "Htok" ∷ threadTok ∗
      "Hups" ∷ ([∗list] s; x ∈ ss.drop (sint.nat n); xs.drop (sint.nat n),
        (threadTok -∗ memberUp s x.2.ρ x.2.E lg γn x.2.id .revocable)) ∗
      "Hcfree" ∷ ([∗list] x ∈ xs.drop (sint.nat n), netAddrFree (GF := GF) x.1.Client') ∗
      "#Hsv" ∷ ([∗list] x ∈ xs.take (sint.nat n), srvdL (GF := GF) x.1.Client') ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ xs.length⌝ : IProp GF)
      $$ [i j m Htok Hups Hcfree]
  · iexists W64 0, _, _
    have h00 : sint.nat (W64 0) = 0 := rfl
    simp only [h00, List.drop_zero, List.take_zero]
    iframe
    isplitl
    · iapply BigSepL.bigSepL_nil.2; itrivial
    ipureintro; exact ⟨by decide, by omega⟩
  wp_for IH
  wp_if_destruct
  · have hlt : sint.nat n < xs.length := by have := Hmsll.1; simp at this; word
    list_elem ss (sint.nat n) as sj
    list_elem xs (sint.nat n) as xj
    have hnz : (sint.Z n).toNat = sint.nat n := by word
    have Hbm : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z msl.len := ⟨Hn.1, Hif⟩
    have Hbs : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z srvsl.len := ⟨Hn.1, by have := Hssl.1; word⟩
    (try wp_auto)
    simp only [Hbm, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index msl (sint.Z n) _ _ xj.1 Hbm.1 $$ [Hmsl] as -
    · iframe #; ipureintro; rw [hnz, List.getElem?_map, Hxj_lookup]; rfl
    (try wp_auto)
    simp only [Hbs, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index srvsl (sint.Z n) _ _ sj Hbs.1 $$ [Hss] as -
    · iframe #; ipureintro; rw [hnz]; exact Hsj_lookup
    (try wp_auto)
    isimp only [drop_cons_of_getElem? ss _ sj Hsj_lookup, drop_cons_of_getElem? xs _ xj Hxj_lookup] at Hups
    ihave Hups := BigSepL2.bigSepL2_cons.1 $$ Hups
    icases Hups with ⟨Hupj, Hups⟩
    ihave Hupj := Hupj $$ Htok
    isimp only [drop_cons_of_getElem? xs _ xj Hxj_lookup] at Hcfree
    ihave Hcfree := BigSepL.bigSepL_cons.1 $$ Hcfree
    icases Hcfree with ⟨Hcj, Hcfree⟩
    have hxj : xj ∈ xs := List.mem_of_getElem? Hxj_lookup
    icases etcdstart.memberUp_served _ _ _ _ _ _ _ $$ Hupj with ⟨%E, %cfg, %γw, %HEc, #Hreq, #Hrd,
      #Hsf, Hgo, Hlg3, Hbemu, #Hwb, Hstk, -, #HLR⟩
    obtain ⟨HEa, HEo, HElg, HEtr, HEw⟩ := HEc
    -- the lessor's reader invariant
    icases etcdstart.srvLeaseRd_srvInv sj E .revocable (by decide) $$ HLR with ⟨%on, #Hsi⟩
    ihave #Hlrd := lease.srvInv_lessorRd on sj E .revocable $$ Hsi
    icases Hlrd with ⟨#Hslr, -⟩
    iunfold srvLessorRd at Hslr
    icases Hslr with ⟨%lpl, -, #Hlinv⟩
    iunfold lease.lessorInv at Hlinv
    icases Hlinv with ⟨-, -, -, #HrdInv⟩
    -- `Serve(srvs[j], m.Client)`, with the live grant and the listing registered at the address
    haveI := Hms
    ihave ⟨%HsvOff, #HreqM, #HrdM, #Hlb⟩ := etcdstart.serveViews_off sj E { xj.2.ρ with wait := γw }
      xj.2.ρ.rd $$ []
    · iframe #
    ihave #HzlgC : zapLoggerOk cfg.Logger' $$ []
    · rw [HElg]; iexact Hlgz
    wp_apply (wp_Serve sj xj.1.Client' E { xj.2.ρ with wait := γw } xj.2.ρ.rd cfg
        (fun _ _ _ => iprop(etcdstart.etcdLeaseGrantLiveAt (GF := GF) xj.1.Client' sj E xj.2.ρ.rd ∗
          srvGoRes sj)))
      $$ [Hcj Hlg3 Hbemu Hgo Hstk] as %serr Hs
    · iframe; iframe #
      isplitr
      · ipureintro; exact ⟨HEtr, HEw, Hms, Hbuq, HsvOff.2, Htb⟩
      iintro %gs' %lis %cid %mid %R Hg
      rw [HsvOff.1]
      ihave Hg := etcdstart.grpcUpM_false _ _ _ _ _ _ _ _ _ _ $$ Hg
      have h := etcdstart.kv_lease_served_go sj E { xj.2.ρ with wait := γw } xj.2.ρ.rd gs' lis
        xj.1.Client' cid mid R Hrb48 (by omega) Hrf Hlp rfl .revocable (Hlm xj hxj) HLv
      simp only [etcdstart.etcdLeaseServedAt] at h
      imod h $$ [Hg Hstk] with ⟨Htk, Hgo', -, #Hga⟩
      · iframe; iframe #
      imodintro
      iframe Htk Hgo'
      iframe #
    icases Hs with (%Hserr | ⟨%Hserr, %cid, %mid, %R, #Hga, Hgr⟩)
    · cases serr with
      | nil => exact absurd rfl Hserr
      | ok ei => ?_
      (try wp_auto)
      wp_for_post
      iapply HΦ; ipureintro; right; rfl
    subst Hserr
    (try wp_auto)
    iunfold srvGoRes at Hgr
    icases Hgr with ⟨-, Htok⟩
    iunfold etcdstart.etcdLeaseGrantLiveAt at Hga
    icases Hga with ⟨#Hrg, -, #Hrls⟩
    ihave #Hsv' : [∗list] x ∈ xs.take (sint.nat n + 1), srvdL (GF := GF) x.1.Client' $$ []
    · rw [List.take_add_one, Hxj_lookup, Option.toList_some]
      iapply BigSepL.bigSepL_snoc.2
      iframe #
      iunfold srvdL
      iexists _, (mvcc.api.mvccLeases E.γ),
        EtcdGrove.client.srvWEnv R (etcdstart.srvWOf R.E xj.2.ρ.rd false) xj.2.ρ.rd xj.1.Client' [] null
          null [] null default
      iframe #
    iclear Hsv
    wp_for_post
    iframe
    have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    iexists n + W64 1, n, xj.1
    rw [hn1]
    iframe
    iframe #
    ipureintro; exact ⟨by word, by omega⟩
  -- every member served
  have hnk : sint.nat n = xs.length := by have := Hmsll.1; simp at this; word
  ihave #Hsv : [∗list] x ∈ xs, srvdL (GF := GF) x.1.Client' $$ []
  · iExactEq Hsv; rw [hnk, List.take_of_length_le (Nat.le_refl _)]
  iclear Hups Hcfree
  (try wp_auto)
  -- `clis := make([]*clientv3.Client, len(ms))`, `ids := make([]clientv3.LeaseID, len(ms))`
  wp_apply (wp_slice_make2 (V := Loc) msl.len) as %clsl ⟨Hclsl, -⟩
  · ipureintro; word
  (try wp_auto)
  wp_apply (wp_slice_make2 (V := w64) msl.len) as %idsl ⟨Hidsl, -⟩
  · ipureintro; word
  (try wp_auto)
  have hkn : sint.nat msl.len = xs.length := by word
  -- the grant loop
  ihave IG : (∃ (n jv : w64) (mv : GMember) (cs : List Loc) (gids : List w64),
      "i" ∷ i_ptr ↦ n ∗ "j" ∷ j_ptr ↦ jv ∗ "m" ∷ m_ptr ↦ mv ∗
      "Hclsl" ∷ clsl ↦* (cs ++ List.replicate (xs.length - cs.length) (zero_val Loc)) ∗
      "Hidsl" ∷ idsl ↦* (gids ++ List.replicate (xs.length - gids.length) (zero_val w64)) ∗
      "#Hgr" ∷ ([∗list] p ∈ cs.zip gids, grantedAt (GF := GF) p.1 p.2) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ xs.length ∧ cs.length = sint.nat n ∧
        gids.length = sint.nat n⌝ : IProp GF)
      $$ [i j m Hclsl Hidsl]
  · iexists W64 0, _, _, [], []
    simp only [List.length_nil, Nat.sub_zero, List.nil_append, List.zip_nil_left]
    iframe
    isplitl [Hclsl]
    · iExactEq Hclsl; rw [hkn]
    isplitl [Hidsl]
    · iExactEq Hidsl; rw [hkn]
    isplitl
    · iapply BigSepL.bigSepL_nil.2; itrivial
    have h00 : sint.nat (W64 0) = 0 := rfl
    ipureintro; exact ⟨by decide, by omega, h00.symm, h00.symm⟩
  wp_for IG
  wp_if_destruct
  · have hlt : sint.nat n < xs.length := by word
    list_elem xs (sint.nat n) as xj
    have hxj : xj ∈ xs := List.mem_of_getElem? Hxj_lookup
    have hnz : (sint.Z n).toNat = sint.nat n := by word
    have Hbm : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z msl.len := ⟨Hn.1, Hif⟩
    (try wp_auto)
    simp only [Hbm, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index msl (sint.Z n) _ _ xj.1 Hbm.1 $$ [Hmsl] as -
    · iframe #; ipureintro; rw [hnz, List.getElem?_map, Hxj_lookup]; rfl
    (try wp_auto)
    ihave #Hsj := BigSepL.bigSepL_lookup Hxj_lookup $$ Hsv
    iunfold srvdL at Hsj
    icases Hsj with ⟨%EM, %γl, %V, #Hrg, #Hrls, #HrdInv⟩
    -- `cli, err := etcdstart.NewClient(m.Client, lg)`
    wp_apply (wp_NewClient xj.1.Client' lg V (Hpe xj hxj) (by omega))
      as %cl %cerr Hcl
    · iframe #
    icases Hcl with (⟨%Hcerr, #Hnc, -⟩ | %Hcfail)
    rotate_left
    · obtain ⟨Hcerr, -⟩ := Hcfail
      cases cerr with
      | nil => exact absurd rfl Hcerr
      | ok ei => ?_
      (try wp_auto)
      wp_for_post
      iapply HΦ; ipureintro; right; rfl
    subst Hcerr
    (try wp_auto)
    -- `g, err := grant(cli)`, `Q`: the lease live in the member's lessor from an index
    wp_apply (wp_grant cl [xj.1.Client'] V
        (etcdLeaseGrantSpecLive (EM := EM) γl)
        (fun r => iprop(∃ (i : Nat) (l : Loc), lease.leaseLiveFrom γl i r.id l))) as %gr %gerr Hgr
    · iframe #
      isplitl; rotate_left; · ipureintro; exact hAs
      imodintro; inext
      iunfold etcdLeaseGrantSpecLive, etcdLeaseGrantSpecLiveW
      iunfold etcdLeaseGrantSpecGRW
      iunfold etcdLeaseGrantSpecGW
      isplitr
      · ipureintro; rfl
      iintro %r - - ⟨%i, %l, #Hlv, -⟩
      iexists i, l
      iexact Hlv
    icases Hgr with (⟨%Hgerr, %mg, #Hgid, ⟨%gi, %gl, #Hlive⟩⟩ | %Hgerr)
    rotate_left
    · cases gerr with
      | nil => exact absurd rfl Hgerr
      | ok ei => ?_
      (try wp_auto)
      wp_for_post
      iapply HΦ; ipureintro; right; rfl
    subst Hgerr
    (try wp_auto)
    -- `clis[j] = cli`, `ids[j] = g.ID`
    ihave %Hcll := ownSlice_len $$ Hclsl
    ihave %Hidl := ownSlice_len $$ Hidsl
    have hcl : (cs ++ List.replicate (xs.length - cs.length) (zero_val Loc)).length = xs.length := by
      simp; omega
    have hil : (gids ++ List.replicate (xs.length - gids.length) (zero_val w64)).length = xs.length := by
      simp; omega
    rw [hcl] at Hcll
    rw [hil] at Hidl
    have Hb2 : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z clsl.len := by
      obtain ⟨h1, h2⟩ := Hcll; constructor <;> word
    have Hb3 : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z idsl.len := by
      obtain ⟨h1, h2⟩ := Hidl; constructor <;> word
    simp only [Hb2, _root_.and_self, ↓reduceIte]
    wp_apply (wp_store_slice_index clsl (sint.Z n) _ cl) $$ [Hclsl] as Hclsl
    · iframe Hclsl; ipureintro; rw [hcl]; constructor <;> word
    (try wp_auto)
    simp only [Hb3, _root_.and_self, ↓reduceIte]
    wp_apply (wp_store_slice_index idsl (sint.Z n) _ mg.id) $$ [Hidsl] as Hidsl
    · iframe Hidsl; ipureintro; rw [hil]; constructor <;> word
    (try wp_auto)
    -- the pair's facts
    iunfold lease.leaseLiveFrom at Hlive
    icases Hlive with ⟨%i', %σ, %Hσ, #Hσat⟩
    have hzz : (cs ++ [cl]).zip (gids ++ [mg.id]) = cs.zip gids ++ [(cl, mg.id)] := by
      rw [List.zip_append (by omega)]; rfl
    ihave #Hgr' : [∗list] p ∈ (cs ++ [cl]).zip (gids ++ [mg.id]), grantedAt (GF := GF) p.1 p.2 $$ []
    · rw [hzz]
      iapply BigSepL.bigSepL_snoc.2
      iframe #
      iunfold grantedAt
      iexists [xj.1.Client'], V, γl, i', σ
      iframe #
      ipureintro; rw [Hσ.2]; rfl
    iclear Hgr
    wp_for_post
    iframe
    have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    iexists n + W64 1, n, xj.1, cs ++ [cl], gids ++ [mg.id]
    rw [hn1]
    iframe; iframe #
    have hcz : (sint.Z n).toNat = cs.length := by rw [hnz, Hn.2.2.1]
    have hgz : (sint.Z n).toNat = gids.length := by rw [hnz, Hn.2.2.2]
    isplitl [Hclsl]
    · iExactEq Hclsl
      rw [hcz, set_replicate_snoc _ _ _ _ (by omega)]
      simp only [List.length_append, List.length_singleton]
    isplitl [Hidsl]
    · iExactEq Hidsl
      rw [hgz, set_replicate_snoc _ _ _ _ (by omega)]
      simp only [List.length_append, List.length_singleton]
    ipureintro; refine ⟨by word, by omega, by simp [Hn.2.2.1], by simp [Hn.2.2.2]⟩
  -- every member granted: the slices hold the clients and the lease ids
  have hnk2 : sint.nat n = xs.length := by word
  have hcsl : cs.length = xs.length := by omega
  have hgsl : gids.length = xs.length := by omega
  simp only [hcsl, hgsl, Nat.sub_self, List.replicate_zero, List.append_nil]
  imod ownSlice_persist _ _ _ $$ Hclsl with #Hclsl
  imod ownSlice_persist _ _ _ $$ Hidsl with #Hidsl
  ihave %Hcll := ownSlice_len $$ Hclsl
  ihave %Hidl := ownSlice_len $$ Hidsl
  (try wp_auto)
  -- the check loop
  ihave IB : (∃ (n jv : w64), "i" ∷ i_ptr ↦ n ∗ "j" ∷ j_ptr ↦ jv ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ xs.length⌝ : IProp GF) $$ [i j]
  · iexists W64 0, _
    iframe
    ipureintro; exact ⟨by decide, by simp⟩
  wp_for IB
  wp_if_destruct
  · have hlt : sint.nat n < xs.length := by word
    list_elem cs (sint.nat n) as cj
    list_elem gids (sint.nat n) as idj
    have hnz : (sint.Z n).toNat = sint.nat n := by word
    have Hb2 : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z clsl.len := ⟨Hn.1, by have := Hcll.1; word⟩
    have Hb3 : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z idsl.len := ⟨Hn.1, by have := Hidl.1; word⟩
    have hzj : (cs.zip gids)[sint.nat n]? = some (cj, idj) :=
      List.getElem?_zip_eq_some.2 ⟨Hcj_lookup, Hidj_lookup⟩
    ihave #Hgj := BigSepL.bigSepL_lookup hzj $$ Hgr
    iunfold grantedAt at Hgj
    icases Hgj with ⟨%eps, %V, %γl, %i, %σ, %Hσ, #Hnc, #Hrls, #Hσat, #HrdInv⟩
    ihave #Hlb := lease.lessorAt_lb γl i σ $$ Hσat
    (try wp_auto)
    -- the range's element (`ms[j]`, unused)
    list_elem xs (sint.nat n) as xj
    have Hbm : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z msl.len := ⟨Hn.1, Hif⟩
    simp only [Hbm, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index msl (sint.Z n) _ _ xj.1 Hbm.1 $$ [Hmsl] as -
    · iframe #; ipureintro; rw [hnz, List.getElem?_map, Hxj_lookup]; rfl
    (try wp_auto)
    simp only [Hb2, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index clsl (sint.Z n) _ _ cj Hb2.1 $$ [Hclsl] as -
    · iframe #; ipureintro; rw [hnz]; exact Hcj_lookup
    (try wp_auto)
    simp only [Hb3, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index idsl (sint.Z n) _ _ idj Hb3.1 $$ [Hidsl] as -
    · iframe #; ipureintro; rw [hnz]; exact Hidj_lookup
    (try wp_auto)
    -- `gone(clis[j], ids[j])`
    wp_apply (wp_gone cj eps V γl i idj) as %b Hb
    · iframe #; ipureintro; exact hAs
    cases b
    · (try wp_auto)
      wp_for_post
      iapply HΦ; ipureintro; right; rfl
    isimp only [↓reduceIte] at Hb
    iunfold lease.leaseAbsentFrom at Hb
    icases Hb with ⟨%k, %ρa, %Hρa, #Hρat⟩
    ihave #Hlbk := lease.lessorAt_lb γl k ρa $$ Hρat
    (try wp_auto)
    -- `ls, err := leases(clis[j])`, at the absence's index
    simp only [Hb2, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index clsl (sint.Z n) _ _ cj Hb2.1 $$ [Hclsl] as -
    · iframe #; ipureintro; rw [hnz]; exact Hcj_lookup
    (try wp_auto)
    wp_apply (wp_leases cj eps V (etcdLeaseLeasesSpecLive γl)
        (fun r => iprop(∃ j : Nat, ⌜k ≤ j⌝ ∗ lease.leaseIdsAt γl j r.ids))) as %ls %lerr Hls
    · iframe #
      isplitl; rotate_left; · ipureintro; exact hAs
      imodintro; inext
      iunfold etcdLeaseLeasesSpecLive, etcdLeaseLeasesSpecLiveW
      iexists k
      iframe Hlbk
      iintro %r Hr
      iexact Hr
    icases Hls with (⟨%Hlerr, %ml, %sl, #Hslf, #Hsl, ⟨%j, %Hkj, #Hids⟩⟩ | %Hlerr)
    rotate_left
    · cases lerr with
      | nil => exact absurd rfl Hlerr
      | ok ei => ?_
      (try wp_auto)
      wp_for_post
      iapply HΦ; ipureintro; right; rfl
    subst Hlerr
    (try wp_auto)
    -- the listing is a snapshot where the lease is still absent
    iunfold lease.leaseIdsAt at Hids
    icases Hids with ⟨%τ, %Hτ, #Hτat⟩
    imod lease.lessorAt_absent_stays γl i k j σ ρa τ idj ⊤ (by simp) Hσ Hρa.1 Hρa.2 Hkj
        $$ [HrdInv Hσat Hρat Hτat] with %Hτn
    · iframe #
    have Hnot : idj ∉ ml.ids := by
      intro h
      have := (Hτ.2 idj).1 h
      rw [Hτn] at this
      simp at this
    simp only [Hb3, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index idsl (sint.Z n) _ _ idj Hb3.1 $$ [Hidsl] as -
    · iframe #; ipureintro; rw [hnz]; exact Hidj_lookup
    (try wp_auto)
    wp_apply (wp_listed ls sl ml.ids idj) $$ []
    · iframe #
    rw [decide_eq_false Hnot]
    (try wp_auto)
    wp_for_post
    iframe
    iexists n + W64 1, n
    iframe
    ipureintro; constructor <;> word
  (try wp_auto)
  iapply HΦ; ipureintro; left; rfl

end proof

end etcd_leaseexpiryN
end EtcdGrove
end Perennial
