/- Lean-first (no Rocq counterpart). The proof of `writer` (W4d of `notes/watch-cut-plan.md`;
watchkv's, with linkv3p's `Apply`'s pick of a client): the loop over `tried[lo:hi]`; each put
through the client at `RandomUint64() % len(clis)`, with the writer's update at every member
(`put_au` at the history's names, `kvOpAu1_congr`); each successful put's reply, some member's,
gives `okFactH` (`okFactH_of_reply`), logged under the lock. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv3p.writer
public import Perennial.Proof.context.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.github_com.goose_lang.primitive.Link

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3p

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver
open go_etcd_io.etcd.api.v3 go_etcd_io.etcd.client.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv3p.Assumptions]

set_option maxHeartbeats 400000 in
theorem writer.wp_proof :
    writer.spec (GF := GF) (hG := hG) := by
  intro CS clis cls ms V γr w tsl tried lo hi P hAs hwl hP hrb hne hlo hlh hhi
  wp_start as ⟨#Hcls, #Hcl, #Hms, #Ht, #Hkv, #Hmu⟩
  ihave #Pc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave %Htl := ownSlice_len $$ Ht
  ihave %Hl := ownSlice_len $$ Hcls
  (try wp_auto)
  wp_apply context.wp_Background
  imod client.background_ctx (GF := GF) hAs with ⟨%cd, #Hctx, #Hce⟩
  (try wp_auto)
  ihave #Hnil : optsAt (GF := GF) slice.nil [] $$ []
  · iunfold optsAt
    iexists ([] : List GoFunc)
    isplitl
    · iapply ownSlice_nil
    isplitl
    · ipureintro; rfl
    imodintro
    iintro %i %f %g %Hf %Hg
    simp at Hf
  -- the members' registrations and empty logs, out of `memberPut`
  ihave #Hregs : ([∗list] x ∈ ms, client.kvRegsAt x) $$ [Hms]
  · iapply (BigSepL.bigSepL_mono (Φ := fun _ x => memberPut (GF := GF) γr x) fun _ => by
      iintro #H; iunfold memberPut at H; icases H with ⟨#H1, -⟩; iexact H1) $$ Hms
  ihave #HF : ([∗list] x ∈ ms, mvcc.idxCert x.E.γ.idx []) $$ [Hms]
  · iapply (BigSepL.bigSepL_mono (Φ := fun _ x => memberPut (GF := GF) γr x) fun _ => by
      iintro #H; iunfold memberPut at H; icases H with ⟨-, -, #H1, -⟩; iexact H1) $$ Hms
  have hlen : cls.length ≠ 0 := fun h => hne (List.eq_nil_of_length_eq_zero h)
  ihave HI : (∃ (k : w64), "k" ∷ k_ptr ↦ k ∗
      "%Hk" ∷ ⌜sint.Z lo ≤ sint.Z k ∧ sint.Z k ≤ sint.Z hi⌝ : IProp GF) $$ [k]
  · iexists lo
    iframe
    ipureintro; constructor <;> word
  wp_for HI
  wp_if_destruct
  · have Hb' : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z tsl.len := ⟨by word, by have := Htl.1; word⟩
    simp only [Hb', _root_.and_self, ↓reduceIte]
    list_elem tried (sint.nat k) as x
    wp_apply wp_load_slice_index tsl (sint.Z k) tried DFrac.discard x Hb'.1 $$ [Ht] as -
    · iframe #; ipureintro; exact Hx_lookup
    have hxP : (x.Key', x.Val') ∈ P := by
      rw [← hP]; exact List.mem_map.2 ⟨x, List.mem_of_getElem? Hx_lookup, rfl⟩
    -- the writer's update, at every member's names
    have hau := client.bigAndL_of_sep ms (watchkv.wkKV (GF := GF) γr)
      (fun y : client.SrvAt GF => memberPut γr y)
      (fun y : client.SrvAt GF =>
        kvOpAu1 y.γr.kv (.put (client.putKeyOp x.Key' x.Val')) (fun _ => iprop(True)))
      (fun y _ => by
        iintro ⟨#Hk, #Hm⟩
        iunfold memberPut at Hm
        icases Hm with ⟨-, -, -, %h⟩
        rw [kvOpAu1_congr y.γr.kv γr.kv h.2.1 h.2.2]
        iapply watchkv.put_au γr P hwl x.Key' x.Val' hxP $$ Hk)
    ihave Hau := hau $$ [Hkv Hms]
    · iframe #
    (try wp_auto)
    -- `cli := clis[RandomUint64() % len(clis)]`
    wp_apply github_com.goose_lang.primitive.wp_RandomUint64 as %n -
    (try wp_auto)
    have hpos : 0 < sint.Z clis.len := by
      obtain ⟨h1, h2⟩ := Hl
      unfold sint.nat at h1
      show 0 < BitVec.toInt clis.len
      omega
    have hz : ¬ uint.Z clis.len = 0 := by word
    rw [if_neg hz]
    (try wp_auto)
    have h1 : uint.Z clis.len = sint.Z clis.len := by word
    have hposN : 0 < clis.len.toNat := by
      have : 0 < uint.Z clis.len := by word
      exact_mod_cast this
    have hu : uint.Z (n % clis.len) < uint.Z clis.len := by
      have h := Nat.mod_lt n.toNat hposN
      rw [← BitVec.toNat_umod] at h
      exact_mod_cast h
    have hs : sint.Z (n % clis.len) = uint.Z (n % clis.len) := by word
    have hbnd : 0 ≤ sint.Z (n % clis.len) ∧ sint.Z (n % clis.len) < sint.Z clis.len := by
      rw [hs, ← h1]
      exact ⟨by word, hu⟩
    have hidx : 0 ≤ sint.Z (n % clis.len) ∧ (sint.Z (n % clis.len)).toNat < cls.length := by
      have hb : 0 ≤ BitVec.toInt (n % clis.len) ∧
          BitVec.toInt (n % clis.len) < BitVec.toInt clis.len := hbnd
      have hl : cls.length = (BitVec.toInt clis.len).toNat := Hl.1
      show 0 ≤ BitVec.toInt (n % clis.len) ∧ (BitVec.toInt (n % clis.len)).toNat < cls.length
      omega
    simp only [hbnd, _root_.and_self, ↓reduceIte]
    list_elem cls (sint.Z (n % clis.len)).toNat as cl
    wp_apply wp_load_slice_index _ (sint.Z (n % clis.len)) cls _ cl hidx.1 $$ [] as -
    · iframe #; ipureintro; exact Hcl_lookup
    (try wp_auto)
    ihave #Hc := (BigSepL.bigSepL_lookup (Φ := fun _ c => iprop(isNewClient (GF := GF) c
      (ms.map client.SrvAt.addr) V ∗ client.clientWriteOnce c (ms.map client.SrvAt.addr)))
      Hcl_lookup) $$ Hcl
    icases Hc with ⟨#Hnc, #Hwo⟩
    -- `resp, err := cli.Put(ctx, p.key, p.val)`
    wp_apply (client_Put_hist cl ms V context.backgroundCtxVal cd x.Key' x.Val' slice.nil
        (fun _ => iprop(True))) $$ [Hau] as %resp %err Hout
    · iframe #; iexact Hau
    icases Hout with (⟨%Herr, %m, #Hm, %y, %hy, Hr⟩ | %Herr)
    · subst Herr
      ihave #Hy := (BigSepL.bigSepL_mem (Φ := fun y => memberPut (GF := GF) γr y) hy) $$ Hms
      iunfold memberPut at Hy
      icases Hy with ⟨-, #Hinvs, -, %hmy⟩
      imod okFactH_of_reply γr y.E y.γr hmy.1 hrb [] x.Key' x.Val' _ y.cid y.mid m
        $$ Hinvs Hr with #Hok
      (try wp_auto)
      wp_apply sync.Mutex.wp_Lock $$ [] as ⟨Hown, Hinv⟩
      · iframe #
      iunfold wsInvH at Hinv
      icases Hinv with ⟨%osl, %oks, Hof, Hos, Hocap, #Hoks⟩
      iunfold putRespMsg at Hm
      icases Hm with ⟨%Hnn, %h, %pk, #Hhd, #Hhf, -⟩
      iunfold hdrFull at Hhf
      icases Hhf with ⟨%Hhn, -, -, #Hrevf, -, -⟩
      (try wp_auto)
      wp_apply wp_slice_literal (l := [(⟨m.hdr.revision, x.Key', x.Val'⟩ : wrec)])
      isplitr
      · ipureintro; rfl
      iintro %l1 ⟨Hl1, _⟩
      simp only [go.arrayLiteralSize, List.foldl]
      (try wp_auto)
      wp_apply wp_slice_append $$ [$Hos $Hocap $Hl1] as %osl' ⟨Hos, Hocap, -⟩
      (try wp_auto)
      wp_apply (sync.Mutex.wp_Unlock (structFieldRef
          github_com.mit_pdos.etcd_grove.examples.common.Writes go!"Mu" w) (wsInvH w γr))
        $$ [Hown Hof Hos Hocap]
      · iframe #
        iframe Hown
        iunfold wsInvH
        iexists osl', oks ++ [⟨m.hdr.revision, x.Key', x.Val'⟩]
        iframe
        inext
        imodintro
        iapply BigSepL.bigSepL_snoc.2
        iframe #
      (try wp_auto)
      wp_for_post
      iframe
      iexists k + W64 1
      iframe
      ipureintro; constructor <;> word
    · cases err with
      | nil => exact absurd rfl Herr
      | ok e => ?_
      (try wp_auto)
      wp_for_post
      iframe
      iexists k + W64 1
      iframe
      ipureintro; constructor <;> word
  · (try wp_auto)
    iapply HΦ; itrivial

end proof

end linkv3p
end EtcdGrove
end Perennial
