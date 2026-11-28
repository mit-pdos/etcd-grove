/-
(hraft_robust R3) The proof of `disk.(*Disk).lastIndex`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Disk__lastIndex

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section sec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]
variable [dur_sem : github_com.mit_pdos.etcd_grove.examples.lib.durable.Assumptions]

open github_com.hashicorp.raft proto github_com.hashicorp.raft.examples.hraftnet.disk EtcdGrove

theorem dk_hi_last (I : DiskImg) (n : Nat) (e : DEnt) (hn : I.ents.length = n + 1) (h : I.ents[n]? = some e) :
    I.hi = e.idx := by
  unfold DiskImg.hi
  rw [List.getLast?_eq_getElem?, hn, Nat.add_sub_cancel, h]

theorem dk_hi_nil (I : DiskImg) (h : I.ents.length = 0) : I.hi = W64 0 := by
  unfold DiskImg.hi; rw [List.length_eq_zero_iff.1 h]; rfl

theorem github_com.hashicorp.raft.examples.hraftnet.disk.Disk.lastIndex.wp_proof :
    github_com.hashicorp.raft.examples.hraftnet.disk.Disk.lastIndex.spec (GF := GF) (hG := hG) := by
  intro d I stg
  wp_start as Hd
  iunfold diskMem at Hd
  icases Hd with ⟨%es, %ks, %vs, %iks, %ivs, %lvs, %kss, %vss, %ikss, Hents, Hes, Hescap, #Hent,
    Hkeys, Hks, Hkscap, #Hkr, Hvals, Hvs, Hvscap, #Hvr, Hikeys, Hiks, Hikscap, #Hikr,
    Hivals, Hivs, Hivscap, Hstaged, Hcommit⟩
  ihave %Hesl := ownSlice_len $$ Hes
  ihave %Hentl := BigSepL2.bigSepL2_length $$ Hent
  wp_auto
  wp_if_destruct
  · rw [dk_hi_nil I (by rw [← Hentl, Hesl.1, Hif]; rfl)]
    iapply HΦ
    iunfold diskMem
    iexists es, ks, vs, iks, ivs, lvs, kss, vss, ikss
    iframe; iframe #
  · have hpos : 0 < lvs.length := by
      have : sint.nat es.len ≠ 0 := by intro h; apply Hif; word
      omega
    obtain ⟨n, hn⟩ : ∃ n, lvs.length = n + 1 := ⟨lvs.length - 1, by omega⟩
    list_elem lvs n as lv
    list_elem I.ents n as e
    ihave #Her := BigSepL2.bigSepL2_lookup Hlv_lookup He_lookup $$ Hent
    iunfold entRep at Her
    icases Her with ⟨%Hef, -, -⟩
    have hi1 : sint.Z (es.len - W64 1) = n := by
      have : sint.nat es.len = n + 1 := by rw [← Hesl.1, hn]
      word
    have hb : 0 ≤ sint.Z (es.len - W64 1) ∧ sint.Z (es.len - W64 1) < sint.Z es.len := by
      have : sint.nat es.len = n + 1 := by rw [← Hesl.1, hn]
      constructor <;> word
    icases ownSlice_elem_acc (sint.Z (es.len - W64 1)) lv es (DFrac.own 1) lvs hb.1
      (by rw [hi1]; exact Hlv_lookup) $$ Hes with ⟨Hv, Hclose⟩
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_auto
    ihave Hes := Hclose $$ Hv
    rw [list_set_lookup_self lvs _ lv (by rw [hi1]; exact Hlv_lookup)]
    rw [Hef.1, ← dk_hi_last I n e (by rw [← Hentl, hn]) He_lookup]
    iapply HΦ
    iunfold diskMem
    iexists es, ks, vs, iks, ivs, lvs, kss, vss, ikss
    iframe; iframe #

end sec

end Perennial
